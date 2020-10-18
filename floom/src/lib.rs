use std::{
    alloc::{alloc, dealloc, Layout},
    cell::Cell,
    fmt,
    hint::unreachable_unchecked,
    future::Future,
    marker::PhantomPinned,
    mem::{drop, replace, size_of},
    pin::Pin,
    ptr::{drop_in_place, read, write, NonNull},
    sync::atomic::{AtomicBool, AtomicUsize, Ordering},
    task::{Context, Poll, RawWaker, RawWakerVTable, Waker},
    thread,
    time::{Duration, Instant},
};

struct Lock<T>(usync::sync::Lock<T>);

impl<T> Lock<T> {
    fn new(value: T) -> Self {
        Self(usync::sync::Lock::new(value))
    }

    fn with<F>(&self, f: impl FnOnce(&mut T) -> F) -> F {
        f(&mut *self.0.lock::<usync::parker::DefaultParker>())
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
#[repr(usize)]
enum AtomicWakerState {
    Empty = 0,
    Waiting = 1,
    Updating = 2,
    Consuming = 3,
    Notified = 4,
}

impl From<usize> for AtomicWakerState {
    fn from(value: usize) -> Self {
        match value {
            0 => Self::Empty,
            1 => Self::Waiting,
            2 => Self::Updating,
            3 => Self::Consuming,
            4 => Self::Notified,
            _ => unreachable!(),
        }
    }
}

struct AtomicWaker {
    state: AtomicUsize,
    waker: Cell<Option<Waker>>,
}

impl AtomicWaker {
    fn new() -> Self {
        Self {
            state: AtomicUsize::new(AtomicWakerState::Empty as usize),
            waker: Cell::new(None),
        }
    }

    fn prepare(&self, ctx: &Context<'_>) {
        self.waker.set(Some(ctx.waker().clone()));
        self.state
            .store(AtomicWakerState::Waiting as usize, Ordering::Release);
    }

    fn park(&self, ctx: &Context<'_>) -> Poll<()> {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            match AtomicWakerState::from(state) {
                AtomicWakerState::Waiting => match self.state.compare_exchange_weak(
                    AtomicWakerState::Waiting as usize,
                    AtomicWakerState::Updating as usize,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    Err(e) => state = e,
                    Ok(_) => {
                        if !(unsafe { &*self.waker.as_ptr() })
                            .as_ref()
                            .expect("AtomicWaker updating without a Waker")
                            .will_wake(ctx.waker())
                        {
                            self.waker.set(Some(ctx.waker().clone()));
                        }

                        match self.state.compare_exchange(
                            AtomicWakerState::Updating as usize,
                            AtomicWakerState::Waiting as usize,
                            Ordering::Release,
                            Ordering::Relaxed,
                        ) {
                            Ok(_) => return Poll::Pending,
                            Err(e) => match AtomicWakerState::from(e) {
                                AtomicWakerState::Notified => {
                                    return Poll::Ready(());
                                }
                                waker_state => {
                                    unreachable!(
                                        "invalid AtomicWaker state when updating {:?}",
                                        waker_state,
                                    );
                                }
                            },
                        }
                    }
                },
                AtomicWakerState::Empty => {
                    unreachable!("AtomicWaker parking when not prepared");
                }
                AtomicWakerState::Updating => {
                    unreachable!("AtomicWaker parking on multiple threads");
                }
                AtomicWakerState::Consuming => {
                    return Poll::Pending;
                }
                AtomicWakerState::Notified => {
                    return Poll::Ready(());
                }
            }
        }
    }

    fn unpark(&self) -> Option<Waker> {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            match AtomicWakerState::from(state) {
                AtomicWakerState::Empty => {
                    unreachable!("AtomicWaker unparked when not prepared");
                }
                AtomicWakerState::Waiting => match self.state.compare_exchange_weak(
                    AtomicWakerState::Waiting as usize,
                    AtomicWakerState::Consuming as usize,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    Err(e) => state = e,
                    Ok(_) => {
                        let waker = self.waker.replace(None);
                        self.state
                            .store(AtomicWakerState::Notified as usize, Ordering::Release);
                        return waker;
                    }
                },
                AtomicWakerState::Updating => match self.state.compare_exchange_weak(
                    AtomicWakerState::Updating as usize,
                    AtomicWakerState::Notified as usize,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ) {
                    Err(e) => state = e,
                    Ok(_) => return None,
                },
                AtomicWakerState::Consuming => {
                    unreachable!("multiple threads unparking the same AtomicWaker");
                }
                AtomicWakerState::Notified => {
                    unreachable!("AtomicWaker unparked when already unparked");
                }
            }
        }
    }
}

enum WaiterState<T> {
    Closed(Option<T>),
    Empty,
    Full(T),
}

struct Waiter<T> {
    prev: Cell<Option<NonNull<Self>>>,
    next: Cell<Option<NonNull<Self>>>,
    tail: Cell<Option<NonNull<Self>>>,
    state: Cell<WaiterState<T>>,
    atomic_waker: AtomicWaker,
    _pinned: PhantomPinned,
}

impl<T> Waiter<T> {
    fn new(state: WaiterState<T>) -> Self {
        Self {
            prev: Cell::new(None),
            next: Cell::new(None),
            tail: Cell::new(None),
            state: Cell::new(state),
            atomic_waker: AtomicWaker::new(),
            _pinned: PhantomPinned,
        }
    }
}

struct WaiterQueue<T> {
    head: Option<NonNull<Waiter<T>>>,
}

impl<T> WaiterQueue<T> {
    fn new() -> Self {
        Self { head: None }
    }

    fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    fn push(&mut self, waiter: Pin<&Waiter<T>>) {
        let waiter_ptr = NonNull::from(&*waiter);
        waiter.next.set(None);
        waiter.tail.set(Some(waiter_ptr));

        if let Some(head) = self.head {
            unsafe {
                let tail = head.as_ref().tail.replace(Some(waiter_ptr));
                let tail = tail.expect("WaiterQueue head without a tail");
                tail.as_ref().next.set(Some(waiter_ptr));
                waiter.prev.set(Some(tail));
            }
        } else {
            waiter.prev.set(None);
            self.head = Some(waiter_ptr);
        }
    }

    fn pop<'a>(&mut self) -> Option<Pin<&'a Waiter<T>>> {
        self.head.map(|waiter| unsafe {
            let pinned = Pin::new_unchecked(waiter.as_ref());
            assert!(self.try_remove(pinned));
            Pin::new_unchecked(&*waiter.as_ptr())
        })
    }

    fn try_remove(&mut self, waiter: Pin<&Waiter<T>>) -> bool {
        let head = match self.head {
            Some(head) => head,
            None => return false,
        };

        let prev = waiter.prev.get();
        let next = waiter.next.get();
        if waiter.tail.get().is_none() {
            return false;
        }

        unsafe {
            if let Some(prev) = prev {
                prev.as_ref().next.set(next);
            }
            if let Some(next) = next {
                next.as_ref().prev.set(prev);
            }
            if head == NonNull::from(&*waiter) {
                self.head = next;
            }
            if head.as_ref().tail.get() == Some(NonNull::from(&*waiter)) {
                head.as_ref().tail.set(prev);
            }
        }

        waiter.tail.set(None);
        true
    }

    fn consume(&mut self, other: &mut Self) {
        if let Some(other_head) = replace(&mut other.head, None) {
            unsafe {
                let other_tail = other_head
                    .as_ref()
                    .tail
                    .get()
                    .expect("Consuming a WaiterQueue without a tail");
                if let Some(head) = self.head {
                    let tail = head
                        .as_ref()
                        .tail
                        .replace(Some(other_tail))
                        .expect("Consuming a WaiterQueue without having a tail");
                    tail.as_ref().next.set(Some(other_head));
                    other_head.as_ref().prev.set(Some(tail));
                } else {
                    self.head = Some(other_head);
                }
            }
        }
    }
}

impl<T> IntoIterator for WaiterQueue<T> {
    type Item = Waker;
    type IntoIter = ClosedIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        ClosedIter(self.head)
    }
}

struct ClosedIter<T>(Option<NonNull<Waiter<T>>>);

impl<T> Iterator for ClosedIter<T> {
    type Item = Waker;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(waiter) = self.0 {
            let waiter = unsafe {
                self.0 = waiter.as_ref().next.get();
                &*waiter.as_ptr()
            };

            match waiter.state.replace(WaiterState::Closed(None)) {
                WaiterState::Empty => {}
                WaiterState::Full(item) => waiter.state.set(WaiterState::Closed(Some(item))),
                WaiterState::Closed(_) => unreachable!("Waiter already closed when closing"),
            }

            if let Some(waker) = waiter.atomic_waker.unpark() {
                return Some(waker);
            }
        }

        None
    }
}

struct Channel<T> {
    head: usize,
    tail: usize,
    capacity: usize,
    buffer: Option<NonNull<T>>,
    senders: WaiterQueue<T>,
    receivers: WaiterQueue<T>,
}

impl<T> Drop for Channel<T> {
    fn drop(&mut self) {
        assert!(self.senders.is_empty(), "pending senders when dropping Channel");
        assert!(self.receivers.is_empty(), "pending receivers when dropping Channel");

        while let Ok((item, waker)) = self.try_recv() {
            assert!(waker.is_none(), "pending Waker when dropping Channel");
            drop(item);
        }

        if let Some(buffer) = self.buffer {
            unsafe {
                let layout = Layout::array::<T>(self.capacity());
                dealloc(buffer.as_ptr() as *mut u8, layout.unwrap());
            }
        }
    }
}

impl<T> Channel<T> {
    const DEFAULT_UNBOUNDED_CAPACITY: usize = 8;
    const IS_BOUNDED: usize = 0b01;
    const IS_CLOSED: usize = 0b10;
    const SHIFT: u32 = (Self::IS_BOUNDED | Self::IS_CLOSED).count_ones();

    fn unbounded() -> Self {
        Self::with_capacity(0)
    }

    fn bounded(capacity: usize) -> Self {
        assert!(capacity <= (!0 >> Self::SHIFT), "bound capacity is too large",);
        Self::with_capacity((capacity << Self::SHIFT) | Self::IS_BOUNDED)
    }

    fn with_capacity(capacity: usize) -> Self {
        Self {
            head: 0,
            tail: 0,
            capacity,
            buffer: None,
            senders: WaiterQueue::new(),
            receivers: WaiterQueue::new(),
        }
    }

    fn size(&self) -> usize {
        self.tail.wrapping_sub(self.head)
    }

    fn is_closed(&self) -> bool {
        self.capacity & Self::IS_CLOSED != 0
    }

    fn is_bounded(&self) -> bool {
        self.capacity & Self::IS_BOUNDED != 0
    }

    fn capacity(&self) -> usize {
        self.capacity >> Self::SHIFT
    }

    fn wrap_index(&self, index: usize) -> usize {
        if self.is_bounded() {
            index % self.capacity()
        } else {
            index & (self.capacity() - 1)
        }
    }

    unsafe fn buffer(&self) -> NonNull<T> {
        self.buffer.unwrap_or_else(|| unreachable_unchecked())
    }

    fn try_push(&mut self, item: T) -> Result<(), T> {
        if self.size() == self.capacity() {
            Err(item)
        } else {
            Ok(unsafe {
                let index = self.wrap_index(self.tail);
                self.tail = self.tail.wrapping_add(1);
                let item_ptr = self.buffer().as_ptr().add(index);
                write(item_ptr, item)
            })
        }
    }

    fn try_pop(&mut self) -> Result<T, ()> {
        if self.size() == 0 {
            Err(())
        } else {
            Ok(unsafe {
                let index = self.wrap_index(self.head);
                self.head = self.head.wrapping_add(1);
                let item_ptr = self.buffer().as_ptr().add(index);
                read(item_ptr)
            })
        }
    }

    fn try_send(&mut self, item: T) -> Result<Option<Waker>, TrySendError<T>> {
        if self.is_closed() {
            return Err(TrySendError::Closed(item));
        }

        if let Some(waiter) = self.receivers.pop() {
            match waiter.state.replace(WaiterState::Full(item)) {
                WaiterState::Empty => return Ok(waiter.atomic_waker.unpark()),
                _ => unreachable!("invalid WaiterState when dequeueing receivers"),
            }
        }

        if self.buffer.is_none() {
            let capacity = self.capacity();
            if self.is_bounded() && capacity != 0 {
                self.grow(capacity);
            } else {
                self.grow(Self::DEFAULT_UNBOUNDED_CAPACITY);
            }
        }

        if !self.is_bounded() && self.size() == self.capacity() {
            self.grow(self.capacity() << 1);
        }

        match self.try_push(item) {
            Ok(_) => Ok(None),
            Err(item) => Err(TrySendError::Full(item)),
        }
    }

    fn try_recv(&mut self) -> Result<(T, Option<Waker>), TryRecvError> {
        if let Ok(item) = self.try_pop() {
            return Ok((item, None));
        }

        if let Some(waiter) = self.senders.pop() {
            match waiter.state.replace(WaiterState::Empty) {
                WaiterState::Full(item) => return Ok((item, waiter.atomic_waker.unpark())),
                _ => unreachable!("invalid WaiterState when dequeueing senders"),
            }
        }

        if self.is_closed() {
            Err(TryRecvError::Closed)
        } else {
            Err(TryRecvError::Empty)
        }
    }

    fn grow(&mut self, new_capacity: usize) {
        unsafe {
            let new_layout = Layout::array::<T>(new_capacity).unwrap();
            let new_buffer = alloc(new_layout) as *mut T;
            let new_buffer = NonNull::new_unchecked(new_buffer);

            let mut new_tail = 0;
            while let Ok(item) = self.try_pop() {
                let item_ptr = new_buffer.as_ptr().add(new_tail);
                write(item_ptr, item);
                new_tail += 1;
            }

            if let Some(old_buffer) = self.buffer {
                let old_layout = Layout::array::<T>(self.capacity()).unwrap();
                dealloc(old_buffer.as_ptr() as *mut u8, old_layout);
            }

            self.head = 0;
            self.tail = new_tail;
            self.buffer = Some(new_buffer);
            self.capacity = (new_capacity << Self::SHIFT) | {
                self.capacity & (Self::IS_BOUNDED | Self::IS_CLOSED)
            };
        }
    }

    fn close(&mut self) -> WaiterQueue<T> {
        self.capacity |= Self::IS_CLOSED;

        let mut waiters = WaiterQueue::new();
        waiters.consume(&mut self.senders);
        waiters.consume(&mut self.receivers);
        waiters
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum TrySendError<T> {
    Full(T),
    Closed(T),
}

impl<T> std::error::Error for TrySendError<T> {}

impl<T> fmt::Debug for TrySendError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            TrySendError::Full(..) => "Full(..)".fmt(f),
            TrySendError::Closed(..) => "Closed(..)".fmt(f),
        }
    }
}

impl<T> fmt::Display for TrySendError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TrySendError::Full(..) => "sending on a full channel".fmt(f),
            TrySendError::Closed(..) => "sending on a closed channel".fmt(f),
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum TryRecvError {
    Empty,
    Closed,
}

impl std::error::Error for TryRecvError {}

impl fmt::Debug for TryRecvError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            TryRecvError::Empty => "Empty".fmt(f),
            TryRecvError::Closed => "Closed".fmt(f),
        }
    }
}

impl fmt::Display for TryRecvError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TryRecvError::Empty => "receiving on a empty channel".fmt(f),
            TryRecvError::Closed => "receiving on a closed channel".fmt(f),
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum SendError<T> {
    Closed(T),
}

impl<T> std::error::Error for SendError<T> {}

impl<T> fmt::Debug for SendError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        "SendError(..)".fmt(f)
    }
}

impl<T> fmt::Display for SendError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        "sending on a closed channel".fmt(f)
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum RecvError {
    Closed,
}

impl std::error::Error for RecvError {}

impl fmt::Display for RecvError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        "receiving on a closed channel".fmt(f)
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum SendTimeoutError<T> {
    TimedOut(T),
    Closed(T),
}

impl<T> std::error::Error for SendTimeoutError<T> {}

impl<T> fmt::Debug for SendTimeoutError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            SendTimeoutError::TimedOut(..) => "TimedOut(..)".fmt(f),
            SendTimeoutError::Closed(..) => "Closed(..)".fmt(f),
        }
    }
}

impl<T> fmt::Display for SendTimeoutError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SendTimeoutError::TimedOut(..) => "timed out sending on a channel".fmt(f),
            SendTimeoutError::Closed(..) => "sending on a closed channel".fmt(f),
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum RecvTimeoutError {
    TimedOut,
    Closed,
}

impl std::error::Error for RecvTimeoutError {}

impl fmt::Display for RecvTimeoutError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RecvTimeoutError::TimedOut => "timed out receiving on a channel".fmt(f),
            RecvTimeoutError::Closed => "receiving on a closed channel".fmt(f),
        }
    }
}

const SENDER_MASK: usize = (1 << ((size_of::<usize>() * 8) / 2)) - 1;
const RECEIVER_MASK: usize = SENDER_MASK << ((size_of::<usize>() * 8) / 2);

const SENDER: usize = 1 << SENDER_MASK.trailing_zeros();
const RECEIVER: usize = 1 << RECEIVER_MASK.trailing_zeros();

struct Inner<T> {
    ref_count: AtomicUsize,
    channel: Lock<Channel<T>>,
}

pub fn unbounded<T>() -> (Sender<T>, Receiver<T>) {
    channel(|| Channel::<T>::unbounded())
}

pub fn bounded<T>(capacity: usize) -> (Sender<T>, Receiver<T>) {
    channel(|| Channel::<T>::bounded(capacity))
}

fn channel<T>(make_channel: impl FnOnce() -> Channel<T>) -> (Sender<T>, Receiver<T>) {
    let inner_ptr = unsafe {
        let inner_ptr = alloc(Layout::new::<Inner<T>>());
        let inner_ptr = NonNull::new_unchecked(inner_ptr as *mut Inner<T>);
        write(
            inner_ptr.as_ptr(),
            Inner {
                ref_count: AtomicUsize::new(SENDER | RECEIVER),
                channel: Lock::new(make_channel()),
            },
        );
        inner_ptr
    };

    (Sender(InnerRef(inner_ptr)), Receiver(InnerRef(inner_ptr)))
}

struct InnerRef<T>(NonNull<Inner<T>>);

impl<T> InnerRef<T> {
    fn with_inner<F>(&self, f: impl FnOnce(&Inner<T>) -> F) -> F {
        f(unsafe { self.0.as_ref() })
    }

    fn with_channel<F>(&self, f: impl FnOnce(&mut Channel<T>) -> F) -> F {
        self.with_inner(|inner| inner.channel.with(f))
    }

    fn clone_with(&self, count: usize, count_mask: usize) -> Self {
        self.with_inner(|inner| {
            let ref_count = inner.ref_count.fetch_add(count, Ordering::Relaxed);
            assert!(
                ((ref_count & count_mask) + count) <= count_mask,
                "Reference count overflowed",
            );
            Self(NonNull::from(inner))
        })
    }

    fn drop_with(&self, count: usize, count_mask: usize) {
        let waiters = self.with_inner(|inner| {
            let ref_count = inner.ref_count.fetch_sub(count, Ordering::Relaxed);
            if ref_count == count {
                None
            } else if (ref_count & count_mask) == count {
                Some(Some(inner.channel.with(|channel| channel.close())))
            } else {
                Some(None)
            }
        });

        match waiters {
            None => unsafe {
                let inner_ptr = self.0.as_ptr();
                drop_in_place(inner_ptr);
                dealloc(inner_ptr as *mut u8, Layout::new::<Inner<T>>());
            },
            Some(None) => {}
            Some(Some(waiters)) => {
                for waker in waiters {
                    waker.wake();
                }
            }
        }
    }
}

struct Parker {
    is_parking: AtomicBool,
    thread: Cell<Option<thread::Thread>>,
}

impl Parker {
    fn new() -> Self {
        Self {
            is_parking: AtomicBool::new(false),
            thread: Cell::new(None),
        }
    }

    fn prepare(&self) {
        self.is_parking.store(true, Ordering::Relaxed);
        self.thread.set(Some(thread::current()));
    }

    fn park(&self, deadline: Option<Instant>) -> bool {
        loop {
            if !self.is_parking.load(Ordering::Acquire) {
                return true;
            }

            let timeout = if let Some(deadline) = deadline {
                let now = Instant::now();
                if now > deadline {
                    return false;
                } else {
                    Some(deadline - now)
                }
            } else {
                None
            };

            if let Some(timeout) = timeout {
                thread::park_timeout(timeout);
            } else {
                thread::park();
            }
        }
    }

    fn unpark(&self) {
        let thread = self.thread.replace(None);
        self.is_parking.store(false, Ordering::Release);
        thread
            .expect("unpark on Parker that isn't prepared")
            .unpark();
    }

    unsafe fn as_waker(&self) -> Waker {
        const VTABLE: RawWakerVTable = RawWakerVTable::new(
            |parker_ptr| unsafe {
                (&*(parker_ptr as *const Parker)).prepare();
                RawWaker::new(parker_ptr, &VTABLE)
            },
            |parker_ptr| unsafe {
                (&*(parker_ptr as *const Parker)).unpark();
            },
            |parker_ptr| unsafe {
                (&*(parker_ptr as *const Parker)).unpark();
            },
            |_parker_ptr| {},
        );

        let parker_ptr = self as *const Self as *const ();
        let raw_waker = RawWaker::new(parker_ptr, &VTABLE);
        Waker::from_raw(raw_waker)
    }
}

pub struct Sender<T>(InnerRef<T>);

unsafe impl<T> Send for Sender<T> {}
unsafe impl<T> Sync for Sender<T> {}

impl<T> Drop for Sender<T> {
    fn drop(&mut self) {
        self.0.drop_with(SENDER, SENDER_MASK);
    }
}

impl<T> Clone for Sender<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone_with(SENDER, SENDER_MASK))
    }
}

impl<T> Sender<T> {
    pub fn try_send(&self, item: T) -> Result<(), TrySendError<T>> {
        self.0.with_channel(|channel| match channel.try_send(item) {
            Err(send_error) => Err(send_error),
            Ok(waker) => {
                if let Some(waker) = waker {
                    waker.wake();
                }
                Ok(())
            }
        })
    }

    pub fn try_send_for(&self, item: T, duration: Duration) -> Result<(), SendTimeoutError<T>> {
        self.try_send_until(item, Instant::now() + duration)
    }

    pub fn try_send_until(&self, item: T, deadline: Instant) -> Result<(), SendTimeoutError<T>> {
        self.send_sync(item, Some(deadline))
    }

    pub fn send_async(&self, item: T) -> SendFuture<'_, T> {
        SendFuture(FutureOp::new(Some(item), &self.0))
    }

    pub fn send(&self, item: T) -> Result<(), SendError<T>> {
        match self.send_sync(item, None) {
            Ok(_) => Ok(()),
            Err(SendTimeoutError::Closed(item)) => Err(SendError::Closed(item)),
            _ => unreachable!("invalid send result"),
        }
    }

    fn send_sync(&self, item: T, deadline: Option<Instant>) -> Result<(), SendTimeoutError<T>> {
        sync_future_op(
            deadline,
            self.send_async(item),
            |channel: &mut Channel<T>, waiter| channel.senders.try_remove(waiter),
            |result| match result {
                Ok(_) => Ok(()),
                Err(SendError::Closed(item)) => Err(SendTimeoutError::Closed(item)),
            },
            |waiter_state| match waiter_state {
                WaiterState::Empty => Ok(()),
                WaiterState::Full(item) => Err(SendTimeoutError::TimedOut(item)),
                WaiterState::Closed(Some(item)) => Err(SendTimeoutError::Closed(item)),
                _ => unreachable!("invalid WaiterState when timed out"),
            },
        )
    }
}

pub struct Receiver<T>(InnerRef<T>);

unsafe impl<T> Send for Receiver<T> {}
unsafe impl<T> Sync for Receiver<T> {}

impl<T> Drop for Receiver<T> {
    fn drop(&mut self) {
        self.0.drop_with(RECEIVER, RECEIVER_MASK);
    }
}

impl<T> Clone for Receiver<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone_with(RECEIVER, RECEIVER_MASK))
    }
}

impl<T> Receiver<T> {
    pub fn try_recv(&self) -> Result<T, TryRecvError> {
        self.0.with_channel(|channel| match channel.try_recv() {
            Err(recv_error) => Err(recv_error),
            Ok((item, waker)) => {
                if let Some(waker) = waker {
                    waker.wake();
                }
                Ok(item)
            }
        })
    }

    pub fn try_recv_for(&self, duration: Duration) -> Result<T, RecvTimeoutError> {
        self.try_recv_until(Instant::now() + duration)
    }

    pub fn try_recv_until(&self, deadline: Instant) -> Result<T, RecvTimeoutError> {
        self.recv_sync(Some(deadline))
    }

    pub fn recv_async(&self) -> RecvFuture<'_, T> {
        RecvFuture(FutureOp::new(None, &self.0))
    }

    pub fn recv(&self) -> Result<T, RecvError> {
        match self.recv_sync(None) {
            Ok(item) => Ok(item),
            Err(RecvTimeoutError::Closed) => Err(RecvError::Closed),
            _ => unreachable!("invalid receive result"),
        }
    }

    fn recv_sync(&self, deadline: Option<Instant>) -> Result<T, RecvTimeoutError> {
        sync_future_op(
            deadline,
            self.recv_async(),
            |channel: &mut Channel<T>, waiter| channel.receivers.try_remove(waiter),
            |result| match result {
                Ok(item) => Ok(item),
                Err(RecvError::Closed) => Err(RecvTimeoutError::Closed),
            },
            |waiter_state| match waiter_state {
                WaiterState::Full(item) => Ok(item),
                WaiterState::Empty => Err(RecvTimeoutError::TimedOut),
                WaiterState::Closed(None) => Err(RecvTimeoutError::Closed),
                _ => unreachable!("invalid WaiterState when timed out"),
            },
        )
    }
}

enum FutureOpState<'a, T> {
    TryOp(&'a InnerRef<T>, Option<T>),
    Waiting(&'a InnerRef<T>),
    Completed,
}

struct FutureOp<'a, T> {
    state: FutureOpState<'a, T>,
    waiter: Waiter<T>,
}

fn sync_future_op<'a, T: 'a, F: Future + AsFutureOp<'a, T> + 'a, V, E>(
    deadline: Option<Instant>,
    mut future: F,
    on_remove: impl FnOnce(&mut Channel<T>, Pin<&Waiter<T>>) -> bool,
    on_complete: impl FnOnce(F::Output) -> Result<V, E>,
    on_cancel: impl FnOnce(WaiterState<T>) -> Result<V, E>,
) -> Result<V, E> {
    let parker = Parker::new();
    let waker = unsafe { parker.as_waker() };
    let mut context = Context::from_waker(&waker);

    loop {
        let pinned = unsafe { Pin::new_unchecked(&mut future) };
        match pinned.poll(&mut context) {
            Poll::Ready(output) => return on_complete(output),
            Poll::Pending => {}
        }

        if parker.park(deadline) {
            continue;
        }

        let future_op = future.as_future_op();
        let inner_ref = match replace(&mut future_op.state, FutureOpState::Completed) {
            FutureOpState::Waiting(inner_ref) => inner_ref,
            _ => unreachable!("invalid FutureOpState"),
        };

        if !inner_ref.with_channel(|channel| {
            let waiter = unsafe { Pin::new_unchecked(&future_op.waiter) };
            on_remove(channel, waiter)
        }) {
            parker.park(None);
        }

        let waiter_state = WaiterState::Closed(None);
        let waiter_state = future_op.waiter.state.replace(waiter_state);
        return on_cancel(waiter_state);
    }
}

trait AsFutureOp<'a, T> {
    fn as_future_op(&mut self) -> &mut FutureOp<'a, T>;
}

impl<'a, T> FutureOp<'a, T> {
    fn new(item: Option<T>, inner_ref: &'a InnerRef<T>) -> Self {
        Self {
            state: FutureOpState::TryOp(inner_ref, item),
            waiter: Waiter::new(WaiterState::Closed(None)),
        }
    }
}

pub struct SendFuture<'a, T>(FutureOp<'a, T>);

unsafe impl<'a, T> Send for SendFuture<'a, T> {}

impl<'a, T> SendFuture<'a, T> {
    #[cold]
    fn cancel(&self, inner_ref: &'a InnerRef<T>) {
        inner_ref.with_channel(|channel| unsafe {
            let waiter = Pin::new_unchecked(&self.0.waiter);
            let _ = channel.senders.try_remove(waiter);
        });
    }
}

impl<'a, T> Drop for SendFuture<'a, T> {
    fn drop(&mut self) {
        if let FutureOpState::Waiting(inner_ref) = self.0.state {
            self.cancel(inner_ref);
        }
    }
}

impl<'a, T> AsFutureOp<'a, T> for SendFuture<'a, T> {
    fn as_future_op(&mut self) -> &mut FutureOp<'a, T> {
        &mut self.0
    }
}

impl<'a, T> Future for SendFuture<'a, T> {
    type Output = Result<(), SendError<T>>;

    fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
        let mut_self = unsafe { &mut Pin::get_unchecked_mut(self).0 };

        match replace(&mut mut_self.state, FutureOpState::Completed) {
            FutureOpState::TryOp(_, None) => unreachable!("invalid initial SendFuture state"),
            FutureOpState::TryOp(inner_ref, Some(item)) => {
                match inner_ref.with_channel(|channel| match channel.try_send(item) {
                    Ok(waker) => Some(Ok(waker)),
                    Err(TrySendError::Closed(item)) => Some(Err(SendError::Closed(item))),
                    Err(TrySendError::Full(item)) => {
                        mut_self.waiter.atomic_waker.prepare(ctx);
                        mut_self.waiter.state.set(WaiterState::Full(item));
                        channel
                            .senders
                            .push(unsafe { Pin::new_unchecked(&mut_self.waiter) });
                        None
                    }
                }) {
                    Some(result) => {
                        mut_self.state = FutureOpState::Completed;
                        Poll::Ready(match result {
                            Ok(None) => Ok(()),
                            Ok(Some(waker)) => Ok(waker.wake()),
                            Err(error) => Err(error),
                        })
                    }
                    None => {
                        mut_self.state = FutureOpState::Waiting(inner_ref);
                        Poll::Pending
                    }
                }
            }
            FutureOpState::Waiting(inner_ref) => match mut_self.waiter.atomic_waker.park(ctx) {
                Poll::Pending => {
                    mut_self.state = FutureOpState::Waiting(inner_ref);
                    Poll::Pending
                }
                Poll::Ready(()) => {
                    mut_self.state = FutureOpState::Completed;
                    Poll::Ready(
                        match mut_self.waiter.state.replace(WaiterState::Closed(None)) {
                            WaiterState::Empty => Ok(()),
                            WaiterState::Closed(Some(item)) => Err(SendError::Closed(item)),
                            _ => unreachable!("invalid sender WaiterState"),
                        },
                    )
                }
            },
            FutureOpState::Completed => unreachable!("SendFuture polled after completion"),
        }
    }
}

pub struct RecvFuture<'a, T>(FutureOp<'a, T>);

unsafe impl<'a, T> Send for RecvFuture<'a, T> {}

impl<'a, T> RecvFuture<'a, T> {
    #[cold]
    fn cancel(&self, inner_ref: &'a InnerRef<T>) {
        inner_ref.with_channel(|channel| unsafe {
            let waiter = Pin::new_unchecked(&self.0.waiter);
            let _ = channel.receivers.try_remove(waiter);
        });
    }
}

impl<'a, T> Drop for RecvFuture<'a, T> {
    fn drop(&mut self) {
        if let FutureOpState::Waiting(inner_ref) = self.0.state {
            self.cancel(inner_ref);
        }
    }
}

impl<'a, T> AsFutureOp<'a, T> for RecvFuture<'a, T> {
    fn as_future_op(&mut self) -> &mut FutureOp<'a, T> {
        &mut self.0
    }
}

impl<'a, T> Future for RecvFuture<'a, T> {
    type Output = Result<T, RecvError>;

    fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
        let mut_self = unsafe { &mut Pin::get_unchecked_mut(self).0 };

        match replace(&mut mut_self.state, FutureOpState::Completed) {
            FutureOpState::TryOp(_, Some(_)) => unreachable!("invalid RecvFuture initial state"),
            FutureOpState::TryOp(inner_ref, None) => {
                match inner_ref.with_channel(|channel| match channel.try_recv() {
                    Ok((item, waker)) => Some(Ok((item, waker))),
                    Err(TryRecvError::Closed) => Some(Err(RecvError::Closed)),
                    Err(TryRecvError::Empty) => {
                        mut_self.waiter.atomic_waker.prepare(ctx);
                        mut_self.waiter.state.set(WaiterState::Empty);
                        channel
                            .receivers
                            .push(unsafe { Pin::new_unchecked(&mut_self.waiter) });
                        None
                    }
                }) {
                    Some(result) => {
                        mut_self.state = FutureOpState::Completed;
                        Poll::Ready(match result {
                            Err(error) => Err(error),
                            Ok((item, waker)) => Ok({
                                if let Some(waker) = waker {
                                    waker.wake();
                                }
                                item
                            }),
                        })
                    }
                    None => {
                        mut_self.state = FutureOpState::Waiting(inner_ref);
                        Poll::Pending
                    }
                }
            }
            FutureOpState::Waiting(inner_ref) => match mut_self.waiter.atomic_waker.park(ctx) {
                Poll::Pending => {
                    mut_self.state = FutureOpState::Waiting(inner_ref);
                    Poll::Pending
                }
                Poll::Ready(()) => {
                    mut_self.state = FutureOpState::Completed;
                    Poll::Ready(
                        match mut_self.waiter.state.replace(WaiterState::Closed(None)) {
                            WaiterState::Full(item) => Ok(item),
                            WaiterState::Closed(None) => Err(RecvError::Closed),
                            _ => unreachable!("invalid receiver WaiterState"),
                        },
                    )
                }
            },
            FutureOpState::Completed => unreachable!("RecvFuture polled after completion"),
        }
    }
}
