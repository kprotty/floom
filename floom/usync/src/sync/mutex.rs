// Copyright (c) 2020 kprotty
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![allow(unused, dead_code)]

use crate::utils::sync::{Int, AtomicInt, UnsafeCell};

const UNLOCKED: Int = 0;
const LOCKED: Int = 1;
const PARKED: Int = 2;

/// TODO
#[derive(Debug)]
pub struct Mutex<T> {
    state: AtomicInt,
    value: UnsafeCell<T>,
}