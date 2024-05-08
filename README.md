# queue-queue

[![codecov](https://codecov.io/gh/naomijub/queue-queue/graph/badge.svg?token=DWO0LIC13M)](https://codecov.io/gh/naomijub/queue-queue)

> Name inspired by the sound birds make "cuckoo"

A simple priority queue crate that supports defining the priority of an element with zero default dependencies. All queues depend on 2 types `P` the priority, that implements `PartialOrd + PartialEq + Eq` and `T` the value, that implements `PartialEq + Eq`. 

All priority queues implement the trait [`PriorityQueue`](https://docs.rs/queue-queue/0.0.1/queue_queue/trait.PriorityQueue.html) from `prelude`, and the available queues are:

- [`RustyPriorityQueue`](https://docs.rs/queue-queue/0.0.1/queue_queue/rusty/struct.RustyPriorityQueue.html) which is based on top of Rust's [`BinaryHeap`](https://doc.rust-lang.org/std/collections/struct.BinaryHeap.html)
