pub mod rusty;

pub trait PriorityQueue<P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> {
    /// Add an item to the queue
    fn enqueue(&mut self, priority: P, data: T);

    /// Remove an item from the queue
    fn dequeue(&mut self) -> Option<(P, T)>;

    /// Peeks the next item in the queue
    fn peek(&self) -> Option<(&P, &T)>;

    /// Queue length
    fn len(&self) -> usize;

    /// Boolean if the queue is empty
    fn is_empty(&self) -> bool;

    /// Queue capacity
    fn capacity(&self) -> usize;

    /// Check if an item exists in the queue
    /// true if it exists, false if it does not
    fn contains(&self, data: &T) -> bool;

    /// Check if an item exists in the queue at a certain priority
    /// true if it exists, false if it does not
    fn contains_at(&self, priority: &P, data: &T) -> bool;

    /// Remove all existing items from the queue
    /// true if it was removed, false if it was not
    fn remove(&mut self, data: &T) -> bool;

    /// Remove an item from the queue if exists at a certain priority
    /// true if it was removed, false if it was not
    fn remove_at(&mut self, priority: &P, data: &T) -> bool;

    /// Create a new priority queue with a given capacity
    ///
    /// # Example:
    ///
    /// `RustyPriorityQueue::<usize, &str>::with_capacity(10)`
    fn with_capacity(capacity: usize) -> Self;

    /// Append another priority queue into this one
    ///
    /// * Consumes the other priority queue
    fn append(&mut self, other: Self);

    /// Extend the priority queue with an `IntoIterator` of `(P, T)` => `(Priority, Data)`
    /// where `P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq`
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = (P, T)>;

    /// Reserves capacity for at least additional elements more than the current length.
    /// The allocator may reserve more space to speculatively avoid frequent allocations.
    /// After calling reserve, capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if capacity is already sufficient.
    ///
    /// # Panics
    /// Panics if the new capacity overflows usize.
    fn reserve(&mut self, additional: usize);

    /// Reserves the minimum capacity for at least additional elements more than the current length.
    /// Unlike reserve, this will not deliberately over-allocate to speculatively avoid frequent allocations.
    /// After calling `reserve_exact`, capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if the capacity is already sufficient.
    ///
    /// # Panics
    /// Panics if the new capacity overflows usize.
    fn reserve_exact(&mut self, additional: usize);

    /// Discards as much additional capacity as possible.
    fn shrink_to_fit(&mut self);

    /// Discards capacity with a lower bound.
    /// The capacity will remain at least as large as both the length and the supplied value.
    /// If the current capacity is less than the lower limit, this is a no-op.
    fn shrink_to(&mut self, capacity: usize);

    /// Removes all items from the queue
    fn clear(&mut self);

    /// Clears the binary heap, returning an iterator over the removed elements
    /// in arbitrary order. If the iterator is dropped before being fully
    /// consumed, it drops the remaining elements in arbitrary order.
    ///
    /// The returned iterator keeps a mutable borrow on the heap to optimize
    /// its implementation.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use queue_queue::rusty::RustyPriorityQueue;
    /// # use queue_queue::PriorityQueue;
    ///
    /// let mut prio = RustyPriorityQueue::<usize, String>::default();
    /// prio.enqueue(2, "hello".to_string());
    ///
    /// assert!(!prio.is_empty());
    ///
    /// for x in prio.drain() {
    ///     println!("{x:?}");
    /// }
    ///
    /// assert!(prio.is_empty());
    /// ```
    fn drain(&mut self) -> impl Iterator<Item = (P, T)> + '_;

    /// Returns the node the the highest priority in the queue.
    /// If no nodes exist, `None` is returned.
    fn max_node(&self) -> Option<(&P, &T)>;

    /// Returns the node the the lowest priority in the queue.
    /// If no nodes exist, `None` is returned.
    fn min_node(&self) -> Option<(&P, &T)>;
}

pub mod prelude {
    pub use super::PriorityQueue;
    pub use crate::rusty::RustyPriorityQueue;
}
