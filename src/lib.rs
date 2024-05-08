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
}

pub mod prelude {
    pub use super::PriorityQueue;
    pub use crate::rusty::RustyPriorityQueue;
}
