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

    /// Bollean if the queue is empty
    fn is_empty(&self) -> bool;
}

pub mod prelude {
    pub use super::PriorityQueue;
    pub use crate::rusty::RustyPriorityQueue;
}
