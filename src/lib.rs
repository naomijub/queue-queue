pub mod rusty;

pub trait PriorityQueue<P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> {
    fn enqueue(&mut self, priority: P, data: T);

    fn dequeue(&mut self) -> Option<(P, T)>;

    fn peek(&self) -> Option<(&P, &T)>;

    fn len(&self) -> usize;

    fn is_empty(&self) -> bool;
}
