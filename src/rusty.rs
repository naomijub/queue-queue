use std::{cmp::Ordering, collections::BinaryHeap};

use crate::PriorityQueue;

#[derive(Debug, PartialEq, Eq)]
struct Node<P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> {
    priority: P,
    data: T,
}

impl<P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> PartialOrd for Node<P, T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.priority.partial_cmp(&other.priority)
    }
}

impl<P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> Ord for Node<P, T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.priority
            .partial_cmp(&other.priority)
            .unwrap_or(Ordering::Less)
    }
}

#[derive(Debug)]
pub struct RustyPriorityQueue<P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> {
    queue: BinaryHeap<Node<P, T>>,
}

impl<P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> Default for RustyPriorityQueue<P, T> {
    fn default() -> Self {
        Self {
            queue: BinaryHeap::new(),
        }
    }
}

impl<P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> PriorityQueue<P, T>
    for RustyPriorityQueue<P, T>
{
    fn enqueue(&mut self, priority: P, data: T) {
        let node = Node { priority, data };

        self.queue.push(node);
    }

    fn dequeue(&mut self) -> Option<(P, T)> {
        let node = self.queue.pop();

        node.map(|n| (n.priority, n.data))
    }

    fn peek(&self) -> Option<(&P, &T)> {
        self.queue.peek().map(|node| (&node.priority, &node.data))
    }

    fn len(&self) -> usize {
        self.queue.len()
    }

    fn is_empty(&self) -> bool {
        self.queue.is_empty()
    }
}

impl<P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> RustyPriorityQueue<P, T> {
    pub const fn iter(&self) -> RustyPriorityQueueIterator<P, T> {
        RustyPriorityQueueIterator { queue: &self.queue }
    }

    pub fn into_iter(self) -> RustyPriorityQueueIntoIterator<P, T> {
        RustyPriorityQueueIntoIterator { queue: self.queue }
    }
}

/// An Iterator struct for `RustyPriorityQueue`
pub struct RustyPriorityQueueIterator<'b, P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> {
    queue: &'b BinaryHeap<Node<P, T>>,
}

impl<'b, P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> Iterator
    for RustyPriorityQueueIterator<'b, P, T>
{
    type Item = (&'b P, &'b T);

    fn next(&mut self) -> Option<Self::Item> {
        self.queue.iter().next().map(|n| (&n.priority, &n.data))
    }
}

impl<P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> FromIterator<(P, T)>
    for RustyPriorityQueue<P, T>
{
    fn from_iter<I: IntoIterator<Item = (P, T)>>(iter: I) -> Self {
        let mut collection = Self::default();

        for i in iter {
            collection.enqueue(i.0, i.1);
        }

        collection
    }
}

/// An IntoIterator struct for `RustyPriorityQueue`
pub struct RustyPriorityQueueIntoIterator<P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> {
    queue: BinaryHeap<Node<P, T>>,
}

impl<P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> Iterator
    for RustyPriorityQueueIntoIterator<P, T>
{
    type Item = (P, T);

    fn next(&mut self) -> Option<Self::Item> {
        self.queue.pop().map(|node| (node.priority, node.data))
    }
}

impl<P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> IntoIterator for RustyPriorityQueue<P, T> {
    type Item = (P, T);
    type IntoIter = RustyPriorityQueueIntoIterator<P, T>;

    fn into_iter(self) -> Self::IntoIter {
        RustyPriorityQueueIntoIterator { queue: self.queue }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_is_empty() {
        let prio = RustyPriorityQueue::<usize, String>::default();

        assert_eq!(prio.len(), 0);
        assert!(prio.is_empty());
    }

    #[test]
    fn enqueue_once_has_size_1() {
        let mut prio = RustyPriorityQueue::<usize, String>::default();

        prio.enqueue(3, String::from("hellow world"));
        assert_eq!(prio.len(), 1);
        assert_eq!(prio.peek(), Some((&3, &String::from("hellow world"))));
    }

    #[test]
    fn dequeues_in_order() {
        let mut prio = RustyPriorityQueue::<usize, &str>::default();
        prio.enqueue(2, "hello");
        prio.enqueue(3, "julia");
        prio.enqueue(1, "world");
        prio.enqueue(3, "naomi");

        assert_eq!(prio.len(), 4);

        assert_eq!(prio.dequeue(), Some((3, "julia")));
        assert_eq!(prio.dequeue(), Some((3, "naomi")));
        assert_eq!(prio.dequeue(), Some((2, "hello")));
        assert_eq!(prio.dequeue(), Some((1, "world")));
    }

    #[test]
    fn iterate_over_queue() {
        let mut prio = RustyPriorityQueue::<usize, String>::default();
        prio.enqueue(2, "hello".to_string());
        prio.enqueue(3, "julia".to_string());
        prio.enqueue(1, "world".to_string());
        prio.enqueue(3, "naomi".to_string());

        let mut new_prio: RustyPriorityQueue<usize, String> = prio
            .iter()
            .map(|(priority, data)| (*priority, data.to_owned() + " wow"))
            .collect();

        assert_eq!(new_prio.dequeue(), Some((3, "julia wow".to_string())));
        assert_eq!(new_prio.dequeue(), Some((3, "naomi wow".to_string())));
        assert_eq!(new_prio.dequeue(), Some((2, "hello wow".to_string())));
        assert_eq!(new_prio.dequeue(), Some((1, "world wow".to_string())));
    }

    #[test]
    fn into_iterate_over_queue() {
        let mut prio = RustyPriorityQueue::<usize, String>::default();
        prio.enqueue(2, "hello".to_string());
        prio.enqueue(3, "julia".to_string());
        prio.enqueue(1, "world".to_string());
        prio.enqueue(3, "naomi".to_string());

        let mut new_prio: RustyPriorityQueue<usize, String> = prio
            .into_iter()
            .map(|(priority, data)| (priority, data.to_owned() + " wow"))
            .collect();

        assert_eq!(new_prio.dequeue(), Some((3, "julia wow".to_string())));
        assert_eq!(new_prio.dequeue(), Some((3, "naomi wow".to_string())));
        assert_eq!(new_prio.dequeue(), Some((2, "hello wow".to_string())));
        assert_eq!(new_prio.dequeue(), Some((1, "world wow".to_string())));
    }
}
