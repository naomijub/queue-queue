use std::{cmp::Ordering, collections::BinaryHeap};

use crate::PriorityQueue;

#[derive(Debug, PartialEq, Eq, Clone)]
struct Node<P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> {
    priority: P,
    data: T,
}

impl<P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> PartialOrd for Node<P, T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        other.priority.partial_cmp(&self.priority)
    }
}

impl<P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> Ord for Node<P, T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other
            .priority
            .partial_cmp(&self.priority)
            .unwrap_or(Ordering::Less)
    }
}

#[derive(Debug)]
/// A priority queue implementation based on Rust's `BinaryHeap`.
/// Templated with `P` for priority and `T` for data.
///
/// - `P` must be `PartialOrd`, `PartialEq`, and `Eq`.
/// - `T` must be `PartialEq` and `Eq`.
///
/// If Node A and Node B have the same priority, but Node A was added before Node B,
/// then Node A will be prioritized over Node B.
/// See [`PriorityQueue`](trait.PriorityQueue.html) for more information.
///
/// # Examples
///
/// ```rust
/// # use queue_queue::inverse::InversePriorityQueue;
/// # use queue_queue::PriorityQueue;
///
/// let mut prio = InversePriorityQueue::<usize, String>::default();
/// prio.enqueue(2, "hello".to_string());
/// prio.enqueue(3, "julia".to_string());
/// prio.enqueue(1, "world".to_string());
/// prio.enqueue(3, "naomi".to_string());
///
/// let mut new_prio: InversePriorityQueue<usize, String> = prio
///     .into_iter()
///     .map(|(priority, data)| (priority, data.to_owned() + " wow"))
///     .collect();
///
/// assert_eq!(new_prio.dequeue(), Some((1, "world wow".to_string())));
/// assert_eq!(new_prio.dequeue(), Some((2, "hello wow".to_string())));
/// assert_eq!(new_prio.dequeue(), Some((3, "naomi wow".to_string())));
/// assert_eq!(new_prio.dequeue(), Some((3, "julia wow".to_string())));
/// ```
pub struct InversePriorityQueue<P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> {
    queue: BinaryHeap<Node<P, T>>,
}

impl<P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> Default for InversePriorityQueue<P, T> {
    fn default() -> Self {
        Self {
            queue: BinaryHeap::new(),
        }
    }
}

impl<P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> PriorityQueue<P, T>
    for InversePriorityQueue<P, T>
{
    fn with_capacity(capacity: usize) -> Self {
        Self {
            queue: BinaryHeap::with_capacity(capacity),
        }
    }

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

    fn capacity(&self) -> usize {
        self.queue.capacity()
    }

    fn append(&mut self, mut other: Self) {
        self.queue.append(&mut other.queue);
    }

    /// Extend the priority queue with an iterator
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use queue_queue::inverse::InversePriorityQueue;
    /// # use queue_queue::PriorityQueue;
    ///
    /// let mut prio = InversePriorityQueue::<usize, String>::default();
    /// prio.extend(vec![(2, "world".to_string()), (3, "hello".to_string())]);
    /// assert_eq!(prio.dequeue(), Some((2, "world".to_string())));
    /// assert_eq!(prio.dequeue(), Some((3, "hello".to_string())));
    /// assert_eq!(prio.dequeue(), None);
    /// ```
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = (P, T)>,
    {
        self.queue.extend(iter.into_iter().map(|(x, y)| Node {
            priority: x,
            data: y,
        }));
    }

    fn reserve(&mut self, additional: usize) {
        self.queue.reserve(additional);
    }

    fn reserve_exact(&mut self, additional: usize) {
        self.queue.reserve_exact(additional);
    }

    fn shrink_to_fit(&mut self) {
        self.queue.shrink_to_fit();
    }

    fn shrink_to(&mut self, capacity: usize) {
        self.queue.shrink_to(capacity);
    }

    fn clear(&mut self) {
        self.queue.clear();
    }

    fn drain(&mut self) -> impl Iterator<Item = (P, T)> + '_ {
        self.queue.drain().map(|n| (n.priority, n.data))
    }

    fn contains(&self, data: &T) -> bool {
        self.queue.iter().any(|node| &node.data == data)
    }

    fn contains_at(&self, priority: &P, data: &T) -> bool {
        self.queue
            .iter()
            .any(|node| &node.data == data && &node.priority == priority)
    }

    fn remove(&mut self, data: &T) -> bool {
        let original_size = self.queue.len();
        self.queue.retain(|node| &node.data != data);
        let new_size = self.queue.len();

        original_size != new_size
    }

    fn remove_at(&mut self, priority: &P, data: &T) -> bool {
        let original_size = self.queue.len();
        self.queue.retain(|node| {
            if &node.priority == priority {
                &node.data != data
            } else {
                true
            }
        });
        let new_size = self.queue.len();

        original_size != new_size
    }

    fn max_node(&self) -> Option<(&P, &T)> {
        self.queue
            .iter()
            .max_by(|a, b| {
                a.priority
                    .partial_cmp(&b.priority)
                    .unwrap_or(Ordering::Equal)
            })
            .map(|node| (&node.priority, &node.data))
    }

    fn min_node(&self) -> Option<(&P, &T)> {
        self.queue
            .iter()
            .min_by(|a, b| {
                a.priority
                    .partial_cmp(&b.priority)
                    .unwrap_or(Ordering::Equal)
            })
            .map(|node| (&node.priority, &node.data))
    }
}

impl<P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> InversePriorityQueue<P, T> {
    #[must_use]
    /// Get an iterator over the priority queue
    pub const fn iter(&self) -> InversePriorityQueueIterator<P, T> {
        InversePriorityQueueIterator {
            internal: &self.queue,
            index: 0,
        }
    }

    #[must_use]
    /// Convert the priority queue into an iterator
    pub fn into_iter(self) -> InversePriorityQueueIntoIterator<P, T> {
        InversePriorityQueueIntoIterator { queue: self.queue }
    }

    /// Update the priority of an item in the queue.
    ///
    /// > This is a very slow operation!
    /// > * it uses unsafe `std::mem::transmute_copy` under the hhod to guarantee allocation of priority `P` on every possible scenario.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use queue_queue::inverse::InversePriorityQueue;
    /// # use queue_queue::PriorityQueue;
    ///
    /// let mut prio = InversePriorityQueue::<usize, String>::default();
    /// prio.enqueue(5, "julia".to_string());
    /// prio.enqueue(2, "hello".to_string());
    /// prio.enqueue(3, "julia".to_string());
    /// prio.enqueue(1, "world".to_string());
    /// prio.enqueue(3, "naomi".to_string());

    /// let ref_str = "julia".to_string();
    /// let mut new = prio.update(3, 7,&ref_str);

    /// assert_eq!(new.dequeue(), Some((1, "world".to_string())));
    /// assert_eq!(new.dequeue(), Some((2, "hello".to_string())));
    /// assert_eq!(new.dequeue(), Some((3, "naomi".to_string())));
    /// assert_eq!(new.dequeue(), Some((5, "julia".to_string())));
    /// assert_eq!(new.dequeue(), Some((7, "julia".to_string())));
    /// ```
    #[must_use]
    #[allow(clippy::needless_pass_by_value)]
    pub fn update(mut self, old: P, new: P, data: &T) -> Self {
        self.queue
            .drain()
            .map(|n| {
                if n.priority == old && &n.data == data {
                    let copy: P = unsafe { std::mem::transmute_copy(&new) };
                    (copy, n.data)
                } else {
                    (n.priority, n.data)
                }
            })
            .collect()
    }

    /// Update the priority of an item in the queue with a reference to the data.
    #[allow(clippy::needless_pass_by_value)]
    pub fn update_as(&mut self, old: P, new: P, data: T) {
        self.queue
            .retain(|n| !(n.priority == old && n.data == data));
        self.enqueue(new, data);
    }
}

/// An Iterator struct for `InversePriorityQueue`
pub struct InversePriorityQueueIterator<'b, P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> {
    internal: &'b BinaryHeap<Node<P, T>>,
    index: usize,
}

impl<'b, P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> Iterator
    for InversePriorityQueueIterator<'b, P, T>
{
    type Item = (&'b P, &'b T);

    fn next(&mut self) -> Option<Self::Item> {
        let val = self
            .internal
            .iter()
            .nth(self.index)
            .map(|n| (&n.priority, &n.data));
        self.index += 1;
        val
    }
}

impl<P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> FromIterator<(P, T)>
    for InversePriorityQueue<P, T>
{
    fn from_iter<I: IntoIterator<Item = (P, T)>>(iter: I) -> Self {
        let mut collection = Self::default();

        for i in iter {
            collection.enqueue(i.0, i.1);
        }

        collection
    }
}

/// An `IntoIterator` struct for `InversePriorityQueue`
pub struct InversePriorityQueueIntoIterator<P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> {
    queue: BinaryHeap<Node<P, T>>,
}

impl<P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> Iterator
    for InversePriorityQueueIntoIterator<P, T>
{
    type Item = (P, T);

    fn next(&mut self) -> Option<Self::Item> {
        self.queue.pop().map(|node| (node.priority, node.data))
    }
}

impl<P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> IntoIterator
    for InversePriorityQueue<P, T>
{
    type Item = (P, T);
    type IntoIter = InversePriorityQueueIntoIterator<P, T>;

    fn into_iter(self) -> Self::IntoIter {
        InversePriorityQueueIntoIterator { queue: self.queue }
    }
}

impl<'b, P: PartialOrd + PartialEq + Eq, T: PartialEq + Eq> IntoIterator
    for &'b InversePriorityQueue<P, T>
{
    type IntoIter = InversePriorityQueueIterator<'b, P, T>;
    type Item = (&'b P, &'b T);
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_is_empty() {
        let prio = InversePriorityQueue::<usize, String>::default();

        assert_eq!(prio.len(), 0);
        assert!(prio.is_empty());
    }

    #[test]
    fn enqueue_once_has_size_1() {
        let mut prio = InversePriorityQueue::<usize, String>::default();

        prio.enqueue(3, String::from("hello world"));
        assert_eq!(prio.len(), 1);
        assert_eq!(prio.peek(), Some((&3, &String::from("hello world"))));
    }

    #[test]
    fn dequeues_in_order() {
        let mut prio = InversePriorityQueue::<usize, &str>::default();
        prio.enqueue(2, "hello");
        prio.enqueue(3, "julia");
        prio.enqueue(1, "world");
        prio.enqueue(3, "naomi");

        assert_eq!(prio.len(), 4);

        assert_eq!(prio.dequeue(), Some((1, "world")));
        assert_eq!(prio.dequeue(), Some((2, "hello")));
        assert_eq!(prio.dequeue(), Some((3, "julia")));
        assert_eq!(prio.dequeue(), Some((3, "naomi")));
    }

    #[test]
    fn iterate_over_queue() {
        let mut prio = InversePriorityQueue::<usize, String>::default();
        prio.enqueue(2, "hello".to_string());
        prio.enqueue(3, "julia".to_string());
        prio.enqueue(1, "world".to_string());
        prio.enqueue(3, "naomi".to_string());

        let mut new_prio: InversePriorityQueue<usize, String> = prio
            .iter()
            .map(|(priority, data)| (*priority, data.clone() + " wow"))
            .collect();

        assert_eq!(new_prio.dequeue(), Some((1, "world wow".to_string())));
        assert_eq!(new_prio.dequeue(), Some((2, "hello wow".to_string())));
        assert_eq!(new_prio.dequeue(), Some((3, "julia wow".to_string())));
        assert_eq!(new_prio.dequeue(), Some((3, "naomi wow".to_string())));
    }

    #[test]
    fn into_iterate_over_queue() {
        let mut prio = InversePriorityQueue::<usize, String>::default();
        prio.enqueue(2, "hello".to_string());
        prio.enqueue(3, "julia".to_string());
        prio.enqueue(1, "world".to_string());
        prio.enqueue(3, "naomi".to_string());

        let ref_str = "julia".to_string();
        assert!(prio.contains(&ref_str));
        assert!(prio.contains_at(&3, &ref_str));
        assert!(!prio.contains_at(&2, &ref_str));

        let mut new_prio: InversePriorityQueue<usize, String> = prio
            .into_iter()
            .map(|(priority, data)| (priority, data.to_owned() + " wow"))
            .collect();

        let new_ref_str = "julia wow".to_string();
        assert!(!new_prio.contains(&ref_str));
        assert!(!new_prio.contains_at(&3, &ref_str));
        assert!(!new_prio.contains_at(&2, &ref_str));
        assert!(new_prio.contains(&new_ref_str));
        assert!(new_prio.contains_at(&3, &new_ref_str));
        assert!(!new_prio.contains_at(&2, &new_ref_str));

        assert_eq!(new_prio.dequeue(), Some((1, "world wow".to_string())));
        assert_eq!(new_prio.dequeue(), Some((2, "hello wow".to_string())));
        assert_eq!(new_prio.dequeue(), Some((3, "naomi wow".to_string())));
        assert_eq!(new_prio.dequeue(), Some((3, "julia wow".to_string())));
    }

    #[test]
    fn node_order() {
        let node1 = Node {
            priority: 3,
            data: "hello".to_string(),
        };
        let node2 = Node {
            priority: 2,
            data: "julia".to_string(),
        };

        assert!(node1 < node2);
    }

    #[test]
    fn queue_with_capacity() {
        let prio = InversePriorityQueue::<usize, String>::with_capacity(10);
        assert_eq!(prio.len(), 0);
        assert!(prio.is_empty());
        assert_eq!(prio.capacity(), 10);

        let default_prio = InversePriorityQueue::<usize, String>::default();
        assert_eq!(default_prio.len(), 0);
        assert!(default_prio.is_empty());
        assert_eq!(default_prio.capacity(), 0);
    }

    #[test]
    fn appends_into_queue() {
        let mut prio = InversePriorityQueue::<usize, &str>::default();
        assert_eq!(prio.len(), 0);
        prio.extend([(2, "hello"), (3, "julia"), (1, "world"), (3, "naomi")]);
        assert_eq!(prio.len(), 4);

        let mut append_prio = InversePriorityQueue::<usize, &str>::default();
        assert_eq!(append_prio.len(), 0);
        append_prio.append(prio);
        assert_eq!(append_prio.len(), 4);

        assert_eq!(append_prio.dequeue(), Some((1, "world")));
    }

    #[test]
    fn capacity_management() {
        let mut prio = InversePriorityQueue::<usize, &str>::default();
        assert_eq!(prio.capacity(), 0);
        prio.reserve(3);
        assert_eq!(prio.capacity(), 4);
        prio.shrink_to_fit();
        assert_eq!(prio.capacity(), 0);
        prio.reserve_exact(3);
        assert_eq!(prio.capacity(), 3);
        prio.shrink_to(2);
        assert_eq!(prio.capacity(), 2);
    }

    #[test]
    fn clears_queue() {
        let mut prio = InversePriorityQueue::<usize, String>::default();
        prio.enqueue(2, "hello".to_string());
        prio.enqueue(3, "julia".to_string());
        prio.enqueue(1, "world".to_string());
        prio.enqueue(3, "naomi".to_string());

        assert_eq!(prio.len(), 4);
        prio.clear();
        assert_eq!(prio.len(), 0);
    }

    #[test]
    fn drain_queue() {
        let mut prio = InversePriorityQueue::<usize, String>::default();
        prio.enqueue(2, "hello".to_string());

        assert!(!prio.is_empty());

        for x in prio.drain() {
            assert_eq!(x, (2, "hello".to_string()));
        }

        assert!(prio.is_empty());
    }

    #[test]
    fn remove_node() {
        let mut prio = InversePriorityQueue::<usize, String>::default();
        prio.enqueue(5, "julia".to_string());
        prio.enqueue(2, "hello".to_string());
        prio.enqueue(3, "julia".to_string());
        prio.enqueue(1, "world".to_string());
        prio.enqueue(3, "naomi".to_string());

        let ref_str = "julia".to_string();
        assert!(prio.remove(&ref_str));

        // assert_eq!(prio.dequeue(), Some((3, "julia".to_string())));
        assert_eq!(prio.dequeue(), Some((1, "world".to_string())));
        assert_eq!(prio.dequeue(), Some((2, "hello".to_string())));
        assert_eq!(prio.dequeue(), Some((3, "naomi".to_string())));
    }

    #[test]
    fn remove_node_at_prio() {
        let mut prio = InversePriorityQueue::<usize, String>::default();
        prio.enqueue(5, "julia".to_string());
        prio.enqueue(2, "hello".to_string());
        prio.enqueue(3, "julia".to_string());
        prio.enqueue(1, "world".to_string());
        prio.enqueue(3, "naomi".to_string());

        let ref_str = "julia".to_string();
        assert!(prio.remove_at(&3, &ref_str));

        assert_eq!(prio.dequeue(), Some((1, "world".to_string())));
        assert_eq!(prio.dequeue(), Some((2, "hello".to_string())));
        assert_eq!(prio.dequeue(), Some((3, "naomi".to_string())));
        assert_eq!(prio.dequeue(), Some((5, "julia".to_string())));
    }

    #[test]
    fn update() {
        let mut prio = InversePriorityQueue::<usize, String>::default();
        prio.enqueue(5, "julia".to_string());
        prio.enqueue(2, "hello".to_string());
        prio.enqueue(3, "julia".to_string());
        prio.enqueue(1, "world".to_string());
        prio.enqueue(3, "naomi".to_string());

        let ref_str = "julia".to_string();
        let mut new = prio.update(3, 7, &ref_str);

        assert_eq!(new.dequeue(), Some((1, "world".to_string())));
        assert_eq!(new.dequeue(), Some((2, "hello".to_string())));
        assert_eq!(new.dequeue(), Some((3, "naomi".to_string())));
        assert_eq!(new.dequeue(), Some((5, "julia".to_string())));
        assert_eq!(new.dequeue(), Some((7, "julia".to_string())));
    }

    #[test]
    fn min_max() {
        let mut prio = InversePriorityQueue::<usize, String>::default();
        prio.enqueue(5, "julia".to_string());
        prio.enqueue(2, "hello".to_string());
        prio.enqueue(3, "julia".to_string());
        prio.enqueue(1, "world".to_string());
        prio.enqueue(3, "naomi".to_string());

        assert_eq!(prio.max_node(), Some((&5, &"julia".to_string())));
        assert_eq!(prio.min_node(), Some((&1, &"world".to_string())));
    }

    #[test]
    fn update_as() {
        let mut prio = InversePriorityQueue::<usize, String>::default();
        prio.enqueue(5, "julia".to_string());
        prio.enqueue(2, "hello".to_string());
        prio.enqueue(3, "julia".to_string());
        prio.enqueue(1, "world".to_string());
        prio.enqueue(3, "naomi".to_string());

        let ref_str = "julia".to_string();
        prio.update_as(3, 7, ref_str);

        assert_eq!(prio.dequeue(), Some((1, "world".to_string())));
        assert_eq!(prio.dequeue(), Some((2, "hello".to_string())));
        assert_eq!(prio.dequeue(), Some((3, "naomi".to_string())));
        assert_eq!(prio.dequeue(), Some((5, "julia".to_string())));
        assert_eq!(prio.dequeue(), Some((7, "julia".to_string())));
    }
}
