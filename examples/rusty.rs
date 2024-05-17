use queue_queue::prelude::*;

fn main() {
    let mut prio = RustyPriorityQueue::<usize, String>::default();
    prio.enqueue(2, "hello".to_string());
    prio.enqueue(3, "julia".to_string());
    prio.enqueue(1, "world".to_string());
    prio.enqueue(3, "naomi".to_string());

    let mut new_prio: RustyPriorityQueue<usize, String> = prio
        .into_iter()
        .map(|(priority, data)| (priority, data.to_owned() + " wow"))
        .collect();

    println!(
        "{:?} == Some((1, \"world wow\".to_string()))",
        new_prio.min_node()
    );

    println!(
        "{:?} == Some((3, \"julia wow\".to_string()))",
        new_prio.dequeue()
    );
    println!(
        "{:?} == Some((3, \"naomi wow\".to_string()))",
        new_prio.dequeue()
    );
    println!(
        "{:?} == Some((2, \"hello wow\".to_string()))",
        new_prio.dequeue()
    );
    println!(
        "{:?} == Some((1, \"world wow\".to_string()))",
        new_prio.dequeue()
    );
}
