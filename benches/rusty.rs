use criterion::{black_box, criterion_group, criterion_main, Criterion};
use queue_queue::{rusty::RustyPriorityQueue, PriorityQueue};

fn criterion_benchmark(c: &mut Criterion) {
    let mut queue = RustyPriorityQueue::<usize, usize>::default();
    c.bench_function("enqueue", |b| {
        b.iter(|| queue.enqueue(black_box(1), black_box(1)))
    });

    let mut queue = RustyPriorityQueue::<usize, usize>::default();
    queue.enqueue(1, 1);
    queue.enqueue(2, 2);
    queue.enqueue(2, 22);
    queue.enqueue(3, 3);
    c.bench_function("dequeue", |b| b.iter(|| queue.dequeue()));

    let mut queue = RustyPriorityQueue::<usize, usize>::default();
    queue.enqueue(1, 1);
    queue.enqueue(2, 2);
    queue.enqueue(2, 22);
    queue.enqueue(3, 3);
    c.bench_function("iter - 4", |b| {
        b.iter(|| {
            queue
                .iter()
                .map(|(p, v)| (p, v + 1))
                .collect::<RustyPriorityQueue<_, _>>()
        })
    });

    let mut queue = RustyPriorityQueue::<usize, usize>::default();
    for i in 0..40 {
        queue.enqueue(i, i);
    }
    c.bench_function("iter - 40", |b| {
        b.iter(|| {
            queue
                .iter()
                .map(|(p, v)| (p, v + 1))
                .collect::<RustyPriorityQueue<_, _>>()
        })
    });

    let mut queue = RustyPriorityQueue::<usize, usize>::default();
    for i in 0..400 {
        queue.enqueue(i, i);
    }
    c.bench_function("iter - 400", |b| {
        b.iter(|| {
            queue
                .iter()
                .map(|(p, v)| (p, v + 1))
                .collect::<RustyPriorityQueue<_, _>>()
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
