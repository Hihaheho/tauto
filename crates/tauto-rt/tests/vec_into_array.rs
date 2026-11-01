use std::cell::Cell;
use tauto_rt::{Rc, stdlib::vec_into_array};

#[test]
fn moves_elements_in_order_and_releases_them_once() {
    struct Item(Rc<Cell<usize>>, usize);
    impl Drop for Item {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }
    let drops = Rc::new(Cell::new(0));
    let values = (0..100).map(|i| Item(drops.clone(), i)).collect();
    let array = vec_into_array(values);
    assert_eq!(drops.get(), 0);
    assert!(array.iter().enumerate().all(|(i, x)| x.1 == i));
    let shared = array.clone();
    drop(array);
    assert_eq!(drops.get(), 0);
    drop(shared);
    assert_eq!(drops.get(), 100);
}

#[test]
fn large_flat_array_on_an_ordinary_test_thread_stack() {
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            let array = vec_into_array((0..100_000_u64).collect());
            assert_eq!(array.len(), 100_000);
            assert_eq!(array.iter().sum::<u64>(), 4_999_950_000);
            let shared = array.clone();
            drop(array);
            assert_eq!(shared[99_999], 99_999);
            drop(shared);
        })
        .unwrap()
        .join()
        .unwrap();
    assert!(vec_into_array::<u64>(Vec::new()).is_empty());
}
