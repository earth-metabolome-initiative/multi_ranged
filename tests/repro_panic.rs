#[test]
fn test_reproduce_panic() {
    use multi_ranged::{MultiRange, MultiRanged};
    let mut range = MultiRange::<u8>::default();
    let _ = range.insert(255);
    // This second insert should panic
    let _ = range.insert(10);
}
