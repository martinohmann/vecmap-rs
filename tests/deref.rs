use vecmap::{vecmap, VecMap};

#[test]
fn unfortunate_keys() {
    // A map with `usize` keys. This is unfortunate, because we implemented `Index<usize>` for
    // `VecMap<K, V>` to lookup values by index.
    let map: VecMap<usize, &str> = vecmap! {1 => "foo", 0 => "bar", 2 => "baz"};
    // Lookup by value: `usize` is treated as an array index.
    assert_eq!(&map[0], &"foo");
    // Lookup by ref: `&usize` is treated as a map key.
    assert_eq!(&map[&0], &"bar");
}
