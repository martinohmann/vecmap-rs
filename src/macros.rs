#[macro_export]
/// Create an `VecMap` from a list of key-value pairs
///
/// ## Example
///
/// ```
/// use vecmap::vecmap;
///
/// let map = vecmap!{
///     "a" => 1,
///     "b" => 2,
/// };
/// assert_eq!(map["a"], 1);
/// assert_eq!(map["b"], 2);
/// assert_eq!(map.get("c"), None);
///
/// // "a" is the first key
/// assert_eq!(map.keys().next(), Some(&"a"));
/// ```
macro_rules! vecmap {
    ($($key:expr => $value:expr,)+) => { $crate::vecmap!($($key => $value),+) };
    ($($key:expr => $value:expr),*) => {
        {
            // Note: `stringify!($key)` is just here to consume the repetition,
            // but we throw away that string literal during constant evaluation.
            const CAP: usize = <[()]>::len(&[$({ stringify!($key); }),*]);
            let mut map = $crate::VecMap::with_capacity(CAP);
            $(
                map.insert($key, $value);
            )*
            map
        }
    };
}
