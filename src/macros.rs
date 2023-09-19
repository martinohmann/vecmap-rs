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
#[macro_export]
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

/// Create an `VecSet` from a list of values
///
/// ## Example
///
/// ```
/// use vecmap::vecset;
///
/// let set = vecset!{"a", "b"};
/// assert!(set.contains("a"));
/// assert!(set.contains("b"));
/// assert!(!set.contains("c"));
///
/// // "a" is the first value
/// assert_eq!(set.iter().next(), Some(&"a"));
/// ```
#[macro_export]
macro_rules! vecset {
    ($($value:expr,)+) => { $crate::vecset!($($value),+) };
    ($($value:expr),*) => {
        {
            // Note: `stringify!($key)` is just here to consume the repetition,
            // but we throw away that string literal during constant evaluation.
            const CAP: usize = <[()]>::len(&[$({ stringify!($value); }),*]);
            let mut set = $crate::VecSet::with_capacity(CAP);
            $(
                set.insert($value);
            )*
            set
        }
    };
}
