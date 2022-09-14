use super::VecMap;
use core::fmt;
use core::marker::PhantomData;
use serde::de::{self, value::MapDeserializer};
use serde::ser;

impl<K, V> ser::Serialize for VecMap<K, V>
where
    K: ser::Serialize + Eq,
    V: ser::Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: ser::Serializer,
    {
        serializer.collect_map(self)
    }
}

impl<'de, K, V> de::Deserialize<'de> for VecMap<K, V>
where
    K: de::Deserialize<'de> + Eq,
    V: de::Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        struct VecMapVisitor<K, V>(PhantomData<(K, V)>);

        impl<'de, K, V> de::Visitor<'de> for VecMapVisitor<K, V>
        where
            K: de::Deserialize<'de> + Eq,
            V: de::Deserialize<'de>,
        {
            type Value = VecMap<K, V>;

            fn expecting(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt.write_str("a map")
            }

            fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
            where
                A: de::MapAccess<'de>,
            {
                let mut values = VecMap::with_capacity(map.size_hint().unwrap_or(0));

                while let Some((key, value)) = map.next_entry()? {
                    values.insert(key, value);
                }

                Ok(values)
            }
        }

        deserializer.deserialize_map(VecMapVisitor(PhantomData))
    }
}

impl<'de, K, V, E> de::IntoDeserializer<'de, E> for VecMap<K, V>
where
    K: de::IntoDeserializer<'de, E> + Eq,
    V: de::IntoDeserializer<'de, E>,
    E: de::Error,
{
    type Deserializer = MapDeserializer<'de, <Self as IntoIterator>::IntoIter, E>;

    fn into_deserializer(self) -> Self::Deserializer {
        MapDeserializer::new(self.into_iter())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use alloc::string::String;
    use serde_json::json;

    #[test]
    fn serialize() {
        let map = VecMap::from([("a", 1), ("b", 2), ("c", 3)]);
        let value = serde_json::to_value(&map).unwrap();
        let expected = json!({"a": 1, "b": 2, "c": 3});

        assert_eq!(value, expected);
    }

    #[test]
    fn deserialize() {
        let value = json!({"a": 1, "b": 2, "c": 3});
        let map: VecMap<String, u8> = serde_json::from_value(value).unwrap();
        let expected = VecMap::from([("a".into(), 1), ("b".into(), 2), ("c".into(), 3)]);

        assert_eq!(map, expected);
    }
}
