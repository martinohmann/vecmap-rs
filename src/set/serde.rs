use super::VecSet;
use core::fmt;
use core::marker::PhantomData;
use serde::de::{self, value::SeqDeserializer};
use serde::ser;

impl<T> ser::Serialize for VecSet<T>
where
    T: ser::Serialize + Eq,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: ser::Serializer,
    {
        serializer.collect_seq(self)
    }
}

impl<'de, T> de::Deserialize<'de> for VecSet<T>
where
    T: de::Deserialize<'de> + Eq,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        struct VecSetVisitor<T>(PhantomData<T>);

        impl<'de, T> de::Visitor<'de> for VecSetVisitor<T>
        where
            T: de::Deserialize<'de> + Eq,
        {
            type Value = VecSet<T>;

            fn expecting(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt.write_str("a sequence")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: de::SeqAccess<'de>,
            {
                let mut values = VecSet::with_capacity(seq.size_hint().unwrap_or(0));

                while let Some(element) = seq.next_element()? {
                    values.insert(element);
                }

                Ok(values)
            }
        }

        deserializer.deserialize_seq(VecSetVisitor(PhantomData))
    }
}

impl<'de, T, E> de::IntoDeserializer<'de, E> for VecSet<T>
where
    T: de::IntoDeserializer<'de, E> + Eq,
    E: de::Error,
{
    type Deserializer = SeqDeserializer<<Self as IntoIterator>::IntoIter, E>;

    fn into_deserializer(self) -> Self::Deserializer {
        SeqDeserializer::new(self.into_iter())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use alloc::string::String;
    use alloc::vec;
    use serde_json::json;

    #[test]
    fn serialize() {
        let set = VecSet::from(["a", "b", "c"]);
        let value = serde_json::to_value(&set).unwrap();
        let expected = json!(["a", "b", "c"]);

        assert_eq!(value, expected);
    }

    #[test]
    fn deserialize() {
        let value = json!(["a", "b", "c"]);
        let set: VecSet<String> = serde_json::from_value(value).unwrap();
        let expected = VecSet::from(["a".into(), "b".into(), "c".into()]);

        assert_eq!(set, expected);
    }
}
