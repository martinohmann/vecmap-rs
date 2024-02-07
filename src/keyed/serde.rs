use super::{Keyed, KeyedVecSet};
use core::fmt;
use core::marker::PhantomData;
use serde::de::{self, value::SeqDeserializer};
use serde::ser;

impl<K, V> ser::Serialize for KeyedVecSet<K, V>
where
    K: ser::Serialize + Ord,
    V: ser::Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: ser::Serializer,
    {
        serializer.collect_seq(self)
    }
}

impl<'de, K, V> de::Deserialize<'de> for KeyedVecSet<K, V>
where
    K: de::Deserialize<'de> + Ord,
    V: de::Deserialize<'de> + Keyed<K>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        struct KeyedVecSetVisitor<K, V>(PhantomData<(K, V)>);

        impl<'de, K, V> de::Visitor<'de> for KeyedVecSetVisitor<K, V>
        where
            K: de::Deserialize<'de> + Ord,
            V: de::Deserialize<'de> + Keyed<K>,
        {
            type Value = KeyedVecSet<K, V>;

            fn expecting(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt.write_str("a sequence")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: de::SeqAccess<'de>,
            {
                let mut values = KeyedVecSet::with_capacity(seq.size_hint().unwrap_or(0));

                while let Some(element) = seq.next_element()? {
                    values.insert(element);
                }

                Ok(values)
            }
        }

        deserializer.deserialize_seq(KeyedVecSetVisitor(PhantomData))
    }
}

impl<'de, K, V, E> de::IntoDeserializer<'de, E> for KeyedVecSet<K, V>
where
    K: de::IntoDeserializer<'de, E> + Ord,
    V: de::IntoDeserializer<'de, E>,
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
    use serde_test::{assert_tokens, Token};

    #[test]
    fn ser_de_empty() {
        let map = KeyedVecSet::<u8, u8>::new();
        assert_tokens(&map, &[Token::Seq { len: Some(0) }, Token::SeqEnd]);
    }

    #[test]
    fn ser_de() {
        let map = KeyedVecSet::<&str, (&str, i32)>::from([("a", 1), ("b", 2), ("c", 3)]);
        assert_tokens(
            &map,
            &[
                Token::Seq { len: Some(3) },
                Token::Tuple { len: 2 },
                Token::BorrowedStr("a"),
                Token::I32(1),
                Token::TupleEnd,
                Token::Tuple { len: 2 },
                Token::BorrowedStr("b"),
                Token::I32(2),
                Token::TupleEnd,
                Token::Tuple { len: 2 },
                Token::BorrowedStr("c"),
                Token::I32(3),
                Token::TupleEnd,
                Token::SeqEnd,
            ],
        );
    }
}
