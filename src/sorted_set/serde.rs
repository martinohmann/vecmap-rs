use super::SortedVecSet;
use core::fmt;
use core::marker::PhantomData;
use serde::de::{self, value::SeqDeserializer};
use serde::ser;

impl<T> ser::Serialize for SortedVecSet<T>
where
    T: ser::Serialize + Ord,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: ser::Serializer,
    {
        serializer.collect_seq(self)
    }
}

impl<'de, T> de::Deserialize<'de> for SortedVecSet<T>
where
    T: de::Deserialize<'de> + Ord,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        struct SortedVecSetVisitor<T>(PhantomData<T>);

        impl<'de, T> de::Visitor<'de> for SortedVecSetVisitor<T>
        where
            T: de::Deserialize<'de> + Ord,
        {
            type Value = SortedVecSet<T>;

            fn expecting(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt.write_str("a sequence")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: de::SeqAccess<'de>,
            {
                let mut values = SortedVecSet::with_capacity(seq.size_hint().unwrap_or(0));

                while let Some(element) = seq.next_element()? {
                    values.insert(element);
                }

                Ok(values)
            }
        }

        deserializer.deserialize_seq(SortedVecSetVisitor(PhantomData))
    }
}

impl<'de, T, E> de::IntoDeserializer<'de, E> for SortedVecSet<T>
where
    T: de::IntoDeserializer<'de, E> + Ord,
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
    use serde_test::{Token, assert_tokens};

    #[test]
    fn ser_de_empty() {
        let set = SortedVecSet::<&str>::new();
        assert_tokens(&set, &[Token::Seq { len: Some(0) }, Token::SeqEnd]);
    }

    #[test]
    fn ser_de() {
        // Serializes in sorted order regardless of insertion order.
        let set = SortedVecSet::from(["c", "a", "b"]);
        assert_tokens(
            &set,
            &[
                Token::Seq { len: Some(3) },
                Token::BorrowedStr("a"),
                Token::BorrowedStr("b"),
                Token::BorrowedStr("c"),
                Token::SeqEnd,
            ],
        );
    }
}
