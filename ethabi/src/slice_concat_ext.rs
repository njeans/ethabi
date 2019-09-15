//! Taken from https://doc.rust-lang.org/std/slice/trait.SliceConcatExt.html
//!
use std::prelude::v1::*;
use std::borrow::Borrow;

macro_rules! spezialize_for_lengths {
    ($separator:expr, $target:expr, $iter:expr; $($num:expr),*) => {
        let mut target = $target;
        let iter = $iter;
        let sep_bytes = $separator;
        match $separator.len() {
            $(
                // loops with hardcoded sizes run much faster
                // specialize the cases with small separator lengths
                $num => {
                    for s in iter {
                        copy_slice_and_advance!(target, sep_bytes);
                        copy_slice_and_advance!(target, s.borrow().as_ref());
                    }
                },
            )*
            _ => {
                // arbitrary non-zero size fallback
                for s in iter {
                    copy_slice_and_advance!(target, sep_bytes);
                    copy_slice_and_advance!(target, s.borrow().as_ref());
                }
            }
        }
    };
}

macro_rules! copy_slice_and_advance {
    ($target:expr, $bytes:expr) => {
        let len = $bytes.len();
        let (head, tail) = {$target}.split_at_mut(len);
        head.copy_from_slice($bytes);
        $target = tail;
    }
}

////////////////////////////////////////////////////////////////////////////////
// Extension traits for slices over specific kinds of data
////////////////////////////////////////////////////////////////////////////////
/// An extension trait for concatenating slices
///
/// While this trait is unstable, the methods are stable. `SliceConcatExt` is
/// included in the [standard library prelude], so you can use [`join()`] and
/// [`concat()`] as if they existed on `[T]` itself.
///
/// [standard library prelude]: ../../std/prelude/index.html
/// [`join()`]: #tymethod.join
/// [`concat()`]: #tymethod.concat
pub trait SliceConcatExt<T: ?Sized> {
    /// The resulting type after concatenation
    type Output;

    /// Flattens a slice of `T` into a single value `Self::Output`.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(["hello", "world"].concat(), "helloworld");
    /// assert_eq!([[1, 2], [3, 4]].concat(), [1, 2, 3, 4]);
    /// ```
    fn concat(&self) -> Self::Output;

    /// Flattens a slice of `T` into a single value `Self::Output`, placing a
    /// given separator between each.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(["hello", "world"].join(" "), "hello world");
    /// assert_eq!([[1, 2], [3, 4]].join(&0), [1, 2, 0, 3, 4]);
    /// ```
    fn join(&self, sep: &T) -> Self::Output;

    /// Flattens a slice of `T` into a single value `Self::Output`, placing a
    /// given separator between each.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(deprecated)]
    /// assert_eq!(["hello", "world"].connect(" "), "hello world");
    /// assert_eq!([[1, 2], [3, 4]].connect(&0), [1, 2, 0, 3, 4]);
    /// ```
    fn connect(&self, sep: &T) -> Self::Output {
        self.join(sep)
    }
}

impl<S: Borrow<str>> SliceConcatExt<str> for [S] {
    type Output = String;

    fn concat(&self) -> String {
        self.join("")
    }

    fn join(&self, sep: &str) -> String {
        unsafe {
            String::from_utf8_unchecked( join_generic_copy(self, sep.as_bytes()) )
        }
    }
}

// Optimized join implementation that works for both Vec<T> (T: Copy) and String's inner vec
// Currently (2018-05-13) there is a bug with type inference and specialization (see issue #36262)
// For this reason SliceConcatExt<T> is not specialized for T: Copy and SliceConcatExt<str> is the
// only user of this function. It is left in place for the time when that is fixed.
//
// the bounds for String-join are S: Borrow<str> and for Vec-join Borrow<[T]>
// [T] and str both impl AsRef<[T]> for some T
// => s.borrow().as_ref() and we always have slices
fn join_generic_copy<B, T, S>(slice: &[S], sep: &[T]) -> Vec<T>
    where
        T: Copy,
        B: AsRef<[T]> + ?Sized,
        S: Borrow<B>,
{
    let sep_len = sep.len();
    let mut iter = slice.iter();

    // the first slice is the only one without a separator preceding it
    let first = match iter.next() {
        Some(first) => first,
        None => return vec![],
    };

    // compute the exact total length of the joined Vec
    // if the `len` calculation overflows, we'll panic
    // we would have run out of memory anyway and the rest of the function requires
    // the entire Vec pre-allocated for safety
    let len =  sep_len.checked_mul(iter.len()).and_then(|n| {
        slice.iter()
            .map(|s| s.borrow().as_ref().len())
            .try_fold(n, usize::checked_add)
    }).expect("attempt to join into collection with len > usize::MAX");

    // crucial for safety
    let mut result = Vec::with_capacity(len);
    assert!(result.capacity() >= len);

    result.extend_from_slice(first.borrow().as_ref());

    unsafe {
        {
            let pos = result.len();
            let target = result.get_unchecked_mut(pos..len);

            // copy separator and slices over without bounds checks
            // generate loops with hardcoded offsets for small separators
            // massive improvements possible (~ x2)
            spezialize_for_lengths!(sep, target, iter; 0, 1, 2, 3, 4);
        }
        result.set_len(len);
    }
    result
}

impl<T: Clone, V: Borrow<[T]>> SliceConcatExt<T> for [V] {
    type Output = Vec<T>;

    fn concat(&self) -> Vec<T> {
        let size = self.iter().map(|slice| slice.borrow().len()).sum();
        let mut result = Vec::with_capacity(size);
        for v in self {
            result.extend_from_slice(v.borrow())
        }
        result
    }

    fn join(&self, sep: &T) -> Vec<T> {
        let mut iter = self.iter();
        let first = match iter.next() {
            Some(first) => first,
            None => return vec![],
        };
        let size = self.iter().map(|slice| slice.borrow().len()).sum::<usize>() + self.len() - 1;
        let mut result = Vec::with_capacity(size);
        result.extend_from_slice(first.borrow());

        for v in iter {
            result.push(sep.clone());
            result.extend_from_slice(v.borrow())
        }
        result
    }
}
