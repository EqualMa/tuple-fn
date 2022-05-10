//! This crate provides [`TupleFnOnce`], [`TupleFnMut`] and [`TupleFn`],
//! corresponding to [`FnOnce`], [`FnMut`] and [`Fn`].
//!
//! [`TupleFnOnce`], [`TupleFnMut`] and [`TupleFn`] enables functions or closures
//! to be called with a tuple of arguments.
//! For example:
//!
//! ```
//! use tuple_fn::*;
//!
//! fn add(a: i32, b: i32) -> i32 {
//!     a + b
//! }
//!
//! let sum = add.call_with_args_tuple((1, 2));
//! assert_eq!(sum, 3);
//! ```
//!
//! These three traits should be named as
//! `FnOnceCallWithArgsTupleExt`, `FnMutCallWithArgsTupleExt`, `FnCallWithArgsTupleExt`
//! by convention, because they are implemented for
//! all corresponding `FnOnce`, `FnMut`, `Fn` types and act like extension traits.
//! They are named as `TupleFn*` just for simplicity.

pub trait KnownFnPointer: TupleFn<Self::ArgsTuple> {
    /// The type of arguments tuple of this `fn` pointer.
    /// For example, the following types in each pair are equivalent.
    ///
    /// ```
    /// # trait TupleSameType {} impl<T> TupleSameType for (T, T) {}
    /// # enum SameType<T1, T2> where (T1, T2): TupleSameType { Yes, T1(T1), T2(T2) }
    /// # use tuple_fn::KnownFnPointer;
    /// # SameType::<
    ///     <fn() -> String as KnownFnPointer>::ArgsTuple
    /// #     ,
    ///     ()
    /// # >::Yes;
    ///
    /// # SameType::<
    ///     <fn(i32) -> String as KnownFnPointer>::ArgsTuple
    /// #     ,
    ///     (i32,)
    /// # >::Yes;
    ///
    /// # SameType::<
    ///     <fn(i32, bool) -> String as KnownFnPointer>::ArgsTuple
    /// #     ,
    ///     (i32, bool)
    /// # >::Yes;
    /// ```
    type ArgsTuple;

    /// The type of the `fn` pointer which accepts corresponding references of arguments.
    /// For example, the following types in each pair are equivalent.
    ///
    /// ```
    /// # trait TupleSameType {} impl<T> TupleSameType for (T, T) {}
    /// # enum SameType<T1, T2> where (T1, T2): TupleSameType { Yes, T1(T1), T2(T2) }
    /// # use tuple_fn::KnownFnPointer;
    /// # SameType::<
    ///     <fn() -> String as KnownFnPointer>::FnPointerWithRefArgs
    /// #     ,
    ///     fn() -> String
    /// # >::Yes;
    ///
    /// # SameType::<
    ///     <fn(i32) -> String as KnownFnPointer>::FnPointerWithRefArgs
    /// #     ,
    ///     fn(&i32) -> String
    /// # >::Yes;
    ///
    /// # SameType::<
    ///     <fn(i32, bool) -> String as KnownFnPointer>::FnPointerWithRefArgs
    /// #     ,
    ///     fn(&i32, &bool) -> String
    /// # >::Yes;
    /// ```
    type FnPointerWithRefArgs;

    /// The corresponding `dyn FnOnce` type.
    /// For example, the following types in each pair are equivalent.
    ///
    /// ```
    /// # trait TupleSameType {} impl<T: ?Sized> TupleSameType for (*const T, *const T) {}
    /// # enum SameType<T1: ?Sized, T2: ?Sized> where (*const T1, *const T2): TupleSameType { Yes, T1(*const T1), T2(*const T2) }
    /// # use tuple_fn::KnownFnPointer;
    /// # SameType::<
    ///     <fn() -> String as KnownFnPointer>::DynFnOnce
    /// #     ,
    ///     dyn FnOnce() -> String
    /// # >::Yes;
    ///
    /// # SameType::<
    ///     <fn(i32) -> String as KnownFnPointer>::DynFnOnce
    /// #     ,
    ///     dyn FnOnce(i32) -> String
    /// # >::Yes;
    ///
    /// # SameType::<
    ///     <fn(i32, bool) -> String as KnownFnPointer>::DynFnOnce
    /// #     ,
    ///     dyn FnOnce(i32, bool) -> String
    /// # >::Yes;
    /// ```
    type DynFnOnce: ?Sized;

    /// The corresponding `dyn DynFnMut` type.
    /// For example, the following types in each pair are equivalent.
    ///
    /// ```
    /// # trait TupleSameType {} impl<T: ?Sized> TupleSameType for (*const T, *const T) {}
    /// # enum SameType<T1: ?Sized, T2: ?Sized> where (*const T1, *const T2): TupleSameType { Yes, T1(*const T1), T2(*const T2) }
    /// # use tuple_fn::KnownFnPointer;
    /// # SameType::<
    ///     <fn() -> String as KnownFnPointer>::DynFnMut
    /// #     ,
    ///     dyn FnMut() -> String
    /// # >::Yes;
    ///
    /// # SameType::<
    ///     <fn(i32) -> String as KnownFnPointer>::DynFnMut
    /// #     ,
    ///     dyn FnMut(i32) -> String
    /// # >::Yes;
    ///
    /// # SameType::<
    ///     <fn(i32, bool) -> String as KnownFnPointer>::DynFnMut
    /// #     ,
    ///     dyn FnMut(i32, bool) -> String
    /// # >::Yes;
    /// ```
    type DynFnMut: ?Sized;

    /// The corresponding `dyn DynFn` type.
    /// For example, the following types in each pair are equivalent.
    ///
    /// ```
    /// # trait TupleSameType {} impl<T: ?Sized> TupleSameType for (*const T, *const T) {}
    /// # enum SameType<T1: ?Sized, T2: ?Sized> where (*const T1, *const T2): TupleSameType { Yes, T1(*const T1), T2(*const T2) }
    /// # use tuple_fn::KnownFnPointer;
    /// # SameType::<
    ///     <fn() -> String as KnownFnPointer>::DynFn
    /// #     ,
    ///     dyn Fn() -> String
    /// # >::Yes;
    ///
    /// # SameType::<
    ///     <fn(i32) -> String as KnownFnPointer>::DynFn
    /// #     ,
    ///     dyn Fn(i32) -> String
    /// # >::Yes;
    ///
    /// # SameType::<
    ///     <fn(i32, bool) -> String as KnownFnPointer>::DynFn
    /// #     ,
    ///     dyn Fn(i32, bool) -> String
    /// # >::Yes;
    /// ```
    type DynFn: ?Sized;
}

pub trait KnownTuple<'a> {
    /// The corresponding tuple type which references each item.
    ///
    /// ```
    /// use tuple_fn::KnownTuple;
    ///
    /// let _: <() as KnownTuple>::RefTuple = ();
    /// let _: <(i32,) as KnownTuple>::RefTuple = (&1,);
    /// let _: <(i32, bool) as KnownTuple>::RefTuple = (&1, &true);
    /// let _: <(i32, bool, &u8) as KnownTuple>::RefTuple = (&1, &true, &&0u8);
    /// ```
    type RefTuple: 'a + KnownTuple<'a>;

    /// The `fn` pointer type which accepts this tuple as arguments and returns `()`.
    /// For example, the following types in each pair are equivalent.
    ///
    /// ```
    /// # trait TupleSameType {} impl<T> TupleSameType for (T, T) {}
    /// # enum SameType<T1, T2> where (T1, T2): TupleSameType { Yes, T1(T1), T2(T2) }
    /// # use tuple_fn::KnownTuple;
    /// # SameType::<
    /// <() as KnownTuple>::FnPointer, fn()
    /// # >::Yes;
    /// # SameType::<
    /// <(i32,) as KnownTuple>::FnPointer, fn(i32)
    /// # >::Yes;
    /// # SameType::<
    /// <(i32, bool) as KnownTuple>::FnPointer, fn(i32, bool)
    /// # >::Yes;
    /// ```
    type FnPointer: KnownFnPointer<ArgsTuple = Self>;
}

/// Enables the types which implements [`FnOnce`] to be called with arguments tuple.
///
/// ```
/// use tuple_fn::TupleFnOnce;
///
/// let start = "hello".to_string();
///
/// let closure = move |s1, s2| {
///     let mut start = start;
///     start.push_str(" ");
///     start.push_str(s1);
///     start.push_str(" ");
///     start.push_str(s2);
///     start
/// };
///
/// let result = closure.call_once_with_args_tuple(("world", "!"));
///
/// assert_eq!(result, "hello world !");
/// ```
pub trait TupleFnOnce<Args> {
    type TupleFnOutput;

    fn call_once_with_args_tuple(self, args: Args) -> Self::TupleFnOutput;
}

/// Enables the types which implements [`FnMut`] to be called with arguments tuple.
///
/// ```
/// use tuple_fn::TupleFnMut;
///
/// let mut result = vec![1, 2];
///
/// let mut closure = |value, prepend| {
///     if prepend {
///         result.insert(0, value);
///     } else {
///         result.push(value);
///     }
/// };
///
/// closure(0, true);
/// closure(3, false);
///
/// assert_eq!(result, [0, 1, 2, 3]);
/// ```
pub trait TupleFnMut<Args>: TupleFnOnce<Args> {
    fn call_mut_with_args_tuple(&mut self, args: Args) -> Self::TupleFnOutput;
}

/// Enables the types which implements [`Fn`] to be called with arguments tuple.
///
/// ```
/// use tuple_fn::TupleFn;
///
/// let start = "hello".to_string();
///
/// let closure = move |s1, s2| {
///     format!("{} {} {}", start, s1, s2)
/// };
///
/// let result = closure.call_with_args_tuple(("world", "!"));
///
/// assert_eq!(result, "hello world !");
///
/// let result = closure.call_with_args_tuple(("to", "everyone!"));
///
/// assert_eq!(result, "hello to everyone!");
/// ```
pub trait TupleFn<Args>: TupleFnMut<Args> {
    fn call_with_args_tuple(&self, args: Args) -> Self::TupleFnOutput;
}

macro_rules! impl_for_tuples {
    ($( ( $($t:ident,)* ) )+) => {
        $(
            impl<R, $($t,)*> KnownFnPointer for fn($($t,)*) -> R {
                type ArgsTuple = ($($t,)*);

                type FnPointerWithRefArgs = fn($(&$t,)*) -> R;

                type DynFnOnce = dyn FnOnce($($t,)*) -> R;
                type DynFnMut = dyn FnMut($($t,)*) -> R;
                type DynFn = dyn Fn($($t,)*) -> R;
            }

            impl<'a, $($t: 'a,)*> KnownTuple<'a> for ($($t,)*) {
                type RefTuple = ($(&'a $t,)*);
                type FnPointer = fn($($t,)*);
            }

            impl<R, T: FnOnce( $($t,)* ) -> R, $($t,)*> TupleFnOnce<($($t,)*)> for T {
                type TupleFnOutput = R;

                fn call_once_with_args_tuple(self, #[allow(non_snake_case)] ($($t,)*): ($($t,)*)) -> Self::TupleFnOutput {
                    self($($t,)*)
                }
            }

            impl<R, T: FnMut( $($t,)* ) -> R, $($t,)*> TupleFnMut<($($t,)*)> for T {
                fn call_mut_with_args_tuple(&mut self, #[allow(non_snake_case)] ($($t,)*): ($($t,)*)) -> R {
                    self($($t,)*)
                }
            }

            impl<R, T: Fn( $($t,)* ) -> R, $($t,)*> TupleFn<($($t,)*)> for T {
                fn call_with_args_tuple(&self, #[allow(non_snake_case)] ($($t,)*): ($($t,)*)) -> R {
                    self($($t,)*)
                }
            }
        )+
    };
}

impl_for_tuples! {
    ()
    (A1,)
    (A1,A2,)
    (A1,A2,A3,)
    (A1,A2,A3,A4,)
    (A1,A2,A3,A4,A5,)
    (A1,A2,A3,A4,A5,A6,)
    (A1,A2,A3,A4,A5,A6,A7,)
    (A1,A2,A3,A4,A5,A6,A7,A8,)
    (A1,A2,A3,A4,A5,A6,A7,A8,A9,)
    (A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,)
    (A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,)
    (A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,)
    (A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,)
    (A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,)
    (A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        fn call_fn_once<F: TupleFnOnce<Args>, Args>(func: F, args: Args) -> F::TupleFnOutput {
            func.call_once_with_args_tuple(args)
        }

        assert_eq!(call_fn_once(|| 1, ()), 1);
        assert_eq!(call_fn_once(|v| v, (2,)), 2);
        assert_eq!(call_fn_once(|a, b| a + b, (3, 4)), 7);
        assert_eq!(call_fn_once(|a, b, c| (a + b) > c, (5, 6, 8)), true);
        assert_eq!(
            call_fn_once(|a, b, c, d| (a + b) > (c + d), (1, 2, 3, 4)),
            false
        );

        struct Four;

        impl std::fmt::Display for Four {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "4")
            }
        }

        assert_eq!(
            call_fn_once(
                |a, b, c, d, e| format!("{}-{}-{}-{}-{}", a, b, c, d, e),
                ("1", 2, 3u8, Four, "5".to_string())
            ),
            "1-2-3-4-5"
        );

        assert_eq!(
            call_fn_once(
                |a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15| format!(
                    "{}-{}-{}-{}-{}-{}-{}-{}-{}-{}-{}-{}-{}-{}-{}",
                    a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15
                ),
                (
                    "1",
                    2,
                    3u8,
                    Four,
                    "5".to_string(),
                    std::borrow::Cow::Borrowed("6"),
                    7u32,
                    8,
                    7,
                    6,
                    5,
                    4,
                    3,
                    2,
                    1,
                )
            ),
            "1-2-3-4-5-6-7-8-7-6-5-4-3-2-1"
        );

        assert_eq!(
            (call_fn_once::<_, (&str,)>).call_with_args_tuple((|v| v, ("hello",))),
            "hello"
        );
        assert_eq!(
            call_fn_once.call_with_args_tuple((|v| v, ("world",))),
            "world"
        );
    }
}
