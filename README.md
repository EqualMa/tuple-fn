# tuple-fn

[![Crates.io](https://img.shields.io/crates/v/tuple-fn?style=for-the-badge)](https://crates.io/crates/tuple-fn)
[![docs.rs](https://img.shields.io/docsrs/tuple-fn/latest?style=for-the-badge)](https://docs.rs/tuple-fn)
[![GitHub license](https://img.shields.io/github/license/EqualMa/tuple-fn?style=for-the-badge)](https://github.com/EqualMa/tuple-fn/blob/main/LICENSE)
[![GitHub stars](https://img.shields.io/github/stars/EqualMa/tuple-fn?style=for-the-badge)](https://github.com/EqualMa/tuple-fn/stargazers)

This crate provides [`TupleFnOnce`], [`TupleFnMut`] and [`TupleFn`],
corresponding to [`FnOnce`], [`FnMut`] and [`Fn`].

[`TupleFnOnce`], [`TupleFnMut`] and [`TupleFn`] enables functions or closures
to be called with a tuple of arguments.
For example:

```rust
use tuple_fn::*;

fn add(a: i32, b: i32) -> i32 {
    a + b
}

let sum = add.call_with_args_tuple((1, 2));
assert_eq!(sum, 3);
```

These three traits should be named as
`FnOnceCallWithArgsTupleExt`, `FnMutCallWithArgsTupleExt`, `FnCallWithArgsTupleExt`
by convention, because they are implemented for
all corresponding `FnOnce`, `FnMut`, `Fn` types and act like extension traits.
They are named as `TupleFn*` just for simplicity.
