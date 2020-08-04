# Idris2 Extras

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

Parts of this library are derived from the Idris 2 standard library, whose
[license may be found here.](https://github.com/idris-lang/Idris2/blob/master/LICENSE)

## Goal

The goal of this library is to become obsolete. Currently, Idris 2 is still in
its infancy, so I frequently find things I wished the standard library had.
This library fills some of those gaps.

## Contents

 * `Extras.Prelude` has some basic things like `zip` for streams
 * `Extras.Control.MonadTrans` has `ReaderT`, `ExceptT`, and `ContT`
 * `Extras.Data.DepMap` has a version of `Data.SortedMap` where the values can
   depend on the keys.
 * `Extras.Language.Derive` has utilities to derive `Eq` and `DecEq` interfaces.
   They're not super robust, but they work for most simple types.  See
   `tests/derive.idr` and `tests/derive_fail.idr` for what works and what
   doesn't.

## TODO

 * Better `deriveDecEq` that doesn't rely on `Uninhabited (a = b)` for distinct
   constructors `A`, `B`
