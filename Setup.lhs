#! /usr/bin/env runhaskell

> import Distribution.Simple
> import Distribution.Simple.UUAGC (uuagcLibUserHook)
> import UU.UUAGC (uuagc)

> main = defaultMainWithHooks (uuagcLibUserHook uuagc)
