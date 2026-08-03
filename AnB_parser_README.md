# Alice-and-Bob front-end for Phoebe (prototype)

This is a first go towards a compiler from compact **Alice-and-Bob
style** protocol description into the Phoebe Haskell representation, so that
protocols no longer have to be written directly with `Action`/`Terms` data
constructors.

## What it covers

Given a `.anb` spec it produces the **message-flow layer** of a protocol:

* the role list        → `roles :: [RoleName]`
* the send/receive actions → `actions :: [Action]`


## What it leaves open

Two things on protocol-specific work:

1. **Test formulae.** Enabling conditions such as the Basic-Hash lookup, the
   TagReader `match`, or PrivAuth's `beta` are full PL `Stmt`s. A spec refers to
   them *by name* (`; recv_post phi`, `; send_test phi`); the modeller supplies
   the `Stmt` — exactly as the current hand-written modules do with their local
   `where phi = ...` definitions. `translate` takes a `[(String, Stmt)]`
   environment for this.
2. **Agent construction.** Per-agent initial knowledge, frames, whitelists and
   substitutions are not yet generated

## New files

| file                     | purpose                                                   |
|--------------------------|-----------------------------------------------------------|
| `AnB.hs`                 | parser, translator (`translate`), Haskell codegen (`genHs`) |
| `AnBGen.hs`              | CLI: `anbgen file.anb` prints the generated Haskell        |
| `AnBTest.hs`             | round-trip check against the hand-written modules          |
| `examples/*.anb`         | specs for BasicHash, TagReader0, PrivAuth                  |

## Building / running

```sh
# codegen CLI
ghc AnBGen.hs -o anbgen
./anbgen examples/PrivAuth.anb

# round-trip verification
ghc AnBTest.hs -o anbtest
./anbtest
```

> Note: the tool prints Unicode; run under a UTF-8 locale
> (`export LANG=C.UTF-8 LC_ALL=C.UTF-8`).

## Verification

`AnBTest` parses each `.anb` spec, translates it (with the protocol's test
formulae supplied by name), and checks the resulting `[Action]` is **equal** to
the `actions` list copied verbatim from the corresponding Phoebe module, using
the derived `Eq` instance on `Action`. All three currently pass:

```
BasicHash  : PASS (2 actions)
TagReader0 : PASS (7 actions)   -- exercises multi-receive
PrivAuth   : PASS (6 actions)   -- exercises if/else branching + negated test
ALL ROUND-TRIP CHECKS PASSED
```

Because the comparison is on the actual `Action` values (not on text), this is a
structural guarantee that the parser reconstructs the exact protocol the modules
encode by hand.

## Example spec (PrivAuth)

```
protocol PrivAuth
roles   A C
names   B
nonces  NA NC N
keys    KK

1. A -> C : { < A, NA > }_B              ; new NA
2. C -> A : { < C, NA, NC > }_A          ; new NC ; send_test phi
 | C -> A : {| N |}_KK                    ; new N, KK
```

