# Phoebe

Phoebe is an **epistemic model checker for privacy properties in security
protocols**. It expresses privacy requirements (anonymity, unlinkability,
unobservability, privacy of list membership, strong secrecy) in an epistemic
"privacy logic" and verifies them against a Dolev-Yao protocol model, for a
bounded number of sessions.

Phoebe was introduced in *"Epistemic Model Checking for Privacy"* (IEEE CSF
2024). This README describes the tool as it stands now, including the recent
Alice-and-Bob front-end, two new benchmark protocols, and the experimental work
towards a lazy Dolev-Yao engine.

## Contents

- [Features](#features)
- [What is new](#what-is-new)
- [Installation](#installation)
- [Usage](#usage)
- [Examples](#examples)
- [Alice-and-Bob front-end](#alice-and-bob-front-end)
- [Experimental: towards a lazy Dolev-Yao theory](#experimental-towards-a-lazy-dolev-yao-theory)
- [Limitations and roadmap](#limitations-and-roadmap)
- [Reference](#reference)

## Features

- Phoebe implements a **symbolic** model of security protocols: messages are
  algebraic terms (not bitstrings) and a Dolev-Yao attacker is assumed.
- Phoebe works for protocols with a **bounded number of sessions**.
- Phoebe assumes a limited Dolev-Yao attacker: the DY attacker can only swap
  well-typed terms.
- Privacy properties are expressed in an **epistemic logic** language (PL).
- Protocols are modelled using a **send/receive** language.
- The protocol model in Phoebe is an **interpreted system**.
- The user provides:
  - the protocol description,
  - an epistemic formula expressing the desired property,
  - the domains for protocol names, and long-term keys if necessary,
  - the maximum number of sessions.

## What is new

Recent additions to the tool (all preliminary work extending the CSF 2024
release):

- **An Alice-and-Bob front-end** (`AnB.hs`) that compiles a compact textual
  protocol notation into Phoebe's `roles` and `actions`, verified to reproduce
  the hand-written models exactly across five protocols. See
  [Alice-and-Bob front-end](#alice-and-bob-front-end).
- **Two new benchmark protocols**, Feldhofer and Hash-Lock, both concluded
  unlinkable in the literature. See [Examples](#examples).
- **Experimental lazy prototypes**: an equivalence-class evaluation of the
  knowledge operator (identical verdicts, up to ~186x faster) and an OFMC-style
  lazy Dolev-Yao reducer (which also surfaced a soundness gap in the current
  deduction). See
  [Experimental: towards a lazy Dolev-Yao theory](#experimental-towards-a-lazy-dolev-yao-theory).

## Installation

You need Haskell (GHC). The original release was tested with GHC 9.2.4; the
recent additions build with GHC 9.4.x. Compatibility with other versions is
unknown.

The tool prints Unicode (for example `⟨ ⟩`, `⦃ ⦄`), so run it under a UTF-8
locale:

```sh
export LANG=C.UTF-8 LC_ALL=C.UTF-8
```

## Usage

### With GHCi

The easiest way to get results, although not the most performant. Start GHCi and
load an example module, then evaluate one of its checks.

Private Authentication:

```
$ ghci
> :l PrivAuth.hs
> sat privAuthX (Neg goal3)
  Just [1.(a,A,1,{kb})!: (n1){⟨a,n1⟩}_b
  ,1.(a,C,1,{kb})?: (b,n2,a){⟨b,n2⟩}_a
  ,2.(a,C,1,{kb})!: (n3){⟨a,n2,n3⟩}_b
  ]
```

Basic Hash:

```
> :l BasicHash.hs
> satNegStrongUnlinkabilityBH
  Just [1.(t1,T,1,{})!: (n1)⟨n1,hash(⟨n1,k1⟩)⟩
  ,1.(t1,T,2,{})!: (n2)⟨n2,hash(⟨n2,k1⟩)⟩
  ,1.(t1,T,3,{})!: (n3)⟨n3,hash(⟨n3,k1⟩)⟩
  ]
```

Tag-Reader:

```
> :l TagReader0.hs
> satKeyLinkTR
  Just [1.(t1,T,1,{})!: (n1)⦃n1⦄_k1
  ,1.(t2,T,2,{})!: (n2)⦃n2⦄_k1
  ,1.(r1,R,1,{k1,k2})?: ()⦃n1⦄_k1
  ,2.(r1,R,1,{k1,k2})!: (n3)⦃n3⦄_k1
  ,2.(t1,T,1,{})?: ()⦃n2⦄_k1
  ,2.(t2,T,2,{})?: ()⦃n1⦄_k1
  ,3.(t1,T,1,{})!: ()⦃⟨n2,n1⟩⦄_k1
  ,3.(t2,T,2,{})!: ()⦃⟨n1,n2⟩⦄_k1
  ]
```

### Compiling

This gives better performance. Compile the main module into an executable named
`phoebe`, then run it with one of the arguments defined in `Main.hs`, each
corresponding to a model-checking example.

```sh
ghc -O2 Main.hs -o phoebe
time ./phoebe F3     # Feldhofer, weak unlinkability
```

The available argument labels are listed in `Main.hs` (for example the
`F1..F4` and `H1..H2` labels for the new examples below).

## Examples

Phoebe ships with the following case studies.

- **Private Authentication** (Abadi) : `PrivAuth.hs`
- **Basic Hash** : `BasicHash.hs`
- **Tag-Reader** (Example 17 in Hirschi et al.) : `TagReader0.hs`
- **LoRaWAN Join v1.1** : `LoRaWANJoin.hs`
- **Feldhofer** (new) : `Feldhofer.hs`, `examples/Feldhofer.anb`
- **Hash-Lock** (new) : `HashLock.hs`, `examples/HashLock.anb`

### Feldhofer (new)

Symmetric-key mutual authentication for RFID. Analysed for unlinkability by
Hirschi, Baelde and Delaune (JCS 2019) and Baelde, Delaune and Moreau (CSF 2020),
and concluded **unlinkable**.

```
R -> T : nR
T -> R : {| <nR, nT> |}_k
R -> T : {| <nT, nR> |}_k
```

`k` is a symmetric key shared between the tag and the reader. The nonce echoes
(mutual authentication) are enforced by Phoebe's matching-receive semantics, so
no explicit equality post-conditions are needed. The model uses two tag names
(each with its own key) and a single reader session; the Dolev-Yao intruder
supplies the challenges. Run via `./phoebe F1..F4`.

| check | property | result | time |
|---|---|---|---|
| `F1` | strong unlinkability by name | unlinkable (`Nothing`) | ~90 s |
| `F2` | strong unlinkability by key  | unlinkable (`Nothing`) | ~90 s |
| `F3` | weak unlinkability by name   | unlinkable (`Nothing`) | ~10 s |
| `F4` | weak unlinkability by key    | unlinkable (`Nothing`) | ~10 s |

Non-vacuity: 4652 traces with two completed tag sessions exist, so the `Nothing`
results are genuine unlinkability rather than empty checks.

### Hash-Lock (new)

Randomized, reader-nonce hash authentication. One of the RFID case studies proved
**unlinkable** by Hirschi, Baelde and Delaune.

```
R -> T : nR
T -> R : <nT, h(<nR, nT, k>)>
```

`k` is the tag's secret, shared with the reader's database. The reader identifies
the tag with a lookup post-condition `phi`, as in Basic-Hash. Run via
`./phoebe H1..H2`.

As for Basic-Hash, **weak unlinkability holds**, while the *plausibilistic*
strong notion fails by a pigeonhole argument once the intruder observes more tag
sessions than there are tag names:

| check | setting | property | result | time |
|---|---|---|---|---|
| `H2` | 2 names, 3 sessions | weak unlinkability   | unlinkable (`Nothing`) | ~4 s |
| `H1` | 2 names, 3 sessions | strong unlinkability | attack (pigeonhole) | <1 s |
| (control) | 2 names, 2 sessions | strong unlinkability | holds (`Nothing`) | <1 s |

The control row confirms the strong-unlinkability failure is a genuine
sessions-versus-names pigeonhole effect (it holds at 2/2 and fails at 3/2),
mirroring the Basic-Hash behaviour reported in the paper.

The stateful / XOR-based protocols from those papers (OSK, the original LAK) are
out of scope: Phoebe uses a fixed equational theory (pairing, hash, symmetric and
asymmetric encryption, MAC) and does not model persistent mutable state across
sessions, which those attacks rely on.

### Reproducing the new examples

```sh
export LANG=C.UTF-8 LC_ALL=C.UTF-8
ghc -O2 Main.hs -o phoebe
./phoebe F3     # Feldhofer weak unlinkability   -> Nothing
./phoebe H1     # Hash-Lock strong unlinkability -> attack trace
./phoebe H2     # Hash-Lock weak unlinkability   -> Nothing
```

## Alice-and-Bob front-end

A first step towards a compiler from a compact **Alice-and-Bob style** protocol
description into Phoebe's Haskell representation, so that protocols no longer have
to be written directly with `Action` / `Terms` data constructors.

### What it covers

Given a `.anb` spec it produces the **message-flow layer** of a protocol:

- the role list, `roles :: [RoleName]`
- the send/receive actions, `actions :: [Action]`

### What it leaves open

Two pieces of protocol-specific work are not generated by the front-end:

1. **Test formulae.** Enabling conditions such as the Basic-Hash lookup, the
   Tag-Reader `match`, or PrivAuth's `beta` are full PL statements. A spec refers
   to them *by name* (`; recv_post phi`, `; send_test phi`) and the modeller
   supplies the statement, exactly as the hand-written modules do with their
   local `where phi = ...` definitions. `translate` takes a `[(String, Stmt)]`
   environment for this.
2. **Agent construction.** Per-agent initial knowledge, frames, whitelists and
   substitutions are not yet generated.

### Files

| file            | purpose                                                     |
|-----------------|-------------------------------------------------------------|
| `AnB.hs`        | parser, translator (`translate`), Haskell codegen (`genHs`) |
| `AnBGen.hs`     | CLI: `anbgen file.anb` prints the generated Haskell         |
| `AnBTest.hs`    | round-trip check against the hand-written modules           |
| `examples/*.anb`| specs for BasicHash, TagReader0, PrivAuth, Feldhofer, HashLock |

### Building and running

```sh
# codegen CLI
ghc AnBGen.hs -o anbgen
./anbgen examples/PrivAuth.anb

# round-trip verification
ghc AnBTest.hs -o anbtest
./anbtest
```

### Verification

`AnBTest` parses each `.anb` spec, translates it (with the protocol's test
formulae supplied by name), and checks that the resulting `[Action]` is **equal**
to the `actions` list copied verbatim from the corresponding Phoebe module, using
the derived `Eq` instance on `Action`. Because the comparison is on the actual
`Action` values (not on text), this is a structural guarantee that the front-end
reconstructs exactly the protocol the modules encode by hand. All five protocols
pass:

```
BasicHash  : PASS (2 actions)
TagReader0 : PASS (7 actions)   -- exercises multiple receives
PrivAuth   : PASS (6 actions)   -- exercises if/else branching + negated test
Feldhofer  : PASS (6 actions)
HashLock   : PASS (4 actions)
ALL ROUND-TRIP CHECKS PASSED
```

### Example spec (PrivAuth)

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

Encryption is sort-directed: `{ m }_X` is asymmetric when `X` is a principal and
symmetric when `X` is a key. Each line generates a send by the sender role and a
matching receive by the receiver role at the same protocol step.

## Experimental: towards a lazy Dolev-Yao theory

Work in progress on making Phoebe lazy and scalable, drawing on OFMC
(Basin, Mödersheim, Viganò; the lazy intruder), AAMAS'16 (Cimatti, Gario,
Tonetta; lazy temporal-epistemic model checking) and arXiv:2207.09895 (parallel
Haskell OFMC).

### Eager bottlenecks identified

1. `build prot` materialises **all** traces up front, with an O(n^2) `nub`.
2. `truth`'s `K` case rescans the whole model and recomputes `equiv` / `frame` /
   `terms` (analysis closures) for every state, i.e. O(|W|^2 . analz).
3. Receives (`enabledERec`) enumerate **all** well-typed intruder messages
   (`buildSigmas` / `possSigmaImages`), which is what OFMC's lazy intruder
   removes.
4. **Soundness finding.** `LogicSyntax.analz` has
   `sdec = [x | SCrypt k x <- xs, k <- xs]`. The second generator `k <- xs`
   shadows the pattern-bound key `k`, so the intruder's knowledge-set analysis
   decrypts *every* symmetric ciphertext regardless of key possession (probe:
   `analz Spy [{|n9|}_k5]` contains `n9`). The frame-level `analzP` checks the key
   correctly; the knowledge-set `analz`, used for the intruder's terms, is
   over-strong and risks false attacks. This needs fixing and a re-run of the
   suite.

### Two verified prototypes

1. **Lazy epistemics over equivalence classes** (`LazyCheck.hs`, benchmark
   `LazyEpi.hs`). Evaluates the knowledge operator over precomputed
   indistinguishability classes (wrapping the previously dormant `satK` /
   `allSatK`). On Hash-Lock it returns the **same** satisfying-set as the
   reference `truth` while being about **186x faster** on strong unlinkability
   (46.6 s to 0.25 s) and about 20x on weak (4.3 s to 0.22 s). Set-equality also
   certifies that `equiv` behaved as a sound equivalence on these models. The
   speedup applies to `K obs ...`-shaped properties (intruder-centric
   unlinkability); other shapes fall back to `truth` per class and stay correct.
2. **OFMC-style lazy DY reducer** (`LazyIntruder.hs`, test
   `LazyIntruderTest.hs`). Decides ground intruder derivability by analysis and
   generation, with no synth closure. It agrees with Phoebe on 880 of 896 battery
   cases; all 16 disagreements are Phoebe over-deriving via keyless symmetric
   decryption (the finding above), never the reverse. The corrected `sdec`
   requires key possession.

### Design

- **Symbolic lazy-intruder layer** for `enabledERec`: a lazy state
  `(pt, from-constraints)`, with reduction rules
  `G_pair` / `G_acrypt` / `G_scrypt` / `G_hash` / `G_mac` / `G_unif`
  (not when the target is a variable) / `G_var`, instantiated to Phoebe's
  algebra. Worked Basic-Hash-receive example: `KT` is pinned by unification with
  zero enumeration.
- **CGT/CEGAR lazy epistemics**: witness-pair search with on-demand `equiv`,
  static learning, and memoised frames.

### Plan

1. Finish the two prototypes and add memoisation.
2. Fix `analz` (the `sdec` key-possession bug).
3. Swap the symbolic intruder into `enabledERec` (regression against
   `buildSigmas`).
4. On-the-fly reachability.
5. CEGAR epistemics with nested and quantified `K`.

### Experimental files

`LazyCheck.hs`, `LazyEpi.hs`, `LazyIntruder.hs`, `LazyIntruderTest.hs`.

### Still open

- Prove or assert that `equiv` is transitive before relying on the class engine
  in general.
- Re-run the suite after fixing the `analz` `sdec` rule, to confirm that no
  reported verdict depended on the over-approximation.
- Lazy-intruder termination relies on Phoebe's well-typedness bounding sorts.

## Limitations and roadmap

- To set the number of sessions and the domain, the user currently edits the
  relevant example file and reinterprets or recompiles. *(Planned: expose these
  as command-line arguments.)*
- Protocol descriptions and PL formulae are written with Haskell data
  constructors. The Alice-and-Bob front-end now generates the message-flow layer
  (`roles`, `actions`) from a compact notation; a surface syntax for the PL test
  formulae is still future work.
- Implementing a new example still requires hand-writing the per-agent
  construction (initial knowledge, frames, whitelists), following an existing
  example such as `TagReader0.hs` or `BasicHash.hs`. *(Planned: automate agent
  construction, which is regular for RFID-style protocols.)*
- Scalability: the current model checking is eager. The experimental section
  above tracks the move to a lazy engine.

## Reference

F. Rajaona, I. Boureanu, R. Ramanujam, S. Wesemeyer.
*Epistemic Model Checking for Privacy.*
IEEE Computer Security Foundations Symposium (CSF), 2024.
