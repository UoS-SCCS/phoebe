# Phoebe

Phoebe is an **epistemic model checker for privacy properties in security
protocols**. It expresses privacy requirements (anonymity, unlinkability,
unobservability, privacy of list membership, strong secrecy) in an epistemic
"privacy logic" and verifies them against a Dolev-Yao protocol model, for a
bounded number of sessions.

Phoebe was introduced in *"Epistemic Model Checking for Privacy"* (IEEE CSF
2024). This README describes the tool as it stands now, including the
Alice-and-Bob front-end, the newer case studies (Feldhofer, Hash-Lock, 5G AKMA,
Schnorr identification, DAA signing), zero-knowledge proofs, and the
experimental work towards a lazy Dolev-Yao engine.

## Contents

- [Repository layout](#repository-layout)
- [Features](#features)
- [What is new](#what-is-new)
- [Installation](#installation)
- [Usage](#usage)
- [Examples](#examples)
- [Alice-and-Bob front-end](#alice-and-bob-front-end)
- [Experimental: towards a lazy Dolev-Yao theory](#experimental-towards-a-lazy-dolev-yao-theory)
- [Zero-knowledge proofs, AKMA, and a faster knowledge operator](#zero-knowledge-proofs-akma-and-a-faster-knowledge-operator)
- [Limitations and roadmap](#limitations-and-roadmap)
- [Reference](#reference)

## Repository layout

```
Main.hs              command-line entry point: one option per check
Makefile             make | make test | make tools | make reproduce | make clean
reproduce.sh         runs every check and option into results/
src/                 the tool itself
  LogicSyntax.hs       terms, statements of zero-knowledge proofs, formulas of the logic
  ProtModel.hs         protocol semantics, indistinguishability, model checking
  HelperFunctions.hs   closures and list utilities
  Checks.hs            check framework, bucketed knowledge oracle, sanity tests
  AnB.hs               Alice-and-Bob front-end (parser, translator, code generator)
  LazyIntruder.hs      goal-directed Dolev-Yao deduction (reference for testing)
  LazyCheck.hs         knowledge evaluated over equivalence classes (experimental)
examples/            every case study: the Haskell model and, where there is one, its .anb spec
  PrivAuth  BasicHash  TagReader0  LoRaWANJoin          (CSF 2024)
  Feldhofer  HashLock                                   (RFID unlinkability)
  AKMA  AKMAChecks                                      (5G AKMA key identifiers)
  Schnorr  DAA                                          (zero-knowledge proofs)
tests/               AnBTest.hs, LazyIntruderTest.hs, LazyEpi.hs (benchmark)
tools/               AnBGen.hs (prints the Haskell generated from a .anb file), mktables.py
reference-results/   outputs and times of a complete run, for comparison
docs/                attack-traces.pdf
legacy/              modules that are no longer part of the build
```

All modules keep their flat names; GHC finds them through `-isrc -iexamples`,
which the `Makefile` passes. Run everything from the repository root.

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

- **An Alice-and-Bob front-end** (`src/AnB.hs`) that compiles a compact textual
  protocol notation into Phoebe's `roles` and `actions`, verified to reproduce
  the hand-written models exactly across five protocols. See
  [Alice-and-Bob front-end](#alice-and-bob-front-end).
- **Two new benchmark protocols**, Feldhofer and Hash-Lock, both concluded
  unlinkable in the literature. See [Examples](#examples).
- **A 5G AKMA privacy case study** (`examples/AKMA.hs`) reproducing the unlinkability
  failure of the AKMA procedure and its repair in AKMA^p, following Boureanu et
  al. (EuroS&P 2025). See [AKMA](#akma-5g-privacy-case-study-new).
- **A soundness fix** to symmetric decryption in the knowledge-set analysis
  (`LogicSyntax.analz`), so that the attacker only decrypts ciphertexts whose key
  it actually holds. See [Soundness fix](#soundness-fix-keyless-symmetric-decryption).
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
$ ghci -isrc -iexamples
> :l examples/PrivAuth.hs
> sat privAuthX (Neg goal3)
  Just [1.(a,A,1,{kb})!: (n1){⟨a,n1⟩}_b
  ,1.(a,C,1,{kb})?: (b,n2,a){⟨b,n2⟩}_a
  ,2.(a,C,1,{kb})!: (n3){⟨a,n2,n3⟩}_b
  ]
```

Basic Hash:

```
> :l examples/BasicHash.hs
> satNegStrongUnlinkabilityBH
  Just [1.(t1,T,1,{})!: (n1)⟨n1,hash(⟨n1,k1⟩)⟩
  ,1.(t1,T,2,{})!: (n2)⟨n2,hash(⟨n2,k1⟩)⟩
  ,1.(t1,T,3,{})!: (n3)⟨n3,hash(⟨n3,k1⟩)⟩
  ]
```

Tag-Reader:

```
> :l examples/TagReader0.hs
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
make                 # same as: ghc -O2 -isrc -iexamples -outputdir build Main.hs -o phoebe
time ./phoebe F3     # Feldhofer, weak unlinkability
```

The available argument labels are listed in `Main.hs` (for example the
`F1..F4` and `H1..H2` labels for the new examples below).

## Examples

Phoebe ships with the following case studies.

- **Private Authentication** (Abadi) : `examples/PrivAuth.hs`
- **Basic Hash** : `examples/BasicHash.hs`
- **Tag-Reader** (Example 17 in Hirschi et al.) : `examples/TagReader0.hs`
- **LoRaWAN Join v1.1** : `examples/LoRaWANJoin.hs`
- **Feldhofer** (new) : `examples/Feldhofer.hs`, `examples/Feldhofer.anb`
- **Hash-Lock** (new) : `examples/HashLock.hs`, `examples/HashLock.anb`
- **AKMA / AKMA^p** (new, 5G privacy) : `examples/AKMA.hs`

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

### AKMA (5G privacy case study, new)

`examples/AKMA.hs` models the Ua*-phase of the 5G **AKMA** delegated-authentication
procedure and checks the privacy notion **"Unlinkability of UE-AKIDs and AFs"**
(Definition 4 of Boureanu, Wesemeyer, Rajaona, Schneider and Treharne,
*A Systematic Study of Practical & Formal Privacy in the 5G AKMA Procedure*,
IEEE EuroS&P 2025). The single Ua* observable is AKMA step 1:

```
UE -> AF : AKID , AF_ID          (Application Session Establishment Request)
```

Two entities are kept (the trusted core and the secure core<->AF channels are
abstracted away, matching threat-model item T10 of the paper): the **UE**
(role `T`, named `Tag i`) identified over Ua* by its **AKID**, and the honest
**AF** (role `R`, named `Reader i`), identified by its **AF_ID**.

The crux the paper identifies is that in standard AKMA the **AKID is global**:
one AKID identifies a UE to *all* AFs (Note 1 in the paper). A UE that issues
several AKMA requests therefore presents the *same* AKID each time, and the
Dolev-Yao attacker can link those requests -- tracking the UE, including across
different AFs. This is structurally the Basic-Hash unlinkability failure (a fixed
identifier reused across sessions), so the model reuses Phoebe's Basic-Hash-style
unlinkability formulae with the AKID (slot `AbsKey KT`) as the UE identity.

Three AKID-derivation strategies are compared (all in one small model: two UEs,
two AFs, three requests):

| model | AKID derivation | strong unlinkability | run |
|---|---|---|---|
| AKMA        | global (one AKID per UE, all AFs)        | **attack** (`Just`) | `./phoebe AK1` |
| AKMA (per-AF only) | per `(UE, AF_ID)`, fixed per registration | **attack** (`Just`) | `./phoebe AKA` |
| AKMA^p      | per `AF_ID` **and** regenerated per registration | **holds** (`Nothing`) | `./phoebe AKP1` |

The attacker's knowledge is proved by a pigeonhole argument over the attacker's
indistinguishability classes: with three requests but at most two AKID values,
the attacker knows (in every indistinguishable world) that two requests share an
AKID, i.e. a UE is provably re-used. `./phoebe AKX` returns a witness that makes
the "to AFs" direction explicit -- one AKID re-appearing at two different AFs:

```
1.(t1,T,1,[k1,t1])!: ()<k1,r1>     -- UE t1, AKID k1, to AF r1
1.(t1,T,2,[k1,t1])!: ()<k1,r1>     -- UE t1, AKID k1, to AF r1
1.(t1,T,3,[k1,t1])!: ()<k1,r2>     -- UE t1, AKID k1, to AF r2   <- same AKID, different AF
```

The **per-AF-only** ablation (`AKA`) shows that deriving the AKID per AF_ID is
*not by itself* enough: a UE that re-contacts the *same* AF reuses its per-AF
AKID and stays linkable there. The repair that makes the property hold
(`AKMA^p`, row 3) is the paper's counteraction (i): the AKID is derived per
AF_ID **and** regenerated per registration, so no AKID is ever reused. This
matches the paper's result that AKMA fails and AKMA^p holds for this notion
(their Tables 2 and 3).

The **weak** notion (linking two *named* requests, `./phoebe AK2` / `AKP2`)
returns `Nothing` for *both* models: the attacker knows a collision *exists* but
cannot pin *which two* requests it is -- exactly the strong-fails / weak-holds
pattern already seen for Basic-Hash and Hash-Lock. Because the weak check yields
`Nothing` for the vulnerable model too, it carries no privacy signal that
separates AKMA from AKMA^p; **the discriminating result is the strong check
(AK1 vs AKP1)**. (The weak formula binds the two requests `x, y` outside the
`K`, so inside the attacker's indistinguishability class those specific requests
need not be alive; the strong formula re-quantifies `forAllHonest` inside `K`,
which is what makes it discriminate.)

```
| check | model  | property                    | result             | time |
|-------|--------|-----------------------------|--------------------|------|
| AK1   | AKMA   | strong unlink. of UE-AKIDs  | attack   (Just)    | <1 s |
| AKX   | AKMA   | strong unlink., cross-AF    | attack   (Just)    | <1 s |
| AKA   | AKMA   | strong unlink. (per-AF only)| attack   (Just)    | <1 s |
| AKP1  | AKMA^p | strong unlink. of UE-AKIDs  | holds    (Nothing) | <1 s |
| AK2   | AKMA   | weak   unlink. of UE-AKIDs  | holds    (Nothing) | <1 s |
| AKP2  | AKMA^p | weak   unlink. of UE-AKIDs  | holds    (Nothing) | <1 s |
```

Non-vacuity: `./phoebe AKNV` (and `AKPNV`) report 64 traces each in which three
AKMA requests complete, so the `Nothing` verdicts are genuine, not empty checks.

**Update (corrected core).** The table above was obtained when the tool treated
every key as opaque. With the correction that a long-term key is readable by an
agent that holds it (CSF'24, Defs. 15 and 20; see "Corrections to the core"
below), `AK2` now returns an attack: the attacker sees the AKID in clear, so it
*can* pin two requests that carry it (`<k1,r1>` and `<k1,r2>`). `AKP2` still
returns `Nothing`. The weak notion therefore does separate AKMA from AKMA^p. All
other AKMA options give the same output as before. `examples/AKMAChecks.hs` restates the
study in the check framework (`AKG1`..`AKF4`), with a genuinely fresh AKID for
AKMA^p and a direct two-request formulation.

This case study relies on the soundness fix below: without it the attacker would
"decrypt" an encrypted (secure-channel) request without holding the key, which
would corrupt any AKMA model that used symmetric encryption for a secure Ua*.

### Soundness fix: keyless symmetric decryption

`LogicSyntax.analz` (the attacker's knowledge-set analysis) had

```haskell
sdec xs = [x | SCrypt k x <- xs, k <- xs]   -- BUG: second generator shadows the key k
```

The generator `k <- xs` shadows the pattern-bound key, so the attacker decrypted
*every* symmetric ciphertext regardless of whether it held the key (probe:
`analz Spy [{|n9|}_k5]` returned `n9`). The frame-level `analzP` already checked
the key correctly; only this knowledge-set rule was over-strong. It is now

```haskell
sdec xs = [x | SCrypt k x <- xs, k `elem` xs]  -- decrypt only with a held key
```

Re-running the whole suite after the fix leaves every previously reported verdict
unchanged (Basic-Hash, Tag-Reader, Feldhofer, Hash-Lock, Private Authentication),
consistent with the earlier finding that the 16 lazy-intruder disagreements were
all Phoebe over-deriving via keyless decryption, never the reverse.

### Reproducing the new examples

```sh
export LANG=C.UTF-8 LC_ALL=C.UTF-8
make
./phoebe F3     # Feldhofer weak unlinkability   -> Nothing
./phoebe H1     # Hash-Lock strong unlinkability -> attack trace
./phoebe H2     # Hash-Lock weak unlinkability   -> Nothing
./phoebe AK1    # AKMA   strong unlinkability of UE-AKIDs -> attack trace
./phoebe AKX    # AKMA   cross-AF attack witness          -> attack trace
./phoebe AKP1   # AKMA^p strong unlinkability of UE-AKIDs -> Nothing
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
| `src/AnB.hs`        | parser, translator (`translate`), Haskell codegen (`genHs`) |
| `tools/AnBGen.hs`     | CLI: `anbgen file.anb` prints the generated Haskell         |
| `tests/AnBTest.hs`    | round-trip check against the hand-written modules           |
| `examples/*.anb`| specs for BasicHash, TagReader0, PrivAuth, Feldhofer, HashLock, Schnorr, DAA |

### Building and running

```sh
# codegen CLI
make tools
./anbgen examples/PrivAuth.anb

# round-trip verification (and the deduction test)
make test
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

1. **Lazy epistemics over equivalence classes** (`src/LazyCheck.hs`, benchmark
   `tests/LazyEpi.hs`). Evaluates the knowledge operator over precomputed
   indistinguishability classes (wrapping the previously dormant `satK` /
   `allSatK`). On Hash-Lock it returns the **same** satisfying-set as the
   reference `truth` while being about **186x faster** on strong unlinkability
   (46.6 s to 0.25 s) and about 20x on weak (4.3 s to 0.22 s). Set-equality also
   certifies that `equiv` behaved as a sound equivalence on these models. The
   speedup applies to `K obs ...`-shaped properties (intruder-centric
   unlinkability); other shapes fall back to `truth` per class and stay correct.
2. **OFMC-style lazy DY reducer** (`src/LazyIntruder.hs`, test
   `tests/LazyIntruderTest.hs`). Decides ground intruder derivability by analysis and
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

`src/LazyCheck.hs`, `tests/LazyEpi.hs`, `src/LazyIntruder.hs`, `tests/LazyIntruderTest.hs`.

### Still open

- Prove or assert that `equiv` is transitive before relying on the class engine
  in general.
- Re-run the suite after fixing the `analz` `sdec` rule, to confirm that no
  reported verdict depended on the over-approximation.
- Lazy-intruder termination relies on Phoebe's well-typedness bounding sorts.

## Zero-knowledge proofs, AKMA, and a faster knowledge operator

This section documents the extension described in the two technical notes
(`zk_theory.pdf`, `zk_implementation.pdf`).

### Proof terms

`src/LogicSyntax.hs` has three new term constructors and a small statement language:

```haskell
Nym  :: Terms a -> Terms a -> Terms a               -- nym(base, secret): one-way pseudonym
Sign :: Terms a -> Terms a -> Terms a               -- sig_a(m), with message recovery
Zk   :: ZkStmt -> [Terms a] -> [Terms a] -> Terms a -- zk_S(hidden ; public)

data ZkT    = ZW Int | ZP Int | ZHash ZkT | ZNym ZkT ZkT | ZSign ZkT ZkT | ZPair ZkT ZkT
data ZkStmt = ZkStmt { zkName :: String, zkEqs :: [(ZkT, ZkT)] }

dl  = ZkStmt "DL"  [ (ZP 0, ZHash (ZW 0)) ]
daa = ZkStmt "DAA" [ (ZW 1, ZSign (ZP 2) (ZW 0)), (ZP 1, ZNym (ZP 0) (ZW 0)) ]
```

A proof yields its public components (`analz`, `analzP`); its hidden components
are linked only by an agent that holds all of them; a pseudonym is opened only
by an agent that holds base and secret. `Verifies u tau` is a new formula: the
frame of `u` links `tau` to a proof that satisfies its statement. A verifier is
a receive action with `Verifies` as post-test.

### Checks

`src/Checks.hs` defines a check (model, property stated positively, state selector,
expected outcome) and three sanity tests. Every check has an identifier, which
is also a command-line option:

| option | what |
|---|---|
| `schnorr` / `S1`..`S25` | Schnorr identification (`examples/Schnorr.hs`), six models |
| `daa` / `D1`..`D21` | DAA signing (`examples/DAA.hs`), seven models |
| `akma` / `AKG1`..`AKF4` | AKMA key identifiers in the check framework (`examples/AKMAChecks.hs`), three derivations |
| `AK1 AK2 AKP1 AKP2 AKA AKX AKNV AKPNV` | AKMA, original module (`examples/AKMA.hs`) |
| `sanity` | sanity tests on all models |
| `list` | all check identifiers |
| `pairwise <id>` | the check with the pairwise knowledge oracle |
| `H1+ H2+ F1+ F2+` | earlier options with the bucketed oracle (same output) |

A check prints `HOLDS` or `FAILS` (with the first violating state), whether
this is the expected outcome, and the number of states and of selected states.
Checks whose expected outcome is `FAILS` are negative controls or known attacks.

### Knowledge oracle

`truth` is now `truthWith (pairwiseOracle model)`. `Checks.bucketOracle` first
groups states by everything `equiv` compares for plain equality and runs
`equiv` inside one group only; it returns the same set as the pairwise scan.

### Corrections to the core

1. `analz`: symmetric decryption requires the key to be in the knowledge set.
2. `sees`: the intruder keeps the values it generates for an injection (CSF'24, Def. 11, item 17).
3. `undeciph'`: a long-term key is opaque only to agents that do not hold it (Defs. 15 and 20).
4. `enabledESend`: several fresh values of one step receive distinct numbers.
5. `truth'`: quantifiers may occur under `K (UVarAg x)`.

6. Weak unlinkability formulas (`BasicHash`, `TagReader0`, `Feldhofer`, `HashLock`): the
   conjunct `nEqI (UVarAg "x") (UVarAg "x")` (x differs from x, always false) now reads
   `nEqI (UVarAg "x") (UVarAg "y")`, as in `examples/AKMA.hs`.

The outcome of all 18 original options is unchanged; for `H1` the attack trace
is shorter. This includes the six "weak" options (`2`, `C`, `D`, `F3`, `F4`,
`H2`): with the intended inequality they still return `Nothing`. The weak
notion binds the two agents outside `K`, so it fails only when the attacker can
also tell who the two agents are (as in `AK2` / `AKG4`); where agents stay
anonymous it holds even if sessions are linked (`S25` against `S19`).

### Alice-and-Bob notation

`src/AnB.hs` accepts statement declarations (`statement DL : P0 = hash(W0)`), proof
terms `zk_DL(hidden | public)`, `nym(base, secret)`, `sig(signer, message)` and
the annotation `recv_as <message>` for the receiver's parse. See
`examples/Schnorr.anb` and `examples/DAA.anb`; `AnBTest` checks that they
generate the actions of `examples/Schnorr.hs` and `examples/DAA.hs`.

### Reproducing everything

```
make reproduce                  # builds, runs all checks, options and comparisons into results/
python3 tools/mktables.py       # summary of results/ (add reference-results to summarise the reference run)
```

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
  example such as `examples/TagReader0.hs` or `examples/BasicHash.hs`. *(Planned: automate agent
  construction, which is regular for RFID-style protocols.)*
- Scalability: the current model checking is eager. The experimental section
  above tracks the move to a lazy engine.

## Reference

F. Rajaona, I. Boureanu, R. Ramanujam, S. Wesemeyer.
*Epistemic Model Checking for Privacy.*
IEEE Computer Security Foundations Symposium (CSF), 2024.
