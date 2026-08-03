# Two new Phoebe examples: Feldhofer and Hash-Lock

Two RFID privacy protocols from the unlinkability literature, added as Phoebe
case studies:

* **Feldhofer** — symmetric-key mutual authentication, analysed for
  unlinkability by Hirschi, Baelde & Delaune (JCS 2019) and Baelde, Delaune &
  Moreau (CSF 2020); concluded **unlinkable**.
* **Hash-Lock** — randomized, reader-nonce hash authentication, one of the RFID
  case studies proved **unlinkable** by Hirschi, Baelde & Delaune.

The stateful / XOR-based protocols from those papers (OSK, the original LAK)
are out of scope: Phoebe uses a fixed equational theory (pairing, hash,
symmetric/asymmetric encryption, MAC) and does not model persistent mutable
state across sessions, which those attacks rely on.

Each protocol's message-flow layer (`roles` + `actions`) is produced by the
Alice-and-Bob parser (`AnB.hs`) from `examples/*.anb`; `AnBTest` checks the
generated `[Action]` equals the hand-written module (all 5 protocols pass). The
per-agent construction and the reader lookup formula are hand-written, following
the `TagReader0.hs` / `BasicHash.hs` templates.

## Feldhofer

```
R -> T : nR
T -> R : {| <nR, nT> |}_k
R -> T : {| <nT, nR> |}_k
```

`k` is shared between tag and reader. The nonce echoes (mutual authentication)
are enforced by Phoebe's matching-receive semantics, so no explicit equality
post-conditions are needed. Files: `examples/Feldhofer.anb`, `Feldhofer.hs`.

Model: 2 tag names (each with its own key), a single reader session; the
Dolev-Yao intruder supplies challenges. Run via `./phoebe F1..F4`.

| check (via `phoebe`) | property | result | time |
|---|---|---|---|
| `F1` | strong unlinkability by name | `Nothing` — **unlinkable** | ~90 s |
| `F2` | strong unlinkability by key  | `Nothing` — **unlinkable** | ~90 s |
| `F3` | weak unlinkability by name   | `Nothing` — **unlinkable** | ~10 s |
| `F4` | weak unlinkability by key    | `Nothing` — **unlinkable** | ~10 s |

Non-vacuity: 4652 traces with two completed tag sessions exist, so the
`Nothing` results are genuine unlinkability, not empty checks.

## Hash-Lock

```
R -> T : nR
T -> R : <nT, h(<nR, nT, k>)>
```

`k` is the tag's secret (shared with the reader's database). The reader
identifies the tag with a lookup post-condition `phi` (as in Basic-Hash). Files:
`examples/HashLock.anb`, `HashLock.hs`. Run via `./phoebe H1..H2`.

As for Basic-Hash, **weak unlinkability holds**, while the *plausibilistic*
strong notion fails by a pigeonhole argument once the intruder sees more tag
sessions than there are tag names:

| check | setting | property | result | time |
|---|---|---|---|---|
| `H2` | 2 names, 3 sessions | weak unlinkability   | `Nothing` — **unlinkable** | ~4 s |
| `H1` | 2 names, 3 sessions | strong unlinkability | **attack** (pigeonhole) | <1 s |
| —    | 2 names, 2 sessions | strong unlinkability | `Nothing` — holds | <1 s |

The last row is a control confirming the strong-unlinkability failure is a
genuine sessions-vs-names pigeonhole effect (holds at 2/2, fails at 3/2),
exactly mirroring the Basic-Hash behaviour reported in the paper.

## Reproducing

```sh
export LANG=C.UTF-8 LC_ALL=C.UTF-8
ghc -O2 Main.hs -o phoebe
./phoebe F3     # Feldhofer weak unlinkability  -> Nothing
./phoebe H1     # Hash-Lock strong unlinkability -> attack trace
./phoebe H2     # Hash-Lock weak unlinkability   -> Nothing
```
