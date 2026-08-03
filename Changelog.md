# Rtowards a lazy Dolev-Yao theory for privacy


Ideas based on:
--   OFMC (Basin-Mödersheim-Viganò, lazy intruder),
 -- AAMAS'16 (Cimatti-Gario-Tonetta, lazy temporal-epistemic), 
-- arXiv:2207.09895 (parallel Haskell OFMC).

## Eager bottlenecks identified (with code refs)
1. `build prot` materialises ALL traces + O(n²) `nub` up front.
2. `truth`'s `K` case rescans the whole model and recomputes `equiv`/`frame`/`terms`
   (analz closures) for every state — O(|W|²·analz).
3. Receives (`enabledERec`) enumerate ALL well-typed intruder messages
   (`buildSigmas`/`possSigmaImages`) — the thing OFMC's lazy intruder removes.
4. **Finding:** `LogicSyntax.analz` `sdec = [x | SCrypt k x <- xs, k<-xs]` shadows
   `k`, so the intruder's knowledge-set decrypts EVERY symmetric ciphertext
   regardless of key possession (probe: `analz Spy [{|n9|}_k5] ⊇ {n9}`). Frame-level
   `analzP` is correct; the knowledge-set `analz` (used for `terms`/spyTerms) is
   over-strong → risks false attacks. Needs fixing + re-run.

## Two verified prototypes built
1. **Lazy epistemics over equivalence classes** (`LazyCheck.hs`, benchmark
   `LazyEpi.hs`). Wraps the dormant `satK`/`allSatK`. On Hash-Lock it gives the
   SAME satisfying-set as reference `truth` while being ≈**186× faster** on strong
   unlinkability (46.6s→0.25s) and ≈20× on weak (4.3s→0.22s). Set-equality also
   certifies `equiv` is a sound equivalence on these models. Applies to
   `K obs …`-shaped properties (intruder-centric unlinkability); other shapes fall
   back to `truth` per class (still correct).
2. **OFMC-style lazy DY reducer** (`LazyIntruder.hs`, test `LazyIntruderTest.hs`).
   Ground derivability by analysis+generation reduction, no synth closure. Agrees
   with Phoebe on 880/896 battery cases; all 16 disagreements are Phoebe
   over-deriving via keyless symmetric decryption (the §4 finding), never the
   reverse. Correct sdec requires key possession.

## Design 
- Symbolic lazy-intruder layer for `enabledERec`: lazy state `(pt, from-constraints)`,
  reduction rules G_pair/G_acrypt/G_scrypt/G_hash/G_mac/G_unif (not-when-variable)/G_var
  instantiated to Phoebe's algebra, worked Basic-Hash-receive example showing `KT`
  pinned by unification with zero enumeration.
- CGT/CEGAR lazy epistemics: witness-pair search with on-demand `equiv`, static
  learning, memoised frames.
-  plan: 
 (1) finish the two prototypes + memoise; 
  (2) fix `analz`; 
  (3) swap  symbolic intruder into `enabledERec` (regression vs `buildSigmas`); 
  (4) on-the-fly reachability; 
  (5) CEGAR epistemics + nested/quantified `K`.

## Hs files added for now
`LazyIntruder.hs`, `LazyIntruderTest.hs`, `LazyCheck.hs`, `LazyEpi.hs`,




## Still open
- Prove/assert `equiv` transitive before relying on the class engine generally.
- Re-run suite after fixing `analz` sdec to confirm no verdict depended on the
  over-approximation.
- Lazy-intruder termination rests on Phoebe's well-typedness bounding sorts.