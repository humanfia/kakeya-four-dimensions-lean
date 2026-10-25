# Problem 074: final fidelity verdict (reconciliation of the reviews)

Problem `oai_074_kakeya_four_dimensions`. Paper: OpenAI, *Every four-dimensional Kakeya set has
full Hausdorff dimension* (September 24, 2026), Theorem 1.1. Tree `g-oai-074` (ended `proved`).
Judged export E `71391e12db6f5956b54bcdb01a6b1ceeba11604d` (from X `e18a9d88…`; LOT's v10wz-inlined
export). Both checkers accepted it with nanoda forced on, and the independent recompile passed
with the three standard axioms (`FINAL-CHECK.md`).

Reconciled on 2026-10-23 from:
- `prep/074/FIDELITY.md` (phase B, 2026-10-19, written before the proof existed);
- `final/074/FIDELITY-AUDIT-1.md` (independent audit 1, Lean witnesses in `fidelity-audit-1/`);
- `final/074/FIDELITY-AUDIT-2.md` (independent audit 2, Lean witnesses in `fidelity-audit-2/`);
- `final/074/FINAL-CHECK.md` and its two run reports (`FINAL-CHECK.run1-20261022T204822Z.md`,
  `FINAL-CHECK.run2-20261023T052251Z.md`).

Wherever the reviews differ or raise a concern, I re-read the paper's TeX, the Lean text and the
tree state myself before deciding (§3). I also ran one new Lean check in docker and two read-only
scripts (§2.4, §2.5, §6).

## Verdict: **FAITHFUL**

`Challenge.lean` + `ChallengeDeps.lean` state exactly Theorem 1.1:
- K ⊂ ℝ⁴ is an arbitrary set: no measurability, compactness or boundedness;
- for every e in the Euclidean unit sphere S³ there is a point a_e with the closed unit segment
  {a_e + te : 0 ≤ t ≤ 1} inside K;
- then dim_H K = 4, with Mathlib's `dimH`, which is the paper's covering definition on all sets.

`ChallengeDeps.lean` is `import Mathlib` plus a docstring. It defines nothing. Both audits proved
in Lean (Mathlib only) that:
- the sphere is the round S³ of the ℓ² norm, not the sup-norm cube;
- `segment ℝ a (a + e)` is {a + t•e : t ∈ [0,1]}, with diameter 1 and dimension 1 for e ∈ S³;
- `μH[s]` is the paper's countable-cover formula for every set, and `dimH K = inf{s : μH[s] K = 0}`;
- the theorem stated with the paper's own definitions is equivalent to the frozen type (audit 1,
  `paper_iff_challenge`);
- the hypothesis is satisfiable (closed unit ball, `univ`), and lower-dimensional sets fail it.

No Mathlib convention makes the statement easier. There is no junk value, no measurability side
condition and no normalising constant on either side. `dimH K ≤ 4` holds for every K, so the
content is `4 ≤ dimH K` for arbitrary K: the four-dimensional Hausdorff Kakeya conjecture in full.

The accepted proof is the paper's route. The upper bound is the ambient one. The lower bound is
Theorem 2.17's reduction from an arbitrary set (outer measure, finite selection) to a discrete
statement DK4, and DK4 from §§3–10. The paper's cited inputs are proved in Lean, not assumed: the
weighted plank lemma (via our own Wang–Zahl library), Carbery–Valdimarsson, the OdSS special case,
and Wang–Zahl's planar Theorem 5.2 (via the same library).

I checked in Lean that the six declarations Root applies have exactly their frozen types,
syntactically, and that Root's type is the challenge's (§2.4). The five refuted obligations were
over-strong intermediate statements deep in the §6 machinery. None has a module in E, and nothing
in Root's import closure comes from them. The inlined WZ library (2,872 modules) is byte for byte
our own accepted WZ tree at `da2150fe`, up to the mechanical module rename (§2.5). Nothing on the
route is weakened, unproved, or exploits the formalization.

All three reviews reach "faithful" independently. They differ only on side points: one wording
point about the paper (graph BSG is proved in the paper, not cited), bookkeeping numbers, and the
tree's end time. §3 resolves each. Two new findings do not touch the verdict but matter before any
release: E's `NOTICE` has the same generator defects as 078's (D10), and the check needs 64 GiB
and up to 4.8 h (D16).

## 1. Where the reviews stand

| Question | Phase B (FIDELITY.md) | Audit 1 | Audit 2 | Conflict? |
|---|---|---|---|---|
| Q1 statement ≡ Thm 1.1 (arbitrary K, Euclidean ℝ⁴, round S³, ∀ e ∃ a, closed unit segment, covering 𝓗^s on all sets, dim_H as an infimum, value 4) | equivalent, 8-row clause table; "Mathlib omits the normalising constant"; inf form derived from two lemmas | equivalent; Lean W4 `paper_iff_challenge`: the theorem in the paper's own definitions ⇔ the frozen type | equivalent; Lean (A)–(D): `Stmt` is the frozen type, `stmt_iff`: ⇔ `4 ≤ dimH K` | none (wording only: the paper has no normalising constant either; `dimH_eq_iInf` exists at our pin; D18) |
| Q2 definitions standard / non-degenerate | standard (grep + argument); `K = univ` satisfies `hK` | Lean W1–W6: Euclidean sphere vs sup norm, segment diam 1 and dimH 1, covering formula, ball and `univ` satisfy, a point and `{x₀ = 0}` fail, countably many directions give dimH ≤ 1 | Lean (A)–(F): the same facts; `{x₃ = 0}` holds segments in a great 2-sphere of directions and has dimH 3; `¬ ∀ K, dimH K = 4` | none (different witnesses, same conclusions) |
| Q3 easier than intended? | no | no | no | none |
| Q4 route | predates the proof; checked the six preset children against the TeX | mirrors the paper; "the paper's four cited analytic inputs" include graph BSG; WZ genuine; 5 refuted, none in E | mirrors the paper; graph BSG "proved in the paper"; WZ genuine; 5 refuted, none in any closure | BSG cited or proved (D2); counts (D3, D4, D5, D9, D12); end time (D1) |
| WZ library provenance | extracted, built and accepted the package (PHASE-B B2), not a fidelity question then | 303/303 spot-checked files identical to the package | 2,872/2,872 identical; all 2,875 `WZLOT-FILES.json` entries match the WZ tree at `da2150fe` | none (D6) |
| Verdict | faithful | FAITHFUL | FAITHFUL | none |

## 2. Decisive arguments (checked again for this verdict)

### 2.1 The statement is Theorem 1.1

**Paper.** `01-introduction.tex` l. 8–16: "Let K ⊂ ℝ⁴. Suppose that for every e ∈ S³ there is a
point a_e ∈ ℝ⁴ such that {a_e + te : 0 ≤ t ≤ 1} ⊂ K. Then dim_H K = 4." Lines 17–31 add: "Neither
K nor the choice of its witnessing segments is required to be measurable", and define
𝓗^s_δ(K) = inf{Σ(diam U_i)^s : K ⊂ ⋃U_i, diam U_i ≤ δ} over countable covers,
𝓗^s = lim_{δ↓0} 𝓗^s_δ, and dim_H K = inf{s : 𝓗^s(K) = 0}. There is no normalising constant.
I read the seed's copy of the TeX (`seed/oai_074_kakeya_four_dimensions/papers/tex-*.tex`). Six of
its section files have the same sha256 as zhengyang's `source-…/build/sections/` (checked one by
one).

**Byte identity.** I re-checked these files (sha256, first 16 hex):

| File | starter | E | zhengyang's `lean-problem/` |
|---|---|---|---|
| `Challenge.lean` | `bf8e140c5a8b3516` | same | same |
| `ChallengeDeps.lean` | `c1a46df9350eee8b` | same | same |
| `Solution.lean` | `20074f660bcf05fe` | same | same |
| `config.json` | `538baf9e2f11e421` | same | same |
| `holes.json` | `f0bf46770ff6ed4d` | same | same |
| `README.md` | `e2f2bd7be2da390b` | same | same |
| `.gitignore` | `1fd00cc9adb8010f` | same | same |
| `Submission/Helpers.lean` | `b5b5c31e59632f5c` | same | same |

The build files of E equal the starter's, that is, our standard port: `lean-toolchain`
`bc84812c…`, `lakefile.toml` `e4c94454…`, `lake-manifest.json` `adb71a3b…` (phase B's expected
manifest), `WorkspaceTest.lean` `17bd1978…` (the hardened launcher), `PROBLEM.md` `484eb3a3…`.
FINAL-CHECK found the two statement files identical in the starter, E, both trusted `pristine.tar`s
and the recompile, and all 12 protected files of E equal to `protected.sha256`.

**Lean**:
`theorem kakeya_four_dimensions (K : Set (EuclideanSpace ℝ (Fin 4))) (hK : ∀ e ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, ∃ a : EuclideanSpace ℝ (Fin 4), segment ℝ a (a + e) ⊆ K) : dimH K = 4`.

- **Quantifiers.** K, then `∀ e ∈ S³`, then `∃ a`. So a depends on e with no regularity, as in the
  paper. It is neither one a for all e (stronger) nor a measurable e ↦ a.
- **Space and sphere.** `EuclideanSpace ℝ (Fin 4)` is `PiLp 2`. `pp.explicit` shows
  `PiLp.instPseudoMetricSpace 2 …` for the sphere and `PiLp.instEMetricSpace 2 …` for `dimH`
  (audit 1). `(½,½,½,½)` is on the frozen sphere; `(1,1,0,0)` and `(1,1,1,1)` are not (both
  audits, Lean).
- **Segment.** `segment ℝ a (a + e) = (t ↦ a + t•e) '' Icc 0 1` (both audits, Lean). For e ∈ S³
  its diameter is 1 and its `dimH` is 1. It is closed and contains both endpoints.
- **𝓗^s.** `Measure.hausdorffMeasure_apply` gives, for every set s,
  `μH[d] s = ⨆ r>0, ⨅ (t : ℕ → Set) (s ⊆ ⋃ tₙ) (ediam tₙ ≤ r), ∑' ⨆ (tₙ nonempty), ediam(tₙ)^d`.
  Empty pieces count 0, finite covers are padded with ∅, and the supremum over r is the limit
  δ ↓ 0. This is the paper's formula exactly, with no constant on either side (W3 `paperH_eq`;
  audit 2 `hausdorff_covering`).
- **dim_H.** Mathlib defines `dimH` as `⨆ {d | μH[d] K = ∞}` under `borelize`, and `dimH_eq_iInf`
  gives `⨅ {d : ℝ≥0 | μH[d] K = 0}`, the paper's definition, for every K (W3 `paperDim_eq`;
  audit 2 `dimH_paper`). It does not depend on the ambient measurable-space instance.
- **Value.** `(4 : ℝ≥0∞)`. `dimH` of any subset of ℝ⁴ is ≤ 4 (both audits, Lean), so `= 4` is
  exactly `4 ≤ dimH K`, and no `⊤` case arises.

So the Lean statement is equivalent to Theorem 1.1, not merely at least as strong. Audit 1's W4
proves the equivalence formally, against a restatement that uses only the paper's notions
(Σeᵢ² = 1, {a + te}, the cover formula, the infimum). Not formalized: §11's consequences
(packing and Minkowski dimension, higher n, Nikodym, curved Kakeya). They are outside Theorem 1.1.

### 2.2 The definitions are standard and not degenerate

- **Standard.** `ChallengeDeps` adds no definitions, and `config.json` has no `definition_names`.
  Every notion is stock Mathlib with its expected instances.
- **Satisfiable and consistent.** The closed unit ball (a = 0) and `univ` satisfy the hypothesis
  and have `dimH = 4` (both audits).
- **Not trivially true.**
  - A point and a coordinate hyperplane fail the hypothesis (audit 1, `{x₀ = 0}`, dimH ≤ 3).
  - A hyperplane `{x₃ = 0}` contains unit segments in every direction of a great 2-sphere and has
    `dimH = 3` (audit 2). A countable union of unit segments has `dimH ≤ 1` (audit 1). So "every
    e ∈ S³" is load-bearing.
  - Before this paper the best bound for general Kakeya sets in ℝ⁴ was 3.059 (Katz–Zahl).
- **Independence and logs.** Audit 1's `Witness.lean` imports only `Challenge`. Audit 2's
  `Fid2KK.lean` imports `Mathlib`, `ChallengeDeps` and `Challenge`. Neither uses `Submission` or
  WZ code. I re-read both logs: exit 0, 20 and 18 theorems, each
  `[propext, Classical.choice, Quot.sound]`. The only warning is the starter's own `sorry` in
  `Challenge.lean`.

### 2.3 No convention makes it easier

| Possible loophole | Status |
|---|---|
| `μH` only on measurable sets | No. The cover formula holds for every set, so non-measurable K are in scope, as in the paper. |
| `dimH` junk or ambient instance | No. `borelize` fixes the σ-algebra. `dimH` takes the true values 0, 1, 3 and 4 on a point, a segment, a hyperplane and a ball (audits). |
| sup metric / cube sphere | No. `PiLp 2`, round S³ (Lean witnesses). |
| degenerate segment | No. `‖e‖ = 1`, closed, `dimH = 1`. |
| quantifier order | `∀ e, ∃ a`, as the paper. |
| restricted directions | No. Every e ∈ S³. |
| compactness added | No. K is arbitrary. That is harder than the compact case, and it is the paper's setting. The 3-D `IsKakeya` (compact) of the WZ library appears only inside `Submission/WZ/`: no file in `Obl/`, `Lib/` or `Seed/` mentions `IsKakeya` or `LeanEval.` (grep, 0 files). |
| `ℝ≥0∞` arithmetic | `dimH K ≤ 4` always; no `⊤` case. |
| Submission-side instances or notation | None global (audit 1). In any case the comparator compares kernel types. |

### 2.4 The proof follows the paper, and the refutations weaken nothing

**Root.** `Submission/Obl/Root.lean` in E restates the challenge verbatim (only `:= by` becomes
`:=`) and reads:

```lean
le_antisymm (Submission.Seed.K4.dimH_le_four K)
  (k4_lower_of_discrete
    (k4_core k4_plank_estimate k4_multilinear_kakeya k4_oss_decay k4_graph_bsg)
    K hK)
```

`Solution.lean` (zhengyang's, unchanged) closes the challenge by `Submission.kakeya_four_dimensions K hK`.

**Children's types.** I compiled `fidelity-verdict/RecCheck.lean` in docker. It is generated
mechanically from the tree's `frozen/o00{1..6}.json` (`gen_reccheck.py`). For each child it proves
`theorem Rec074.oN_matches : <frozen lean_statement> := Submission.<lean_name>`. It also proves
`Rec074.root_matches : type_of% @kakeya_four_dimensions := @Submission.kakeya_four_dimensions`,
and compares the types as `Expr`s. Result (`RecCheck.log`, exit 0):
- all six children's declaration types are **syntactically equal** to their frozen types;
- `Submission.kakeya_four_dimensions` has **syntactically** the challenge theorem's type;
- each of the seven theorems, and `Submission.kakeya_four_dimensions` itself, depends only on
  `[propext, Classical.choice, Quot.sound]`.

The root has no frozen statement of its own (`root_fixed`; the frozen root is `Challenge.lean`).

**Mapping to the paper** (both audits; I spot-checked the TeX and computed the closures,
`closure.txt`):

| Child | Paper | Content; import closure (local modules) |
|---|---|---|
| seed `dimH_le_four` | the ambient bound, last line of the proof of Thm 1.1 (`09-unbounded-narrowness.tex` l. 1184–1232, §10) | `dimH_mono` + `Real.dimH_univ_eq_finrank`; seed file 70 lines |
| o001 `k4_lower_of_discrete` (R2) | Thm 2.17 ¶1, "A finite selection from outer measure" | DK4 → ∀ K, hK → 4 ≤ dimH K; outer measure of the slope set, `choose` for witnesses, countable ball covers; 12 modules, 1,381 lines |
| o006 `k4_core` (R3core) | Thm 2.17 ¶2 onward and §§3–10 | T1 → T3 → T4 → T5 → DK4; 10,349 modules |
| o002 `k4_plank_estimate` (T1) | Lemma 2.15, which the paper cites as Lemma 2.3 of OpenAI's 3-D maximal paper (← Guth–Wang–Zahl) | from WZ's `wz_endpoint_bootstrap` (the E(0,0) union estimate); 2,889 modules, including all 2,872 WZ modules |
| o003 `k4_multilinear_kakeya` (T3) | (6.10), cited from Carbery–Valdimarsson | n = 2 by two strips, n = 3, 4 by visibility; 44 modules |
| o004 `k4_oss_decay` (T4) | the special case of (7.10) (Orponen–de Saxcé–Shmerkin Thm 1.5, cited) that Lemma 7.4 uses | Bourgain's route; 234 modules, 165 of them WZ |
| o005 `k4_graph_bsg` (T5) | Lemma 7.1, **proved in the paper** (after Sudakov–Szemerédi–Vu 2005) | c = 1/36, C₀ = 6144; 5 modules |
| (not a child) T2 | Thm 5.5, cited from Wang–Zahl sticky Kakeya Thm 5.2 | `WangZahlLot.wz_ad_projection_dichotomy` (WZ o103), used in `k4_scalar_normal_first_jet` and `k4_horizontal_interior_parameter_bootstrap` |

The six preset children (split s001, author `preset`) were all accepted. Unlike 078, no preset
child was false.

**The refuted obligations.** `tree.json` has six refutation claims. All are `how: model`,
`lean_blob: null`, confirmed by a second verifier session. Five obligations ended `refuted`:

| Obligation (depth, parent/split) | Claim | What was false |
|---|---|---|
| o137 `k4_scalar_physical_parameter_preparation` (8, o092/s048) | g00347 | coefficient-bin floors at every real width; the paper uses aligned dyadic bins |
| o285 `k4_original_interpolated_field_source` (11, o265/s107) | g00961 | a Cantor-digit hidden law defeats the field-packet clause |
| o267 `k4_original_potential_reference_completion` (10, o204/s098) | g00978 | a tilted digit-tree configuration excludes the width and candidate exits |
| o266 `k4_narrow_original_potential_atlas` (10, o204/s098) | g00997 | the same construction, middle-level test changed |
| o292 `k4_narrow_atlas_breadth_ladder` (11, o266/s111) | g00996 | the same construction |

The sixth claim, g00977, was on o283 (child of o267), which was already superseded. The repairs:
o092 was re-split (s084, o228–o231, all accepted). o106 `k4_isotropic_path_improvement` was proved
directly at 2026-10-22T18:07:07Z, and the event "superseded o116, o143, o204: o106 was proved on
its own first" removed the whole o204 branch.

My closure check (`closure.py`, on the recompile's `ws/`, whose 10,629 `.lean` files I verified
blob-identical to E):
- no refuted or superseded obligation has a module file or directory in E;
- none is in Root's import closure, and no module in that closure lies under a refuted or
  superseded obligation's name;
- every obligation module in Root's closure is accepted.

The refutations are informal (model-checked), unlike 078's, which I could check in Lean. That does
not matter here: no false statement is assumed anywhere. Every module on the route is a closed
theorem, the checkers enforce the three axioms transitively, and the root's type is the
challenge's. The repairs follow the paper (nested dyadic grids for o137).

### 2.5 The inlined WangZahlLot library

- **What it is.** `Submission/WZ/` holds 2,872 modules, 370,727 lines. They are the import closure
  of `Submission.WZ.Obl.wz_tube_estimate`, which is exactly the set of WZ modules the 074 proof
  reaches. It is our own LOT tree `g-wang_zahl_kakeya_dimH` (humanfia; 2026-10-11T13:27:49Z →
  2026-10-13T23:41:50Z, `proved`, root lib commit `da2150fe…`; Lean-Eval #2121 per NOTICE). The
  package renames `Submission` → `WangZahlLot` and nothing else. E renames module paths
  `WangZahlLot.*` → `Submission.WZ.*` and keeps declaration names.
- **Provenance, checked byte for byte** (`wzcheck.py`, `wzcheck.txt`):
  1. `prep/074/wzlib/pkg/WangZahlLot/` and the package in the sealed wzlib set
     (`deps-wzlib-20261019/…/packages/WangZahlLot/`, the one the v10wz checker re-inlines from)
     are identical: 2,881 files, sha256 equal.
  2. All 2,875 entries of `WZLOT-FILES.json` match: `sha256_to` equals the package file, and
     `sha256_from` equals the blob at `da2150fe` in the WZ tree's `tree.git` (read with `git
     cat-file`).
  3. All 2,872 files under E's `Submission/WZ/` equal their package file, after dropping the two
     header comment lines and mapping `Submission.WZ.` → `WangZahlLot.` on `import` / `open
     private … from` lines. 0 differ.
  4. The three package modules not in E are `WangZahlLot/Helpers.lean`, `Obl/Root.lean` and
     `Obl/Root/Geometry.lean` (180 lines). So WZ's own compact-set root theorem is not in E.
- **The checker enforces it.** `trusted-v10wz/<id>/check.sh root` re-inlines the package with the
  pinned `inline.py` (its sha256 is pinned in `inline.json`) and refuses any byte of E's copy that
  differs. In run 2 it accepted, and the official `trusted-v10` accepted the same files.
- **Built from source.** The WZ files are `.lean` sources in `Submission/`. The recompile built
  all 10,625 Submission modules and the checkers built them too, so WZ's axioms fall under the
  same transitive check. No prebuilt WZ `.olean` is trusted.
- **No external code inside WZ.** Its provenance comments name only sessions of the WZ tree (grep:
  no lean-pool, GitHub or arXiv source cited).
- **Genuine use.** T1 rests on WZ's E(0,0) estimate. T2 is WZ's projection dichotomy (the paper's
  Theorem 5.5). WZ also supplies a projection theorem in T4 and many utilities (both audits).
- **X → E.** `git diff X E`: 2,876 files added (the 2,872 WZ files, `NOTICE` and three `LICENSES/`
  files) and 2,620 pruned (`.lot/lib` 99, `Lib` 376, `Obl` 2,145). 29 paths changed: 27
  Submission files, where only 72 `import` lines changed (36 removed, 36 re-added under the new
  name), plus `lakefile.toml` and `lake-manifest.json`. Those two return to the starter's official
  bytes; X used the wzlib Lean set's build files.

## 3. Points of difference or concern, and decisions

| # | Point | Raised by | My check | Decision |
|---|---|---|---|---|
| D1 | End time: "ended at 20:47Z" (audit 2) or 20:36:24Z (audit 1) | audits 1 and 2 | `result.json`: started 2026-10-21T01:44:08Z, `ended` 2026-10-22T20:36:24Z (42.87 h). `tree.json` `root_accepted_at` 20:30:36.75Z (42.78 h). `result.json` and `REPORT.md` were written at 20:46. The final-check plan run started at 20:47:23Z. | **Audit 1 is right.** Use "root accepted after about 42.8 h; tree ended after 42.9 h (result.json)". |
| D2 | Graph BSG: one of "the paper's four cited analytic inputs" (audit 1) or "proved in the paper" (audit 2) | audits 1 and 2 | `06a-retained-edge.tex` l. 26–47: Lemma 7.1 `re:graph-bsg` has its own proof, "following Sudakov–Szemerédi–Vu [Lemma 4.2] … compare Tao–Vu". The cited inputs are Lemma 2.15 (← 3-D maximal Lemma 2.3), (6.10) Carbery–Valdimarsson, (7.10) OdSS Thm 1.5 and Thm 5.5 (← WZ sticky Thm 5.2). | **Audit 2 is right.** Public text: "the four cited inputs (3-D maximal Lemma 2.3 with its GWZ input, Carbery–Valdimarsson, the OdSS special case, Wang–Zahl's planar theorem) are proved in Lean, as is the paper's own Lemma 7.1". |
| D3 | Sizes: "10,624 files … Obl 7,231 files, 933,872 lines" (audit 1); "10,629 `.lean` paths", "10,625 Submission sources", Root closure "10,414 modules, 1,357,270 lines", `Submission` closure "10,626" (audit 2); "10,625 modules, 1,381,639 lines" (FINAL-CHECK) | audits, FINAL-CHECK | `closure.txt`: E's Submission = `Submission.lean` + `Helpers` + WZ 2,872 + Obl 7,231 + Lib 519 + Seed 1 = **10,625 modules, 1,381,639 lines**. Under `Submission/` there are 10,624 files; with the 5 top-level `.lean` files, 10,629. Root's closure is 10,413 Submission modules + `ChallengeDeps` = 10,414; `Submission`'s is 10,625 + `ChallengeDeps` = 10,626. Line counts differ by one between `wc -l` and Python, because `RepairedCut.lean` has no final newline. | **All are right**; they count different sets. Public numbers: "10,625 modules, about 1.38M lines, of which 2,872 modules / 371k lines are our inlined WZ library". |
| D4 | Obligations in E: "235 accepted modules plus Root; o248, o265, o289–o291 pruned" (audit 1) or "218 in Root's closure; 18 accepted off-route" (audit 2) | audits 1 and 2 | 296 obligations: 241 accepted (root included), 50 superseded, 5 refuted; depth ≤ 12; 112 splits. Of the 240 non-root accepted: 235 have modules in E, 217 are in Root's closure (218 with the root), and 18 are in E off-route (o033, o034, o045, o052, o053, o058, o060, o061, o066, o095, o110, o117, o122, o155, o187, o190, o257, o260; 212 modules). The 5 pruned ones lie under superseded o227 (o248) or o204 (o265, o289, o290, o291). | **Both are right.** |
| D5 | WZ counts: 2,872 (E, NOTICE), 2,874 (package NOTICE), 2,875 (`WZLOT.json`); 370,727 vs 365,163 lines | audit 2 (note 5) | The package is WZ's root closure (2,874 modules) + its problem file = 2,875 files, 365,163 lines. E inlines 2,872 = the closure of `wz_tube_estimate`. 365,163 − 180 (the three modules not inlined) + 2 × 2,872 header lines = 370,727. | **Consistent.** |
| D6 | WZ byte identity: 303 spot-checked (audit 1) or all 2,872 (audit 2) | audits 1 and 2 | §2.5: all 2,872 identical after un-inlining; prep package = sealed-set package (2,881 files); all 2,875 `sha256_from`/`sha256_to` match the WZ tree at `da2150fe`. The v10wz checker re-inlined and accepted (run 2). | **Provenance proven** from source to E. |
| D7 | Refutations "confirmed by a model, none in Lean" | audits 1 and 2 | `tree.json`: six claims, `how: model`, `lean_blob: null`, each verified by a second session (x0485, x1029, x1042, x1043, x1072, x1073). None of the five refuted modules, nor o283's, is in E or in Root's closure (§2.4). | **Agree.** The refutations are informal, but nothing depends on them. They were defects of internal frozen children, not of the paper or the root. |
| D8 | lean-pool imports: "ZhangYeungInequality…Entropy, two files" (audit 1), "ZhangYeung/PFR entropy ×2" (audit 2); NOTICE "attributes one adapted file" (audit 1, §5.5) | audits 1 and 2 | Four files import four lean-pool modules: `NavierStokesAndEuler.Euler.LpParameterIntegral` (OpenAI), `SardMoreira.MainTheorem` (Yury G. Kudryashov), and two PFR files vendored in Zhang–Yeung: `PFR.ForMathlib.Entropy.Kernel.MutualInfo` and `PFR.Mathlib.Analysis.SpecialFunctions.NegMulLog` (both "PFR contributors"). NOTICE lists **two** adapted files, both `ConicKernels.lean` copies from `LeanPool.MetricCodes` (openai/ten-proofs). | **Both essentially right**; the exact lists are here. |
| D9 | `admit`: "15 hits, all prose" (audit 1) or "four prose lines" (audit 2) | audits 1 and 2 | `grep -w admit`: 15 lines in 15 files, all English prose in doc comments. `sorry` 1 (Root's docstring), `axiom` 1 and `opaque` 2 (comments); `native_decide`, `implemented_by`, `extern`, `unsafe`: 0. | **Audit 1's count is right.** Audit 2 undercounted prose hits. No effect. |
| D10 | E's `NOTICE` (new finding) | (my check) | (a) The Zhang–Yeung entry ends with "Its attribution notice reads:" and nothing after it. lean-pool's NOTICE (l. 460–465) has "The Zhang-Yeung Inequality / Copyright 2026 Christopher Boone". This is the same bug as 078 D8: the generator (`lot12-sizectl`) drops the indented quote. (b) PFR contributors are not named. (c) The second copy `Obl/k4_approximate_conic_taylor_decomposition/Kit/ConicKernels.lean` lacks the upstream header "Copyright (c) 2026 OpenAI … Authors: OpenAI, Dean Cureton", which the first copy (`Lib/K4CubicTests/ConicKernels.lean`) carries. NOTICE names OpenAI but not Dean Cureton. (d) `LICENSES/wang-zahl-lot/NOTICE` says the WZ problem file is "unchanged but for its module path", but the package dropped `import Lake.Toml`, `import Lake.Util.Message` and `import Lean` (diff against `da2150fe`). `WZLOT.json` and E's top-level NOTICE say this correctly. (e) "Files of the proof whose imports were renamed" stops after 20 of 27 with "...". (f) The licence of the WZ problem file (Lean-Eval via lean-gap, Apache-2.0) is not named. | Not a fidelity issue. **Fix before any public release** (§5.1). The generator bug from 078 D8 is still unfixed; check every tree that imports lean-pool projects with upstream notices. |
| D11 | Root's docstring is stale | audit 1 (the `sorry` prose); (my check) | It says "The only `sorry`s it depends on are the six children" and calls T2 "the prebuilt `WangZahlLot.wz_ad_projection_dichotomy`". In E there is no `sorry`, and WZ is inlined source (declaration name kept). | Cosmetic. Do not edit E. Correct the prose in any public copy. |
| D12 | X → E: "27 Submission files, 36 import lines" (audit 1) | audit 1 | 29 changed paths: the 27 Submission files (72 changed lines, all `import`) plus `lakefile.toml` and `lake-manifest.json`, which go back to the starter's bytes (§2.5). | **Audit 1 is right** for Submission. The two build files are protected and checked. |
| D13 | Copy used by the audits: `20261022T204723Z` vs FINAL-CHECK's `20261022T204822Z` | (my check) | `204723Z` is the `final-oai.py` plan run (`final-oai-plan.log`). Both copies hold E with tree `63f3d0d9…`. | No effect. |
| D14 | dglib involvement | task question | None in E: no `DifferentialGeometry`/`dglib` import or text (grep 0), no such package in `lake-manifest.json`. Only tooling names come from the dglib work: `inline.py` (written for dglib's package; its docstring still says `Submission/DG/`), the index schema `dglot-index/1` in the package's `DGLOT-INDEX.json`, phase B's `dglib/build.lock`, and `wzwiki.py` (derived from `dgwiki2.py`). | **No dglib involvement.** |
| D15 | Environment | audits 1 and 2, phase B | zhengyang's pin is Lean v4.33.0 / Mathlib 6f1ef4e5; ours is v4.35.0-rc3 / 5e0c4e5. The statement files are byte-identical, and all elaboration witnesses ran under our pin. | The verdict applies to the statement as elaborated under our pin. Any other target environment must re-check with its own comparator. |
| D16 | Resources | FINAL-CHECK | Container `memory.peak` was 68,719,476,736 bytes = **64.0 GiB, the container limit**, in the plain check and in both v10wz containers (`oom_kill 0`). The recompile peaked at 39.98 GiB. Times at 16 CPUs: plain 8,971 s (2.5 h), recompile build 9,720.5 s (2.7 h), v10wz + official 17,265.5 s (4.8 h). The submission is 17.53 MB gz and 91.7 MB raw, against LOT's 100 MB raw limit. | Not a fidelity question. **A blocker to check before any benchmark submission**: Lean-Eval allows 16 GB and 6 h. A peak at the cap hides the true need, because page cache counts. No submission is planned or allowed. |
| D17 | Run 1's v10wz ERROR | FINAL-CHECK | `20261022T204822Z/check-v10wz/official.log` ends at build 12608/12684 with "error waiting for container: unexpected EOF" (00:03:19Z). The v10wz check itself had said "Your solution is okay!". Run 2 repeated the same check on the same E, and both containers accepted. | Infrastructure (dockerd crash), not a verdict on E. |
| D18 | Phase B wording: "Mathlib omits the normalising constant"; inf form from two lemmas | audits 1 and 2 (against phase B) | `01-introduction.tex` l. 22–29 has no constant either. `dimH_eq_iInf` exists at 5e0c4e5 (audit 1's `Elab.log`). | **Refinements only.** μH is the paper's 𝓗^s exactly. The conclusion is unchanged. |
| D19 | "WZ accepted on Lean-Eval as #2121" | audits 1 and 2 | Stated in E's NOTICE, `WZLOT.json` and `inline.json`. I did not re-verify it against Lean-Eval. The WZ tree's `result.json` says `proved`, root `da2150fe`. | Before citing #2121 publicly, confirm it from the submission record. |
| D20 | Independence of the witnesses | (my check) | Neither audit imports `Submission` or WZ. The seed `Seed/K4/Basic.lean` (ours, 70 lines) has similar `dimH` lemmas; the audits wrote their own. | No issue. |

## 4. Open caveats (none blocks the verdict)

1. **Scope.** The statement is Theorem 1.1 only. §11's consequences are not formalized.
2. **Environment.** Fidelity was checked for the elaboration under Lean v4.35.0-rc3 / Mathlib
   5e0c4e5 (D15).
3. **Weight of the result.** The paper is an unrefereed 175-page preprint, and it claims the
   four-dimensional Hausdorff Kakeya conjecture. Our evidence is:
   - the kernel check by two checkers, with Lean and nanoda;
   - the independent recompile;
   - standard axioms only;

   applied to a statement that three reviews found faithful. A claim of this weight deserves an
   external expert reading of `Challenge.lean` / `ChallengeDeps.lean` before it goes public.
4. **Refutations are informal.** The five refutations were confirmed by models, not in Lean (D7).
   That affects only how the tree found its route, not the result.
5. **Unused accepted modules.** Besides the top module `Submission`, E carries 212 Submission
   modules outside Root's import closure. They belong to 18 accepted obligations that the route
   does not use (D4). They are closed lemmas, harmless, and add only to the build.
6. **External code beyond lean-pool.** E's sources cite no openai/math (`oaimath`) extlib code
   (grep 0). I did not run a content-similarity scan against the tree's search index.

## 5. Needed before any public claim

1. **Attribution and licensing.**
   - **Inlined code.** The WZ library is our own: humanfia LOT tree `g-wang_zahl_kakeya_dimH`,
     2026-10-11..13, lib `da2150fe`. Its mathematics is H. Wang and J. Zahl's (arXiv:2502.17655,
     2210.09581). Its `ChallengeDeps.lean` is the Lean-Eval problem file of `wang_zahl_kakeya_dimH`
     (leanprover/lean-eval 38361be via ZhengyangZhang06/lean-gap d04dcc4, Apache-2.0).
   - **Imported libraries.** E imports 4 modules from pinned lean-pool e9d53e9c, from three
     Apache-2.0 upstreams: openai/NavierStokesAndEuler, urkud/SardMoreira, and
     cboone/zhang-yeung-inequality with its vendored PFR code.
   - **Adapted code.** Two `ConicKernels.lean` files are adapted from `LeanPool.MetricCodes`
     (openai/ten-proofs; "OpenAI, Dean Cureton").
   - **What E ships.** `LICENSES/lean-pool/LICENSE` (Apache-2.0 text),
     `LICENSES/wang-zahl-lot/{NOTICE,WZLOT.json}` and `NOTICE`.
   - **What any public tarball or repository must fix** (D10):
     - restore the Zhang–Yeung notice ("The Zhang-Yeung Inequality / Copyright 2026 Christopher
       Boone");
     - name the PFR contributors;
     - carry the OpenAI / Dean Cureton header in the second `ConicKernels.lean`, or name them in
       NOTICE;
     - correct "unchanged but for its module path" in the WZ NOTICE;
     - list all 27 renamed files;
     - name the WZ problem file's licence.
   - **The generator.** Fix LOT's NOTICE generator; the 078 D8 bug is still in `lot12-sizectl`.
   - **Credit.**
     - zhengyang wrote the formal statement. Credit him for `Challenge.lean` / `ChallengeDeps.lean`
       (and `Solution.lean`, `config.json`, `holes.json`), used byte for byte, and ask how he wants
       them licensed.
     - Our seed `Submission/Seed/K4/Basic.lean` (70 lines) is our own code.
2. **The claim itself.** Say: "a Lean 4 proof, kernel-checked (Lean and nanoda), of Theorem 1.1 of
   OpenAI's preprint *Every four-dimensional Kakeya set has full Hausdorff dimension* (September
   24, 2026): every set K ⊂ ℝ⁴ containing a unit segment in every direction has Hausdorff
   dimension 4", and cite the paper.
   - Say that the cited inputs (D2) are proved in Lean, the 3-D input and the planar theorem
     through our own earlier Wang–Zahl formalization.
   - Credit the authors of the cited mathematics: Wang–Zahl, Guth–Wang–Zahl, Carbery–Valdimarsson,
     Orponen–de Saxcé–Shmerkin, Sudakov–Szemerédi–Vu.
   - Do not claim §11's consequences, and do not describe a Lean statement of the Wang–Zahl
     theorems other than the ones actually proved.
3. **Provenance**, stated plainly:
   - The agents worked from the paper's TeX, so this is a formalization of the paper's proof, not
     an independent discovery. The seed's `papers/` also held the 3-D maximal paper's TeX sections
     and the two Wang–Zahl PDFs.
   - The WZ library was available as an importable package, and phase B built a search index
     (lean wiki) for the tree. If the claim goes into detail, say whether online search was
     available to the agents.
   - We wrote the preset six-way split (R2, T1, T3, T4, T5, R3core) from the paper's structure
     (`seed/tools/gen_split.py`; T4 and DK4 revised after `REVIEW.md` P0-4/P1-1). All six were
     accepted.
   - The tree wrote the rest: 7,231 Obl + 519 Lib modules (about 1.01M lines) on top of the
     2,872-module WZ library. It had 296 obligations (241 accepted, 50 superseded, 5 refuted) and
     ran 42.9 h.
   - Give the model mix: slot A `codex/gpt-6.1-sol:max`, slot B `claude/claude-opus-5-5:max`,
     `model_policy=ratio`, `model_ratio_a=2/3` (`tree.json`).
4. **Re-check openai/math before publishing:**
   - that Theorem 1.1 has not changed in a later revision of the 074 preprint;
   - that OpenAI has not since published its own Lean formalization of family 074.
5. **Target environment and resources.**
   - Before any benchmark submission, measure the real memory need below the 64 GiB cap, find where
     it arises (compile, or comparator/nanoda), and compare it and the 2.5–4.8 h run time with that
     benchmark's limits; Lean-Eval's are 16 GB and 6 h (D16). This is a likely blocker.
   - Re-run the target environment's official checker.
   - Locally, both of our checkers accepted E with nanoda.
6. **Optional extra assurance** (not required for faithfulness):
   - Lean refutations of the five refuted children, if the refutations are ever described;
   - Lean corollaries for §11's consequences.
7. **Go-ahead.** Nothing may be submitted, posted or published without the user's explicit
   go-ahead.

## 6. What this reconciliation did

- **Read:**
  - the paper TeX (seed copy, six section files sha256-equal to zhengyang's `build/sections/`):
    `01-introduction.tex` l. 1–60, `02-framework.tex` (Lemma 2.15 and its proof),
    `05-scalar-tools.tex` (Thm 5.5), `06-isotropic.tex` ((6.10)), `06a-retained-edge.tex`
    (Lemma 7.1, (7.10)) and `09-unbounded-narrowness.tex` l. 1184–1232 (the proof of Thm 1.1),
    and `paper.tex`'s section order;
  - `Challenge.lean`, `ChallengeDeps.lean`, `Solution.lean`, `Root.lean`, the seed file and the
    two `ConicKernels.lean` files;
  - phase-B `FIDELITY.md`, `README.md` and `PHASE-B.md`, both audits with their Lean sources and
    logs, FINAL-CHECK.md and both run reports, and the run-1 `official.log` tail;
  - from the ended tree, read only: `result.json`, `tree.json` (obligations, splits, refutations,
    models, parameters), `frozen/*.json`, `effective.json`, and `events.jsonl` (grep for o106);
  - in E (read-only `git ls-tree`/`show`/`diff` on the final-check copy of `tree.git`): `NOTICE`,
    `LICENSES/`, the protected files and the X → E diff. The recompile's `ws/` is blob-identical
    to E (all 10,629 `.lean` files, `git hash-object`);
  - the WZ package's `NOTICE`, `WZLOT.json`, `WZLOT-FILES.json`, `DGLOT-INDEX.json`, `lakefile.toml`,
    `trusted-v10wz/<id>/inline.json` and `inline.py`'s header, and the WZ tree's `result.json` and
    `tree.git` at `da2150fe` (read only);
  - lean-pool's NOTICE (l. 355–468) and the headers of the four imported modules and of
    `MetricCodes/HarmonicAnalysis.lean`;
  - sha256 of zhengyang's `lean-problem/` files, specific files only, no traversal of /mnt/data.
- **Ran:**
  - `closure.py` (import closures from `import` lines) and `wzcheck.py` (WZ provenance), host
    Python, read-only;
  - one Lean check in docker:
    - container `oai074rec-check-4183887`, image `deuring-runner:1`;
    - `--network none`, `--rm`, `--memory 32g`, 4 CPUs, every input mounted read-only (`~/.elan`,
      the sealed deps packages, the recompile's `.lake/build/lib/lean`, this directory);
    - `lean` only: no lake, no check.sh, no comparator;
    - 10:20:35Z–10:20:44Z, exit 0;
    - no `oai074rec*` container remains.

  The deps `.git/index` digest (absolute-path form) was **7f64b9cb** and the wzlib set's was
  **b7c369c1**, before and after the run and at the end of this work. Nothing in the tree, E, the
  recompile directory, prep/ or the deps was modified.
- **Written:** this file, and `final/074/fidelity-verdict/`:
  - `RecCheck.lean` and `RecCheck.log` (sha256 `92923a23…`, `99b0b6cd…`), generated by
    `gen_reccheck.py` (`e138b749…`);
  - `run-in-docker.sh` (`7b321a27…`);
  - `closure.py` and `closure.txt` (`124bc707…`, `5a0cd713…`);
  - `wzcheck.py` and `wzcheck.txt` (`e94c445d…`, `dc8e7edd…`).
