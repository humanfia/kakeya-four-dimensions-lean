# 074 fidelity audit #2: `oai_074_kakeya_four_dimensions`

Independent second audit, 2026-10-22. I did not read `FIDELITY-AUDIT-1.md` or `fidelity-audit-1/`.
I formed the view below from the paper and the Lean files first. I read the phase-B review
(`prep/074/FIDELITY.md`) only afterwards (§6).

**Sources**

- **Paper.** OpenAI, *Every Four-Dimensional Kakeya Set Has Full Hausdorff Dimension*
  (September 24, 2026).
  - TeX at `/mnt/data/zhengyang-workspace/openai-math-lot-pdfs/074-kakeya-four-dimensions/source-…/build/`
    (read only). PDF sha256 `30d0c186…`, the same file phase B used.
  - I read §1 (Theorem 1.1 and the covering definition of `H^s` and `dim_H`) in full, Theorem 2.17
    (`thm:model-reduction`, its first paragraph in full), Lemma 2.15 (`lem:weighted-planks`),
    Theorem 5.5 (`a04:planar-input`) and the proof of Theorem 1.1 (§10, "Completion of the proof"; the TeX files `01`–`10` with `06a` are §§1–11).
    For the rest I used the introduction's outline and `prep/074/REVIEW.md` (a)–(b).
- **Statement.** `/home/ubuntu/lean-runs/lean-gap/workspaces/oai_074_kakeya_four_dimensions/{Challenge,ChallengeDeps}.lean`.
  - sha256 `bf8e140c…` and `c1a46df9…`.
  - Both are byte-identical to zhengyang's `lean-problem/` copies. So are `Solution.lean`
    (`20074f66…`), `Submission.lean`, `config.json` (`538baf9e…`), `holes.json` and `README.md`.
  - Only the build files differ (`lean-toolchain` v4.33.0 → v4.35.0-rc3, `lakefile.toml`,
    `lake-manifest.json` Mathlib 6f1ef4e5 → 5e0c4e5 plus lean-pool, and the hardened
    `WorkspaceTest.lean`). That is our standard port; it does not touch the statement.
- **Proof.** Tree `g-oai-074`, X = `e18a9d88…`, judged export E = `71391e12db6f5956b54bcdb01a6b1ceeba11604d`.
  - I read E only through read-only `git ls-tree`/`git archive` of the copy
    `final/074/20261022T204723Z/copy/…`, unpacked into a scratch directory outside the deps.
  - E has 10,641 paths: 10,629 `.lean` files (`Submission/WZ/` 2,872, `Submission/Obl/` 7,231,
    `Submission/Lib/` 519, `Submission/Seed/` 1), plus `LICENSES/` (3) and the protected files.
  - E's protected files (`Challenge`, `ChallengeDeps`, `Solution`, `config.json`, `holes.json`,
    the build files, `WorkspaceTest.lean`, `README.md`, `PROBLEM.md`) are byte-identical to the
    workspace's.
  - Tree state (`tree.json`, `archive/blobs`) and the WZ tree's `tree.git` were only read.

## Verdict: **FAITHFUL**

`kakeya_four_dimensions` is exactly Theorem 1.1 of the paper (§1). It covers:
- an arbitrary set `K ⊆ ℝ⁴`, with no measurability, compactness or boundedness;
- the Euclidean `ℝ⁴` and its round unit sphere `S³`;
- for every direction, some closed unit segment `{a + te : 0 ≤ t ≤ 1}`, with no regularity of
  `e ↦ a`;
- Mathlib's `dimH`, which is the paper's covering definition applied to arbitrary sets;
- the value `4` in `ℝ≥0∞`.

`ChallengeDeps` adds no definitions. Every Mathlib notion in the statement has its textbook
meaning, and I Lean-checked each one (§2):
- the norm, the distance and the sphere are Euclidean;
- `segment ℝ a (a + e)` is `{a + t • e | t ∈ [0,1]}`;
- `μH[d] s` is the countable-cover formula for every set;
- `dimH K = ⨅ {d | μH[d] K = 0}`, the paper's definition;
- `dimH ≤ 4` always.

The statement is neither vacuous nor degenerate (Lean-checked):
- the closed unit ball satisfies the hypothesis and has `dimH = 4`;
- each witnessing segment has `dimH = 1`;
- the hyperplane `{x₃ = 0}` has a unit segment in every direction of a great 2-sphere, yet
  `dimH = 3`. The quantifier over all of `S³` is therefore load-bearing.

No convention makes the statement easier (§3).

The proof follows the paper (§4):
- the upper bound;
- the Theorem 2.17 reduction from an arbitrary Kakeya set to a discrete estimate (R2, using
  outer measure only);
- the discrete estimate from the "no bad problem" argument of Sections 2–10 (R3core);
- the four cited inputs, which the tree proved rather than assumed (T1, T3, T4, T5).

The inlined `WangZahlLot` library is a genuine mathematical dependency, not plumbing. It supplies:
- the Wang–Zahl 3D convex-tube union estimate behind T1, the paper's cited Lemma 2.3 of the OpenAI
  3D maximal paper;
- the Wang–Zahl planar dot-product theorem, the paper's Theorem 5.5;
- a robust projection theorem used inside T4;
- classical utilities.

It is our own fully proved library, inlined from source, and its files trace byte for byte to the
accepted WZ tree (§4.2). The five refuted obligations were over-strong intermediate statements.
None of their modules is in E, and the root is the frozen statement verbatim (§4.3).

E contains no `sorry`, `axiom`, `implemented_by`, `@[extern]`, `unsafe`, `native_decide` or
`opaque` declarations (§4.4). The axiom and kernel checks themselves belong to `FINAL-CHECK.md`,
which was still running when I wrote this.

## 1. Lean statement against Theorem 1.1

Paper, §1, Theorem 1.1: *Let K ⊂ ℝ⁴. Suppose that for every e ∈ S³ there is a point a_e ∈ ℝ⁴ such
that {a_e + te : 0 ≤ t ≤ 1} ⊂ K. Then dim_H K = 4.* The paper also says: "Neither K nor the choice
of its witnessing segments is required to be measurable."

The covering definition it uses:
- H^s_δ(K) = inf{Σ (diam U_i)^s : K ⊂ ⋃ U_i, diam U_i ≤ δ}, over countable covers;
- H^s = lim_{δ↓0} H^s_δ;
- dim_H K = inf{s : H^s(K) = 0}.

```lean
theorem kakeya_four_dimensions (K : Set (EuclideanSpace ℝ (Fin 4)))
    (hK : ∀ e ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
      ∃ a : EuclideanSpace ℝ (Fin 4), segment ℝ a (a + e) ⊆ K) :
    dimH K = 4
```

| # | Paper | Lean | Assessment |
|---|---|---|---|
| 1 | K ⊂ ℝ⁴ arbitrary: no measurability, compactness or boundedness | `K : Set (EuclideanSpace ℝ (Fin 4))`, no condition | same. Unlike the 3-D Lean-Eval problem's `IsKakeya`, there is no `IsCompact` |
| 2 | ℝ⁴, Euclidean metric (diam in the covering definition) | `EuclideanSpace ℝ (Fin 4)` = `PiLp 2`: ℓ² norm and distance | same (Lean-checked `norm_eq`, `dist_eq`) |
| 3 | every e ∈ S³ | `∀ e ∈ Metric.sphere 0 1` in that metric: the round sphere Σ eᵢ² = 1 | same (Lean-checked `mem_sphere_iff`). It is not the sup-norm cube: `(½,½,½,½)` is on it and `(1,1,1,1)` is not |
| 4 | a point a_e for each e, with no regularity of e ↦ a_e | `∃ a`, inside `∀ e`, in `Prop` | same. The choice is a bare existential, with no measurable selection |
| 5 | {a_e + te : 0 ≤ t ≤ 1} ⊂ K, a closed unit segment | `segment ℝ a (a + e) ⊆ K` | same (Lean-checked `segment_eq`, `segment_subset_iff`: ⇔ `∀ t ∈ [0,1], a + t • e ∈ K`). With ‖e‖ = 1 it has length 1 and `dimH = 1` (Lean-checked) |
| 6 | H^s via countable covers by arbitrary sets of diam ≤ δ, δ ↓ 0, for arbitrary K | `μH[s] K` = `⨆ r>0, ⨅ covers t : ℕ → Set, diam ≤ r, Σ' diam(tₙ)^s` (empty pieces count 0) | same, for every set (Lean-checked `hausdorff_covering`). The limit δ ↓ 0 is the supremum over r > 0 because H^s_δ is antitone in δ. Finite covers are padded with ∅. Neither side has a normalising constant |
| 7 | dim_H K = inf{s : H^s(K) = 0} | `dimH K` (Mathlib: `⨆ {d : ℝ≥0 \| μH[d] K = ∞}`) | same: `dimH K = ⨅ (d : ℝ≥0) (_ : μH[d] K = 0), d` for every K (Lean-checked `dimH_paper`, Mathlib's `dimH_eq_iInf`) |
| 8 | dim_H K = 4 | `dimH K = 4` in `ℝ≥0∞` | same. `4` is the dimension of the space: `dimH univ = 4` (Lean-checked) |
| 9 | the ambient bound dim_H K ≤ 4 (the paper's final line) | automatic | `dimH K ≤ 4` for every K, so the statement is ⇔ `4 ≤ dimH K` (Lean-checked `dimH_le_four`, `stmt_iff`) |
| 10 | §11 consequences (packing/Minkowski, higher n, Nikodym, curved Kakeya) | not stated | outside Theorem 1.1 |

**Q1 answer.** The Lean statement is equivalent to Theorem 1.1, not merely at least as strong.
The quantifier structure is the same: K, then ∀ e ∈ S³, then ∃ a.
- The set class is the same (arbitrary sets).
- The metric and sphere are the same (Euclidean).
- The segment is the same (closed, length 1).
- The dimension is the same (the covering definition on arbitrary sets).
- The value is the same.

Its content is the four-dimensional Hausdorff Kakeya conjecture in full. Before this paper, the
best bound for general Kakeya sets in ℝ⁴ was 3.059 (Katz–Zahl).

## 2. The definitions, and Lean witnesses

### 2.1 Standard, neither vacuous nor degenerate (argument)

- **`ChallengeDeps.lean`** is `import Mathlib` plus a module docstring. It has no definitions, so
  there is no trusted vocabulary to audit and `config.json` lists no `definition_names`.
- **Metric and sphere.** `EuclideanSpace ℝ (Fin 4)` is `PiLp 2`, so the sphere is the round S³.
  - Hausdorff dimension is bi-Lipschitz invariant, so the metric matters only through the sphere
    and the segment length.
  - Both are Euclidean, as in the paper.
- **Segment.** Mathlib defines `segment ℝ x y` as `{a•x + b•y | a,b ≥ 0, a+b = 1}`. For `y = a + e`
  this is `{a + t e | t ∈ [0,1]}`, closed, with both endpoints included.
- **`μH` and `dimH`.**
  - `μH[d] = (OuterMeasure.mkMetric (r ↦ r^d)).toMeasure`. A `Measure` applied to any set returns
    its outer measure.
  - `hausdorffMeasure_apply` states the covering formula for every `s`, so non-measurable K are
    covered.
  - `dimH` is defined with `borelize`. In `EuclideanSpace`, the ambient measurable space is the
    Borel one, so `dimH_def`/`dimH_eq_iInf` apply.
- **The hypothesis is satisfiable** (any ball of radius ≥ 1, or `univ`), and the sphere is
  nonempty.
- **The conclusion is not a tautology.**
  - Sets of every dimension 0–4 exist.
  - The theorem is false without "every direction": a hyperplane has segments in a 2-sphere of
    directions and dimension 3.
  - Each witnessing segment has dimension exactly 1, so the hypothesis cannot degenerate to points.

### 2.2 Lean confirmation (frozen files, pinned environment)

`final/074/fidelity-audit-2/Fid2KK.lean` (255 lines) imports `Mathlib`, `ChallengeDeps` and
`Challenge`. I wrote it for this audit, using only Mathlib API names. It uses none of the tree's
code and none of `WangZahlLot`.

How it was compiled:
- `frozen/ChallengeDeps.lean` and `frozen/Challenge.lean` are byte-identical copies (sha256
  `c1a46df9…`, `bf8e140c…`). They were compiled first, inside the container, to the container's
  own `/tmp`.
- The toolchain was Lean v4.35.0-rc3, against Mathlib 5e0c4e5.
- Everything ran in docker container `oai074audit2-final-<pid>` with `--network none`, 4 CPUs,
  16 GB, every input mounted read-only, and `--rm`.

The result: 0 errors and 0 warnings in `Fid2KK`, in about 25 s wall. The only message was the
starter's `declaration uses 'sorry'` in `Challenge.lean`. All 18 printed theorems depend only on
`[propext, Classical.choice, Quot.sound]` (log `Fid2KK.log`).

- **(A) The frozen type.**
  - `Stmt` is the Challenge theorem's type, copied verbatim. `example : Stmt := @kakeya_four_dimensions`
    type-checks, so `Stmt` is definitionally the frozen theorem's type.
  - `segment_eq`: `segment ℝ a (a + e) = (t ↦ a + t • e) '' Icc 0 1`.
  - `segment_subset_iff`: `segment ℝ a (a+e) ⊆ K ↔ ∀ t ∈ [0,1], a + t • e ∈ K`. This is the
    paper's hypothesis word for word.
- **(B) The Euclidean metric.**
  - `norm_eq`: `‖x‖ = √(Σ xᵢ²)`. `dist_eq`: `dist x y = √(Σ (xᵢ − yᵢ)²)`.
  - `mem_sphere_iff`: `e ∈ sphere 0 1 ↔ Σ eᵢ² = 1`.
  - `half_mem_sphere`: `(½,½,½,½)` (sup norm ½) is on the frozen sphere.
  - `ones_not_mem_sphere`: `(1,1,1,1)` (sup norm 1) is not.
- **(C) The covering definitions.**
  - `hausdorff_covering`: `μH[d] s = ⨆ r>0, ⨅ (t : ℕ → Set E4) (s ⊆ ⋃ tₙ) (ediam tₙ ≤ r),
    Σ' ⨆ (tₙ nonempty), ediam(tₙ)^d`, for every set `s`.
  - `dimH_paper`: `dimH K = ⨅ (d : ℝ≥0) (μH[d] K = 0), d`, the paper's `inf{s : H^s(K) = 0}`.
  - `dimH_mathlib`: `dimH K = ⨆ (d : ℝ≥0) (μH[d] K = ∞), d`, Mathlib's own definition.
- **(D) The upper bound.** `dimH_univ_four` (`dimH univ = 4`), `dimH_le_four` (every K), and
  `stmt_iff`: `Stmt ↔ ∀ K, hyp K → 4 ≤ dimH K`.
- **(E) Satisfiable and consistent.** `closedBall_instance`: `closedBall 0 1` satisfies the
  hypothesis (with a = 0) and `dimH (closedBall 0 1) = 4`.
- **(F) Non-triviality.**
  - `dimH_segment`: `‖e‖ = 1 → dimH (segment ℝ a (a+e)) = 1`, via the isometry `t ↦ a + t•e`.
  - `emb_isometry`, `dimH_H`: the hyperplane `H = {x | x 3 = 0}` is the isometric image of ℝ³,
    so `dimH H = 3`.
  - `H_partial_kakeya`, `partial_kakeya_dim_three`: H contains a unit segment in every direction
    `e ∈ S³` with `e 3 = 0`. So the hypothesis restricted to a great 2-sphere of directions is
    compatible with `dimH = 3`.
  - `not_all_dim_four`: `¬ ∀ K, dimH K = 4` (via `{0}`).

To rerun: `bash fidelity-audit-2/run-in-docker.sh <tag> Fid2KK.lean`. No lake, check.sh or
comparator was run, and nothing ran on the host against the deps. The deps `.git/index` digest was
`7f64b9cb` before and after every run (three runs; the script prints it). No `oai074audit2-*`
container remains.

**Q2 answer.** The definitions are standard and non-degenerate:
- the space, sphere and segment are Euclidean and literal;
- `μH` and `dimH` are the paper's covering definitions on arbitrary sets;
- the hypothesis is satisfiable;
- the conclusion is consistent (the closed ball) and not trivial (dimension-1 segments, a
  dimension-3 hyperplane with a 2-sphere of directions, `{0}`).

## 3. Conventions that could make the statement easier

| Possible loophole | Status |
|---|---|
| `dimH` junk (wrong measurable space, `⊤`/`0` defaults) | Not hit. `dimH` is defined via `borelize` and agrees with the paper's inf-formula for every set (C). It takes its true values 1, 3 and 4 on a segment, a hyperplane and a ball (E, F). |
| `μH` only on measurable sets | No. The formula holds for every set (C), and the paper's non-measurable K are in scope. |
| `ℝ≥0∞` arithmetic | `dimH K ≤ 4` always, so `= 4` is exactly `≥ 4` (D). There is no `⊤` case to exploit. |
| sup metric / cube sphere | No. The space is `PiLp 2` and the sphere is round (B). |
| degenerate segment (zero length, single point, open) | No. `‖e‖ = 1`, the segment is closed, and it has `dimH = 1` (F). |
| order of quantifiers | `∀ e, ∃ a`: a depends on e arbitrarily, as in the paper. It is not a single `a` for all e, which would be stronger, nor a measurable `e ↦ a`. |
| restricted direction set | No. Every e ∈ S³. A 2-sphere of directions allows dimension 3 (F). |
| compactness/boundedness added | No: K is arbitrary. This is harder than the compact case, and it is the paper's setting. |
| `ChallengeDeps` vocabulary | none (only `import Mathlib`) |

**Q3 answer.** Nothing makes the statement easier than Theorem 1.1.

## 4. The final proof's top level (route)

### 4.1 Root and children

`Submission/Obl/Root.lean` restates the challenge verbatim; only `:= by` becomes `:=`. It proves it
as follows:

```lean
le_antisymm (Submission.Seed.K4.dimH_le_four K)
  (k4_lower_of_discrete
    (k4_core k4_plank_estimate k4_multilinear_kakeya k4_oss_decay k4_graph_bsg) K hK)
```

`Solution.lean` in E is the starter's, so the comparator checks `Submission.kakeya_four_dimensions`
against the challenge.

| Measure | Value |
|---|---|
| Root's import closure | 10,414 modules, 1,357,270 lines |
| ↳ `Submission.WZ.*` | 2,872 modules (370,727 lines) |
| ↳ `Submission.Obl.*` | 7,020 modules (909,730 lines) |
| ↳ `Submission.Lib.*` | 519 modules (76,727 lines) |
| `Submission`'s closure | 10,626 modules, every module in E (212 more than Root's) |

The extra 212 modules come from 18 accepted obligations that `Submission.lean` imports but the
route does not use. They are closed lemmas, so they are harmless.

The tree has 296 obligations: 241 accepted, 50 superseded and 5 refuted. 218 of them are in
Root's closure, and all of those are accepted. No superseded or refuted obligation's module is in
E.

The paper's proof of Theorem 1.1 (§10, "Completion of the proof") runs as follows:
- upper bound plus contradiction;
- dim_H K < 4 ⇒ a bad weighted problem (Theorem 2.17);
- every bad problem is excluded (Sections 3–10, across the regimes ℓ = 0, 0 < ℓ < ∞ and ℓ = ∞).

Each child maps to the paper:

- **Seed `dimH_le_four`.** This is the ambient upper bound, the last line of the paper's proof.
- **o001 R2 `k4_lower_of_discrete`.** This is Theorem 2.17 ¶1, "A finite selection from outer
  measure".
  - It states `DK4 → ∀ K, hK → 4 ≤ dimH K`.
  - DK4 is the discrete configuration after "Choose one successful witness":
    - n ≥ c·2^{3k}/(k+1)² graph lines (x, v), with x₀ = 0, v₀ = 1, ‖v‖ ≤ 2, 2^{−k}-separated
      directions and ‖x‖ ≤ R;
    - m ≤ 2^{(k+1)(4−σ)} balls with radii in (2^{−k−1}, 2^{−k}];
    - the conclusion: not every line spends time ≥ c/(k+1)² in the union of the balls.
  - The proof (12 modules, 1.4k lines) has two steps:
    - `exists_graph_localization`: a graph-slope set A with `volume A ≠ 0`, which for a
      non-measurable A is outer measure, as in the paper;
    - `four_le_dimH_of_bounded_graph_family`: dyadic ball classes, the k^{−2} time pigeonhole, and
      separated packing.
  - It uses no compactness.
- **o006 R3core `k4_core`.** This is Theorem 2.17 ¶2–7 plus Sections 3–10: T1, T3, T4, T5 ⇒ DK4.
  It splits into:
  - `k4_quadratic_slope_volume`: (2.34), the semialgebraic selector and area formula;
  - `k4_algebraic_sheet_bound`: Lemma 3.1;
  - `k4_core_from_geometric_bounds`, which in turn splits into:
    - `k4_two_color_matching` (Lemma 3.3), `k4_scalar_coefficient_clustering` (Lemma 5.1) and
      `k4_real_conic_restoration` (Lemma 6.7);
    - `k4_framework_from_matching_clustering_conic`, whose two parts are:
      - `k4_discrete_of_terminal_charts`: Theorem 2.17's smoothing, homogenization (Lemmas 2.4–2.5),
        density bounds (2.27) and endpoint crop;
      - `k4_cap_class_terminal_charts`: Sections 3–10 (exclusion of bad problems), via
        `k4_scalar_mesh_projection` (Thm 8.2), `k4_affine_skew_row_fit` (L7.7) and
        `k4_terminal_charts_from_scalar_mesh_row_fit`.
- **o002 T1 `k4_plank_estimate`.** This is Lemma 2.15 (`lem:weighted-planks`), which the paper
  cites as Lemma 2.3 of OpenAI's 3-D maximal paper, itself proved from the Guth–Wang–Zahl union
  estimate.
  - The tree proves it with three pieces:
    - `k4_plank_tube_realization`: traces become δ-tubes;
    - `k4_weighted_convex_tubes`: the weighted form from the set form;
    - `unweighted_set_estimate`: from WZ's `wz_tube_estimate` endpoint E(0,0) =
      `wz_endpoint_bootstrap … wz_hairbrush_seed wz_estimate_equivalence wz_strict_improvement`,
      through WZ's pointwise dense estimate.
  - Its closure is 2,889 modules, including all 2,872 WZ modules.
- **o003 T3 `k4_multilinear_kakeya`.** This is the determinant-weighted endpoint multilinear Kakeya
  (6.10), n ∈ {2,3,4}, which the paper cites from Carbery–Valdimarsson. The tree proves it:
  - n = 2 by the two-strip estimate;
  - n = 3, 4 by visibility (polynomial ham sandwich), finite duality and grid transfer.

  44 modules, 6.7k lines.
- **o004 T4 `k4_oss_decay`.** This is the special case of (7.10) (Orponen–de Saxcé–Shmerkin) that
  Lemma 7.4 uses. The paper cites it; the tree proves it by Bourgain's route:
  - collision Cauchy–Schwarz;
  - projection flattening;
  - flat decay;
  - dyadic reduction.

  234 modules, 165 of them WZ.
- **o005 T5 `k4_graph_bsg`.** This is graph BSG with retained edges (Lemma 7.1, proved in the
  paper), with c = 1/36 and C₀ = 6144. 5 modules.
- **T2, the planar dot-product theorem (Theorem 5.5).** It is not a child. It is
  `WangZahlLot.wz_ad_projection_dichotomy` (Wang–Zahl, sticky Kakeya, Theorem 5.2), used in
  `k4_scalar_normal_first_jet` (Prop 5.4) and `k4_horizontal_interior_parameter_bootstrap`.

So the route mirrors the paper's architecture. It goes further than the paper in one respect:
every cited external input (3D-max Lemma 2.3 with its GWZ input, Carbery–Valdimarsson, the OdSS
special case, Wang–Zahl sticky Theorem 5.2) is proved in Lean rather than assumed.

The root's children enter as closed theorems. `k4_core`'s hypotheses are discharged by the
proved `k4_plank_estimate`, `k4_multilinear_kakeya`, `k4_oss_decay` and `k4_graph_bsg`, so no
hypothesis is left open.

### 4.2 The inlined `WangZahlLot` (WZ) library: legitimacy and role

- **What it is.** It is our own LOT tree `g-wang_zahl_kakeya_dimH`, proved 2026-10-13 and accepted
  on Lean-Eval as #2121. Its root closure (2,874 modules plus the problem file) was renamed
  `Submission` → `WangZahlLot`. In E it is inlined as `Submission/WZ/` (2,872 modules) with the
  imports renamed `WangZahlLot.*` → `Submission.WZ.*`, and attributed in `NOTICE` and
  `LICENSES/wang-zahl-lot/`.
- **Provenance (checked).**
  - All 2,872 inlined files equal `prep/074/wzlib/pkg/WangZahlLot/WangZahlLot/**` after removing
    their two header comment lines and undoing the import rename (2,872/2,872 identical).
  - All 2,875 entries of `WZLOT-FILES.json` match. Each `sha256_from` equals the blob at
    `da2150fe` in the WZ tree's `tree.git`, and each `sha256_to` equals the package file.
- **Checked from source.** WZ ships in E as `.lean` sources inside `Submission/`. The checkers
  therefore compile and kernel-check it with the rest: it is not trusted prebuilt `.olean`. The
  forbidden-construct scan (§4.4) found nothing in it.
- **Genuine dependency, not plumbing.**
  1. **T1** uses the core of the Wang–Zahl 3D theorem: the convex-Wolff tube union estimate
     E(0,0), obtained by WZ's induction-on-scales bootstrap. This is exactly the input the paper
     cites (via 3D-max Lemma 2.3 ⇐ GWZ). T1's closure contains every WZ module.

     The 4D proof uses WZ's internal tube estimate, not its compact-set dimension theorem. So the
     `IsCompact` in WZ's own Lean-Eval statement plays no role.
  2. **T2** = `wz_ad_projection_dichotomy` is Wang–Zahl sticky Theorem 5.2, the paper's Theorem
     5.5. It is built in WZ from Kaufman projection counts and Orponen–Shmerkin–Wang thin tubes.
  3. **Inside T4**, `k4_oss_projection_flattening` uses WZ's `uniform_weak_coordinate_expansion`,
     a robust discretized projection theorem.
  4. **Utilities:**
     - covering, dyadic and separated-packing lemmas in R2 (from WZ's 3D reduction);
     - slab-covering lemmas in the scalar sections;
     - the polynomial zero-set null lemma and Stone–Tukey in T3's ham sandwich;
     - Wongkew;
     - the graph path lemma in T5;
     - separated counts and convex-test families.
- **Legitimate.** Using our own previously proved, kernel-checked library is allowed. It is
  inlined from source with attribution, so its correctness rests on the same kernel and axiom
  checks as everything else. It is also the paper's own dependency structure: the 4D proof uses
  the 3D theorem as an input.

### 4.3 The refuted obligations, and whether the accepted route weakens anything

Five obligations are in state `refuted`; all of them were confirmed by a model reviewer, none in
Lean. A sixth confirmed claim, g00977 on o283, came after o283 had already been superseded.

| Obligation | Claim | What was false (the counterexample's point) | Fate of the branch |
|---|---|---|---|
| o137 `k4_scalar_physical_parameter_preparation` (child of o092, split s048) | g00347 | Coefficient-bin floors were required for **every real** width in a compact exponent range; the paper uses aligned dyadic bins. An explicit linear trajectory family meets every hypothesis and violates the floor | s048 rejected. o092 was re-split as s084 (o228–o231, all accepted and on the route) |
| o285 `k4_original_interpolated_field_source` (child of o265, s107) | g00961 | An allowed nonlinear change of the old hidden test (a Cantor-set coefficient law, an exactly linear profile) defeats all three exits | o265's split s107 was replaced by s108. o265 itself is off the route |
| o267 `k4_original_potential_reference_completion` (child of o204, s098) | g00978 (= g00977 on its child o283) | A globally γ-narrow configuration with tilted path bands, whose hidden law is full on short windows: no width exit, no candidate | o204 and its parent o143 were superseded. The branch is off the route |
| o266 `k4_narrow_original_potential_atlas` (child of o204, s098) | g00997 | The same construction with one change to the middle-level tests | as o267 |
| o292 `k4_narrow_atlas_breadth_ladder` (child of o266, s111) | g00996 | The same construction | dropped with o266 |

These were over-strong **intermediate** statements frozen during decomposition. They were deep in
the Section 6 machinery (the isotropic case and its scalar model), at depths 8–11. None of them is a defect of the paper or of the frozen
root.

None of their modules (nor o283's) is in E or in any closure. The parents were either re-split
(o092 → s084) or superseded (o143/o204). The route does not rest on them or on weakened
replacements of the root: the root theorem is the challenge verbatim (byte comparison of
`Solution.lean`, comparator in the final check), and every obligation on the route is a closed,
accepted theorem.

Whether a replacement intermediate statement is "weaker" than a refuted one is irrelevant to
fidelity. The frozen root statement is faithful (§§1–3), so any kernel-checked proof of it with
standard axioms proves Theorem 1.1.

### 4.4 Forbidden constructs in E's `Submission` (grep over all 10,625 Submission sources)

| Construct | Result |
|---|---|
| `sorry`, `admit` | none in code. The only matches are four prose lines in docstrings ("admit a common convergent subsequence", and so on) and Root's docstring describing the split |
| `axiom` declarations | none |
| `implemented_by`, `@[extern]`, `unsafe`, `native_decide`, `decide := true`, `ofReduceBool`, `trustCompiler` | none |
| `opaque` | none as a keyword. Two matches are in comments |
| `#eval`, `run_cmd`, `run_tac`, `include_str`, `elabCommand`, `elab`/`macro`/`macro_rules`, `initialize`, `csimp`, `debug.*`/`skipKernelTC` options | none |
| `set_option` | only `autoImplicit`, `linter.*`, `maxHeartbeats` (333), `maxRecDepth` (109), `backward.isDefEq.respectTransparency` (42): elaboration options only |
| attributes | `simp`/`scoped simp`/`local simp`, `fun_prop`, `instance_reducible` (2), `irreducible` (1) |
| lean-pool imports | 4 (SardMoreira `MainTheorem`; NavierStokesAndEuler `LpParameterIntegral`; ZhangYeung/PFR entropy ×2). Permitted, and the transitive axiom check covers them |

**Q4 answer.** The final proof is the paper's proof, as listed in §4.1:
- the upper bound;
- the Theorem 2.17 reduction from an arbitrary Kakeya set, with outer measure and no compactness;
- Theorem 2.17's remaining paragraphs and the Sections 3–10 exclusion of bad problems;
- the four cited inputs, proved.

WZ is a genuine dependency. It supplies the 3D Kakeya union estimate and the planar dot-product
theorem, exactly where the paper cites them, plus a projection theorem and utilities. It is our
own proved library, compiled from source.

The proof exploits nothing in the formalization:
- the frozen statement has no junk-value branch to exploit (§3);
- the refuted intermediate statements were dropped, not used;
- the scan finds no unsafe or kernel-bypassing constructs.

## 5. Notes (none affects the verdict)

1. `config.json` has `"enable_nanoda": false` (the template default). The hardened
   `WorkspaceTest.lean` forces nanoda on, and so do the final checkers. `FINAL-CHECK.md` should
   state that nanoda ran.
2. The final check (`final-oai.py 074 all`) was still building when this was written (v10wz
   build at about 10,000/10,448 modules). My statements about axioms come from the source scan.
   The binding axiom and kernel verdict is `FINAL-CHECK.md`.
3. Pin: zhengyang's files target Lean v4.33.0 / Mathlib 6f1ef4e5. The proof is built and checked at
   our pin (v4.35.0-rc3 / 5e0c4e5), where the statement elaborates as shown in §2.2. Re-checking
   at his pin would be a separate backport.
4. Size and time:
   - Root's closure is about 1.36M lines, about 0.37M of them the inlined WZ library.
   - The tree ran from 2026-10-21T01:44Z until the root was accepted at 2026-10-22T20:30Z (about
     43 h). It ended at 20:47Z.

   The audit's question is fidelity, and the kernel check is what makes the size irrelevant to it.
5. The NOTICE line "Submission/WZ/ (2872 files)" and `WZLOT.json` "2,875 modules" are consistent.
   E holds only the WZ modules in the proof's import closure, which is the whole closure of
   `wz_tube_estimate` (2,872 modules).

## 6. Comparison with the phase-B review (`prep/074/FIDELITY.md`, read after the above)

Phase B and this audit agree on every row:
- arbitrary K;
- Euclidean `PiLp 2` and the round sphere;
- the `∀ e ∃ a` order;
- the closed segment via `segment_eq_image'`;
- `μH` as the countable-cover outer measure;
- `dimH` = inf{s : H^s = 0};
- `4 : ℝ≥0∞`;
- no `ChallengeDeps` definitions;
- the port touching only build files;
- the verdict "faithful".

There are no disagreements. One wording point and three additions:

- **Row 6 wording.** Phase B says "Mathlib omits the normalising constant; dimension is
  unaffected". The paper's covering definition (§1) has no normalising constant either, so `μH` is
  the paper's `H^s` exactly, not only up to a constant. The conclusion is unchanged.
- **Lean-checked, where phase B relied on grep and argument:**
  - `dimH K = ⨅ {d | μH[d] K = 0}` (Mathlib's `dimH_eq_iInf` at our pin; phase B derived it from
    two lemmas);
  - the covering formula for arbitrary sets;
  - the Euclidean norm and sphere, with a sup-norm discriminating pair;
  - the segment equivalence.
- **Lean-checked non-degeneracy beyond phase B's "`K = univ` satisfies `hK`":**
  - the closed ball satisfies the hypothesis and has `dimH = 4`;
  - every witnessing segment has `dimH = 1`;
  - the hyperplane `{x₃ = 0}` has segments in a great 2-sphere of directions and `dimH = 3`;
  - `¬ ∀ K, dimH K = 4`.
- **The final proof:**
  - the review of the route against the paper (§4.1);
  - the legitimacy, provenance and role of the inlined WZ library (§4.2);
  - the five refutations (§4.3);
  - the forbidden-construct scan (§4.4).

  Phase B predates the run, so none of this was in its scope.
