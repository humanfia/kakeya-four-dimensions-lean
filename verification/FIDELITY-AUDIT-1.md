# Problem 074: fidelity audit 1 (independent)

Problem: `oai_074_kakeya_four_dimensions`. Paper: OpenAI, *Every four-dimensional Kakeya set has
full Hausdorff dimension* (September 24, 2026), Theorem 1.1. Tree: `g-oai-074` on the wzlib Lean
set. Per `result.json` and `tree.json` it started 2026-10-21T01:44:08Z, the root was accepted at
2026-10-22T20:30:37Z (about 42.8 h) and the tree ended `proved` at 20:36:24Z.
- Root commit X: `e18a9d88893ffcab5d04f3eaea93f240c663a088`.
- Judged export E: `71391e12db6f5956b54bcdb01a6b1ceeba11604d`. E is X with the WangZahlLot
  package inlined under `Submission/WZ/` and unused files pruned.
- The final check (two isolated checkers with nanoda forced on, plus an independent recompile with
  `#print axioms`) was still running while I wrote this (`check-v10wz.log` at about module
  9890/10448). I did not wait for it. Its report will be `final/074/FINAL-CHECK.md`.

Audit date: 2026-10-22. Auditor 1. I did not read `FIDELITY-AUDIT-2.md`, and I did not open the
`fidelity-audit-2/` directory. I read the Phase-B review `prep/074/FIDELITY.md` only after I had
formed my own view; §6 compares the two.

## Verdict: **FAITHFUL**

The Lean statement (`Challenge.lean` + `ChallengeDeps.lean`, which is only `import Mathlib`) is a
word-for-word formalization of Theorem 1.1. In words: if K ⊂ ℝ⁴ is arbitrary and for every e ∈ S³
there is a_e with {a_e + te : 0 ≤ t ≤ 1} ⊂ K, then dim_H K = 4.

- **Same objects as the paper.**
  - K is an arbitrary set, with no measurability or compactness hypothesis.
  - The space is ℝ⁴ with the Euclidean metric (`PiLp 2`, seen in the elaboration).
  - Directions range over every e on the Euclidean unit sphere S³.
  - Each direction has a closed unit segment.
  - The conclusion is Hausdorff dimension, with value `(4 : ℝ≥0∞)`.
- **Equivalence proved in Lean (W4).** I wrote `PaperThm`, the theorem in the paper's own terms:
  - unit vectors given by Σeᵢ² = 1;
  - segments written as {a + te : t ∈ [0,1]};
  - 𝓗^s given by the paper's countable δ-cover formula;
  - dim_H K = inf{s : 𝓗^s(K) = 0}.

  `paper_iff_challenge : PaperThm ↔ type_of% @kakeya_four_dimensions` compiles with the standard
  axioms only.
- **Non-degeneracy (Lean witnesses W1–W6).** The sphere is the Euclidean one, not the sup-metric
  one. Each segment has diameter exactly 1 and dimension 1. The hypothesis is satisfiable (closed
  unit ball, `univ`). The conclusion is non-trivial: a point and the coordinate hyperplane
  (dimH ≤ 3) fail the hypothesis. Unit segments in only countably many directions give dimH ≤ 1,
  so "every direction" is essential.
- **Nothing makes the statement easier.** No Mathlib convention weakens it. Mathlib's 𝓗^s is the
  paper's covering formula on every set (no measurability). It has no normalising constant, and
  neither has the paper's. Mathlib's `dimH_eq_iInf` is literally the paper's definition of dim_H.
- **The proof mirrors the paper and does not exploit the formalization.** The root is
  `le_antisymm (dimH ≤ 4) (Thm 2.17's outer-measure reduction ∘ k4_core)`.
  - `k4_core` takes the paper's four cited analytic inputs as hypotheses: the weighted plank lemma,
    Carbery–Valdimarsson, Orponen–de Saxcé–Shmerkin and graph BSG. All four are proved in Lean.
  - The 3-D input enters through the inlined WangZahlLot library. That library is our own proved
    Wang–Zahl tree, and its use is genuine (§5.3): the Wang–Zahl/GWZ set estimate E(0,0) feeds the
    plank lemma, and WZ's projection dichotomy is the paper's planar input, Theorem 5.5.
  - Outside comments, no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`,
    `unsafe`, `opaque` or compile-time evaluation occurs anywhere in E's `Submission` (10,624
    files, WZ included; §5.2).
  - None of the five refuted obligations, and none of the 50 superseded ones, has a module in E.

Caveats. None of them affects the verdict.
- (i) **Final check pending.** This audit is about the statement and the proof's route. It does
  not replace the final check. The verdict on the *proof* depends on FINAL-CHECK.md (both checkers
  pass, `#print axioms` gives `[propext, Classical.choice, Quot.sound]`).
- (ii) **Pin.** Everything was checked at our pin (Lean v4.35.0-rc3, Mathlib 5e0c4e5). zhengyang's
  lean-problem targets Lean 4.33.0 / Mathlib 6f1ef4e5. The statement files are byte-identical to
  his, but proof validity at his pin was not checked.
- (iii) **The paper is an unrefereed preprint.** The Lean proof formalizes the argument itself and
  all the inputs the paper cites (GWZ via WZ, CV, OdSS, BSG, semialgebraic selection). The formal
  theorem therefore does not rest on the paper's correctness. This is an observation about the
  proof, not a fidelity issue.

## 1. Sources read

- **Statement.** `/home/ubuntu/lean-runs/lean-gap/workspaces/oai_074_kakeya_four_dimensions/`
  `{Challenge.lean, ChallengeDeps.lean, Solution.lean, Submission.lean, holes.json, config.json, PROBLEM.md, README.md, lakefile.toml}`.
  - `Challenge.lean` (sha256 `bf8e140c…`) and `ChallengeDeps.lean` (`c1a46df9…`) are byte-identical
    to zhengyang's `lean-problem/` (`diff`).
  - They are also identical to E's copies. E's `Solution.lean`, `config.json`, `holes.json`,
    `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `WorkspaceTest.lean`, `README.md`,
    `PROBLEM.md` and `.gitignore` are all byte-identical to the workspace (sha256 compared).
- **Paper TeX** (read-only; I listed only `074-kakeya-four-dimensions/` and its direct
  subdirectories):
  `/mnt/data/zhengyang-workspace/openai-math-lot-pdfs/074-kakeya-four-dimensions/source-…/build/`.
  - Read in full: `paper.tex` and `sections/01-introduction.tex`. The latter has Theorem 1.1 and
    the covering definition of 𝓗^s and dim_H.
  - Read: `02-framework.tex` lines 880–1300, i.e. `lem:weighted-planks` and Theorem
    `thm:model-reduction` (its "finite selection from outer measure" paragraph and the start of
    the smoothing).
  - Read: `09-unbounded-narrowness.tex` lines 1180–1230, the proof of Theorem 1.1.
  - The PDF was only listed, not opened.
- **Final proof.** I read E from the read-only copy
  `final/074/20261022T204723Z/copy/g-oai-074/oai_074_kakeya_four_dimensions`, using only
  `git ls-tree`, `git show`, `git grep`, `git diff` and `git archive`.
  - Read: `Submission.lean`, `Submission/Obl/Root.lean`, `Submission/Seed/K4/Basic.lean` and the
    six root children (`k4_lower_of_discrete`, `k4_plank_estimate`, `k4_multilinear_kakeya`,
    `k4_oss_decay`, `k4_graph_bsg`, `k4_core`).
  - Also read: `Obl/k4_lower_of_discrete/Localization.lean`, `Lib/KakeyaCovering/GraphReduction.lean`,
    `Obl/k4_plank_estimate/SetEstimate.lean`, `Obl/k4_scalar_tangent_isotropic_improvement/RepairedCut.lean`,
    `Obl/k4_isotropic_path_improvement.lean`, and `NOTICE` and `LICENSES/wang-zahl-lot/*`.
- **Tree state.** Read-only on `/home/ubuntu/lean-runs/lean-gap/lot/g-oai-074/oai_074_kakeya_four_dimensions/.hmz/lot/`:
  - `tree.json`, read with python: obligations, splits, refutations, final;
  - `result.json`;
  - `events.jsonl`, grep only, around the o106 landing;
  - the six refutation text blobs and verdict blobs in `archive/blobs/`.

  Nothing was written there. The tree was neither resumed nor stopped.
- **wzlib.** `trusted-v10wz/oai_074_kakeya_four_dimensions/inline.json` and
  `prep/074/wzlib/pkg/WangZahlLot/` (WZLOT.json and NOTICE). I spot-checked 303 randomly chosen
  inlined `Submission/WZ/**` files against the package sources (§5.3).
- **Plans and prep, read before forming a view:** `PLAN-074.md` §0–§2 and `prep/074/README.md`.
  `prep/074/FIDELITY.md` I read only after §§2–5 were drafted.

## 2. Question 1: is the Lean statement equivalent to Theorem 1.1?

**Paper, Theorem 1.1** (`01-introduction.tex` l. 8–16): Let K ⊂ ℝ⁴. Suppose that for every
e ∈ S³ there is a point a_e ∈ ℝ⁴ such that {a_e + te : 0 ≤ t ≤ 1} ⊂ K. Then dim_H K = 4.

The paper's conventions follow at l. 17–31:
- "Neither K nor the choice of its witnessing segments is required to be measurable."
- 𝓗^s_δ(K) = inf{Σ(diam U_i)^s : K ⊂ ⋃U_i, diam U_i ≤ δ} over countable covers.
- 𝓗^s = lim_{δ↓0} 𝓗^s_δ.
- dim_H K = inf{s : 𝓗^s(K) = 0}.
- "This definition requires no measurability assumption."

**Elaborated Lean statement** (`Elab.lean`, `pp.numericTypes`; output in §7):

```
kakeya_four_dimensions : ∀ (K : Set (EuclideanSpace ℝ (Fin (4 : ℕ)))),
  (∀ e ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (4 : ℕ))) (1 : ℝ), ∃ a, segment ℝ a (a + e) ⊆ K) →
    dimH K = (4 : ENNReal)
```

| Item | Paper | Lean | Verdict |
|---|---|---|---|
| Set | K ⊂ ℝ⁴ arbitrary, no measurability or compactness | `K : Set (EuclideanSpace ℝ (Fin 4))`, no hypothesis on K | same |
| Space and metric | ℝ⁴ with Euclidean diam | `EuclideanSpace ℝ (Fin 4)` = `PiLp 2`. `pp.explicit` shows `PiLp.instPseudoMetricSpace 2 …` for the sphere and `PiLp.instEMetricSpace 2 …` for `dimH`. **W1** shows Σeᵢ² = 1 ⇔ e ∈ sphere, and contrasts this with the sup metric | same |
| Directions | every e ∈ S³ | `∀ e ∈ Metric.sphere 0 1`, the Euclidean unit sphere (W1) | same |
| Witness point | a_e ∈ ℝ⁴, with no regularity of e ↦ a_e | `∃ a` inside `∀ e` | same |
| Segment | {a_e + te : 0 ≤ t ≤ 1}, closed, length 1 | `segment ℝ a (a + e)` (`WithLp.instSMul`, `WithLp.instAddCommGroup`: the coordinatewise vector-space structure). **W2**: it equals `(fun t => a + t • e) '' Icc 0 1`; for e ∈ S³ its `diam` is exactly 1 and its `dimH` is 1 | same |
| 𝓗^s | countable δ-covers, Σ(diam U_i)^s, lim δ↓0, defined on all sets | `μH[s] K` = `Measure.hausdorffMeasure s K`. `hausdorffMeasure_apply` holds for every set K: `⨆ r>0, ⨅ covers t : ℕ → Set, K ⊆ ⋃ t n, ediam (t n) ≤ r, ∑' ⨆ (t n).Nonempty, ediam (t n)^s`. **W3** `paperH_eq` | same (empty pieces contribute 0; no normalising constant on either side) |
| dim_H | inf{s : 𝓗^s(K) = 0} | `dimH` (defined as `⨆ d, ⨆ μH[d] K = ∞, d` under `borelize`). Mathlib's `dimH_eq_iInf` gives `dimH K = ⨅ (d : ℝ≥0) (_ : μH[d] K = 0), d`. **W3** `paperDim_eq` | same |
| Value | dim_H K = 4 | `dimH K = (4 : ENNReal)`; **W5** gives `dimH univ = 4` | same |
| Quantifiers | ∀K, (∀e ∃a_e …) ⇒ dim = 4 | `∀ K, (∀ e ∈ S³, ∃ a, …) → dimH K = 4` | same |

**W4 (formal equivalence).** `PaperThm` restates Theorem 1.1 with only the paper's notions:
- unit vectors as Σ (e.ofLp i)² = 1;
- segments as ∀ t ∈ [0,1], a + t•e ∈ K;
- `paperH`, the covering formula;
- `paperDim`, the infimum definition.

Lean proves `PaperThm ↔ type_of% @kakeya_four_dimensions`. `#check` shows that the right-hand side
is the frozen theorem's type, and the proof uses only `[propext, Classical.choice, Quot.sound]`.
`type_of%` reads only the type, so the sorried constant is not used.

Conclusion for Q1: **equivalent** to Theorem 1.1, not merely at least as strong.

## 3. Question 2: are the definitions standard, non-vacuous and non-degenerate?

### 3.1 Standard

- `ChallengeDeps.lean` is `import Mathlib` plus a docstring. It defines nothing, so there are no
  trusted definitions to audit (`config.json` has no `definition_names`).
- `EuclideanSpace`, `Metric.sphere`, `segment` and `dimH` are standard Mathlib definitions. Their
  elaborated instances are the expected ones (§7: `PiLp` with p = 2, `WithLp` module structure).
- The definition of `segment` is `{z | ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a • x + b • y = z}`
  (`#print segment`). It is closed, contains both endpoints, and equals the paper's parametrisation
  (W2 `segment_eq`).

### 3.2 Not vacuous and not degenerate (Lean witnesses; Appendix A)

| Witness | Content |
|---|---|
| W1 `mem_sphere_iff`, `u_mem`, `u_sup`, `w_not_mem`, `w_sup` | e ∈ sphere ⇔ Σeᵢ² = 1. u = (½,½,½,½) is on the frozen sphere, but its sup norm is ½. w = (1,1,0,0) has sup norm 1 but is not on the frozen sphere. So the sphere is Euclidean, not the sup-metric one. |
| W2 `segment_eq`, `segment_diam`, `segment_dimH` | `segment ℝ a (a+e) = {a + t e : t ∈ [0,1]}`. For e ∈ S³ it has `diam = 1` and `dimH = 1`, so it is a genuine unit segment and never degenerate. |
| W3 `paperH_eq`, `paperDim_eq` | Mathlib's μH and dimH are the paper's covering definitions for **arbitrary** K. |
| W4 `paper_iff_challenge` | Paper Theorem 1.1 (paper definitions) ⇔ frozen type. |
| W5 `closedBall_hyp`, `univ_hyp`, `dimH_closedBall4`, `dimH_univ4` | The hypothesis is satisfiable, by the closed unit ball (a = 0) and by `univ`. These sets have `dimH = 4`, so the statement is consistent and the hypothesis is not contradictory. |
| W6 `point_fails`, `dimH_point`, `hyperplane_fails`, `dimH_hyperplane_le`, `hyperplane_conclusion_fails`, `countable_directions` | `dimH {0} = 0` and the coordinate hyperplane {x₀ = 0} has `dimH ≤ 3`. Both fail the hypothesis: no segment in direction (1,0,0,0) fits. So the conclusion `= 4` is not a tautology, and the hypothesis must exclude low-dimensional sets. Also ⋃ₙ segment(aₙ, aₙ+eₙ) has `dimH ≤ 1` for **any countable** family of directions, e.g. a dense countable subset of S³. So the hypothesis "every e ∈ S³" is used essentially; it cannot be weakened to a countable or dense set of directions. |

All 20 witness theorems compile with exit 0 and no warnings, and depend only on
`[propext, Classical.choice, Quot.sound]` (§7).

### 3.3 Mathlib conventions checked

| Concern | Finding |
|---|---|
| Measurability of K | Not required. `hausdorffMeasure_apply` and `dimH_eq_iInf` hold for every `s : Set X`. `dimH` is defined with `borelize X`, so it does not depend on the ambient `MeasurableSpace` instance. |
| Hausdorff normalisation | Mathlib's `μH[d]` has no ω_d/2^d constant. The paper's 𝓗^s has none either, and dimension does not depend on it anyway. |
| Empty sets and diameter 0 in covers | Mathlib uses `⨆ _ : (t n).Nonempty, ediam^s`, so empty pieces contribute 0. Points contribute 0^s = 0 for s > 0. This matches the paper's convention and only matters at s = 0, far from s ∈ (3,4). |
| `ℝ≥0` vs real exponents | `dimH` takes its sup/inf over `d : ℝ≥0`; the paper's s ranges over s ≥ 0 implicitly. Same. |
| The value `4` | `(4 : ENNReal)` via `instOfNatAtLeastTwo` (pp.explicit). `dimH` of any subset of ℝ⁴ is finite (`Real.dimH_lt_top`), so no `∞` corner case arises. |
| Sphere vs sup metric | Euclidean (W1). Hausdorff dimension is bi-Lipschitz invariant, so the metric matters only for the direction set and segment length, and those are the paper's. |
| e vs −e | `segment ℝ a (a+e) = segment ℝ (a+e) ((a+e) + (−e))`, so the condition for e implies it for −e, as for paper directions. |
| Submission-side overrides | E's `Submission` has no global `instance`. The only attribute changes are four file-local `attribute [-instance] Nat.decidableForallFin …`. There are no `notation`/`macro` hacks on the statement's symbols. In any case the comparator compares kernel-level types of `Challenge` and `Solution`. |
| Protected files | Byte-identical in the starter workspace, zhengyang's lean-problem and E (§1). |

Conclusion for Q2: the definitions are **standard, non-vacuous and non-degenerate**.

## 4. Question 3: anything that makes the statement easier than intended?

No.
- **No compactness or measurability is added.** The 3-D WangZahlLot problem's `IsKakeya` requires
  compactness, but it is not part of this statement. The 4-D proof uses WZ only for finite and
  discretized estimates, never for the compact 3-D set theorem (§5.3).
- **Every direction is required.** W6 shows that weakening the hypothesis to countably many
  directions would make the conclusion false.
- **The segments are closed, of length exactly 1, and non-degenerate (W2).**
- **The upper bound `dimH K ≤ 4` is trivial in both versions.** The seed proves it in two lines.
  The content of the theorem is `4 ≤ dimH K` for arbitrary K, which is the full four-dimensional
  Hausdorff Kakeya conjecture. It is strictly beyond Wolff's 3, Katz–Zahl's 3.059 and the other
  bounds in paper §1.1.
- **No Mathlib convention makes the claim cheaper.** There is no junk value: `dimH` is a genuine
  sup/inf over Hausdorff measures, finite on ℝ⁴. There is no measurability side condition, and no
  normalisation issue.

## 5. Question 4: the final proof's top level

### 5.1 Root and its six children

`Submission/Obl/Root.lean` (identical in X and E):

```lean
theorem kakeya_four_dimensions (K …) (hK …) : dimH K = 4 :=
  le_antisymm (Submission.Seed.K4.dimH_le_four K)
    (k4_lower_of_discrete
      (k4_core k4_plank_estimate k4_multilinear_kakeya k4_oss_decay k4_graph_bsg)
      K hK)
```

`Submission.lean` imports `Submission.Obl.Root` and every obligation module. `Solution.lean`
(unchanged) closes the challenge by `Submission.kakeya_four_dimensions K hK`.

| Obligation | Paper | Lean content |
|---|---|---|
| seed `dimH_le_four` | "ambient upper bound" | `dimH_mono` + `Real.dimH_univ_eq_finrank` + `finrank_euclideanSpace_fin`. |
| o001 `k4_lower_of_discrete` (R2): DK4 → ∀ K, hK → 4 ≤ dimH K | Thm 2.17 (`thm:model-reduction`), ¶ "A finite selection from outer measure" | **Localization.** `exists_graph_localization` uses `choose` to pick a witness for each graph-slope direction (arbitrary K) and finds a slope set S ⊂ ℝ³ of positive **outer** measure with a common time window and intercept box. An affine 2-Lipschitz map y ↦ 2y − w normalises.<br>**Covering.** `four_le_dimH_of_bounded_graph_family`: dimH K < 4 ⇒ μH[s] K = 0 for some s ∈ [3,4) ⇒ countable ball cover with Σr^s small. Outer-measure pigeonhole gives a productive dyadic scale k with time fraction ≥ c/(k+1)², and a 2^{−k}-separated slope family comes from WZ's `exists_finset_separated_cover`. This contradicts DK4.<br>This is exactly the paper's paragraph. Measurability is never assumed. |
| o002 `k4_plank_estimate` (T1) | Lemma 2.15 `lem:weighted-planks` = Lemma 2.3 of OpenAI's 3-D maximal paper (from GWZ Thm 1.1) | `unweighted_set_estimate` derives the 3-D convex-clustered set estimate from **WZ's `wz_endpoint_bootstrap` E(0,0)**, the Wang–Zahl set estimate, together with WZ's `pointwise_dense_estimate` and `frostman_of_katz`. Then o010 `k4_weighted_convex_tubes` (weighted convex clustering) and o011 `k4_plank_tube_realization` (planks as tubes) give the weighted plank bound. |
| o003 `k4_multilinear_kakeya` (T3) | (6.10) `a05:determinant-kakeya`, Carbery–Valdimarsson | n = 2 by a two-strip estimate. For n = 3, 4: visibility, via o012/o021/o022/o046/o047 (polynomial ham sandwich, arctan-variation tube bounds), then o013 finite duality, o014 lattice-to-Lebesgue transfer and scaling. |
| o004 `k4_oss_decay` (T4) | (7.10) `re:oss-input`, Orponen–de Saxcé–Shmerkin; the special case Lemma 7.4 uses | Bourgain's route: o023 collision Cauchy–Schwarz, o024 projection flattening (o041–o043, o058–o061; uses WZ's Frostman graph-projection counting), o025 flat decay, o026 unit decay (o045), and o027 dyadic reduction. |
| o005 `k4_graph_bsg` (T5) | Lemma 7.1 `re:graph-bsg` | Graph BSG with retained edges, with explicit c = 1/36 and C₀ = 6144. Built on WZ's Furstenberg/Katz–Tao path lemma. |
| o006 `k4_core` (R3core): T1 ∧ T3 ∧ T4 ∧ T5 → DK4 | Thm 2.17 ¶2 onward, §§3–10 | Glue of three children:<br>– o007 `k4_quadratic_slope_volume` (Thm 2.17 (2.34)), via semialgebraic selection o019/o028–o031 and bounded fibre volume o020;<br>– o008 `k4_algebraic_sheet_bound` (Lemma 3.1);<br>– o009 `k4_core_from_geometric_bounds`. Under it sit two-color matching (o015, Lemma 3.3), scalar coefficient clustering (o016, Lemma 5.1), real-conic restoration (o017, Lemma 6.7), and the framework o018 → o048/o049 down to depth 12 (critical paths, isotropic case, retained-edge rigidity, finite and unbounded narrowness, critical rates).<br>The planar input (Thm 5.5 `a04:planar-input`) is `WangZahlLot.wz_ad_projection_dichotomy`. |

**Size.** E's `Submission/` holds 10,624 Lean files:
- `Obl/`: 7,231 files, 933,872 lines;
- `Lib/`: 519 files, 76,727 lines;
- `Seed/`: 1 file, 70 lines;
- `WZ/`: 2,872 files, 370,727 lines.

**Tree.** `tree.json` has 296 obligations: 241 accepted (root included), 50 superseded and 5
refuted. Maximum depth is 12. E contains exactly 235 accepted obligation modules plus `Root`. The
other 5 accepted obligations (o248, o265, o289, o290, o291) lie under superseded ancestors and were
pruned from the export. No refuted and no superseded obligation has a module in E.

### 5.2 Forbidden constructs (grep of every blob of E under `Submission/` and `Submission.lean`)

- `sorry`: one hit, in a doc comment of `Root.lean` ("The only `sorry`s it depends on are the six
  children…", stale prose from the preset glue).
- `admit`: 15 hits, all the English word in doc comments ("… admit a measurable choice").
- `axiom`: one hit, in a comment ("no new axiom is introduced").
- `opaque`: two hits, in comments.
- `import Lean…`: four hits, all `import LeanPool.*`:
  - `NavierStokesAndEuler…LpParameterIntegral`;
  - `ZhangYeungInequality…Entropy`, two files;
  - `SardMoreira.MainTheorem`.

  These are generic analysis, entropy and Sard tools. Their axioms fall under the transitive check.
- Zero hits: `implemented_by`, `extern`, `unsafe`, `native_decide`, `decide +kernel`,
  `ofReduceBool`, `trustCompiler`, `#eval`, `run_cmd`, `run_tac`, `run_elab`, `include_str`,
  `elabCommand`, `initialize`, `csimp`, `partial def`, `addDecl`, `debug.skipKernelTC`,
  `macro_rules`, `elab`, `Lean.Elab`.
- Global `instance` declarations: none (every grep hit is in prose).

### 5.3 The inlined WangZahlLot: genuine dependency, verified from source

- **What it is.** `Submission/WZ/` holds the 2,872 modules of WangZahlLot that the proof imports,
  plus their import closure.
  - WangZahlLot is our own proved LOT tree `g-wang_zahl_kakeya_dimH`, at root lib commit
    `da2150fe…` (proved 2026-10-13; Lean-Eval #2121 per NOTICE).
  - Its only change is the mechanical rename `Submission` → `WangZahlLot` (WZLOT.json).
  - In E the module paths are renamed `WangZahlLot.*` → `Submission.WZ.*`. Declaration names keep
    `WangZahlLot.*`.
  - Each file carries two provenance comment lines.
- **It is identical to the package.** I spot-checked 303 inlined files: 300 random, plus
  `wz_tube_estimate`, `wz_ad_projection_dichotomy` and `ChallengeDeps`. After removing the two
  header lines and undoing the import rename, all 303 are byte-identical to
  `prep/074/wzlib/pkg/WangZahlLot/WangZahlLot/`.
- **X → E changes nothing else.** Besides additions and pruning deletions, X → E modifies 27
  Submission files. The only changed lines are 36 WZ `import` lines (removed and re-added under
  the new module name).
- **It is built from source.** The final checker builds the WZ modules from these sources inside
  E (`check-v10wz.log` shows `Built Submission.WZ.…`). WZ's axioms are therefore covered by the
  same transitive check. It is not trusted as prebuilt oleans in the final check.
- **The use is genuine, not plumbing.**
  - *Deep input 1:* `WangZahlLot.wz_endpoint_bootstrap` (E(0,0), the Wang–Zahl/GWZ union
    estimate) feeds T1, via `Obl/k4_plank_estimate/SetEstimate.lean`. This is the paper's only
    use of 3-D Kakeya: its weighted plank Lemma 2.15 is cited from the 3-D maximal paper's Lemma
    2.3, which rests on GWZ Thm 1.1.
  - *Deep input 2:* `WangZahlLot.wz_ad_projection_dichotomy` (WZ o103) is the paper's planar
    dot-product Theorem 5.5 (Wang–Zahl sticky restricted triples). It is used in
    `k4_scalar_normal_first_jet` (`scalar_projection_input`) and in
    `k4_horizontal_interior_parameter_bootstrap`.
  - *Utilities:*
    - covering, dyadic and packing lemmas from WZ's `kakeya_three_le_dimH_of_tube_estimate`;
    - the Katz–Tao path lemma (for BSG);
    - Frostman graph-projection counting (OdSS);
    - `wz_slab_local_linearity` covers (scalar jets);
    - polynomial zero-set nullity (ham sandwich);
    - Wongkew (isolated points);
    - convex test families and tube volumes (weighted convex tubes).
- **No compactness leaks in.** WZ's `IsKakeya` (compact 3-D sets) is not used anywhere outside
  `Submission/WZ/` (grep: no `LeanEval.`/`IsKakeya` references in `Obl`, `Lib` or `Seed`). WZ's
  own root theorem (3-D dimH) is not even in E's import closure.

### 5.4 The refuted obligations

Six refutation claims were filed, all "model" (informal) and confirmed by a separate verifier
session. None is a Lean refutation. Five obligations ended with state `refuted`. o283 was already
superseded when its claim settled.

| Claim | Obligation (depth) | Why false (verifier's summary) | What replaced it |
|---|---|---|---|
| g00347 (10-21 05:31Z) | o137 `k4_scalar_physical_parameter_preparation` (8), split s048 of o092 | It demands coefficient-bin floors at **every real width r** (non-nested bins `⌊l/N^{-r}⌋`). A shear-trajectory example with C = 1 − N⁻² makes all bins at a continuum of widths null. The paper uses aligned dyadic bins. | s048 rejected. o092 re-split as s084 (o228–o231, all accepted). `RepairedCut.lean` records the same six statements with the floors required only on a grid r = m/M(k), i.e. the paper's nested bins. |
| g00961 (10-21 23:07Z) | o285 `k4_original_interpolated_field_source` (11), under o265 | A Cantor-digit hidden law satisfies every frozen hypothesis but defeats the field-packet clause (a frozen derivative is affine in U while the row prediction is independent of U). | o265 re-split (s108). The whole o204 subtree was later superseded (below). |
| g00977/g00978 (10-22 03:07Z) | o283 (11) / o267 `k4_original_potential_reference_completion` (10) | A tilted digit-tree configuration, globally γ-narrow with full hidden law near every tested level, meets all hypotheses while excluding the Width and Candidate exits. Margins are 0.000054 Ξ and 0.0013 Ξ. | o204 re-split (s109), then superseded. |
| g00996/g00997 (10-22 06:30Z) | o292 `k4_narrow_atlas_breadth_ladder` (11) / o266 `k4_narrow_original_potential_atlas` (10) | The same counterexample with a modified middle-level test (and, for o292, a triangle-wave tangent velocity). The menu size is forced ≥ N^{0.118e} > N^{α}. | as above |

- **Where the defects lay.** All five are statement defects of *internal* frozen children. Some
  children were over-strong, with quantifiers at non-nested real widths. Others had
  slack/quantifier orders that admit digit-tree counterexamples. They are not defects of the paper
  or of the root.
- **How the defects were removed from the route.** o106 `k4_isotropic_path_improvement` was proved
  directly at 2026-10-22T18:07Z, by x1078 (slot B). Its own folder ports a source tree that proves
  o265's statement, plus the glue o106 ≤ o265. That superseded o116 → o143 → o204 and with them
  every subtree containing o266, o267, o283, o285 and o292 (events: "superseded o116, o143, o204:
  o106 was proved on its own first").
- **Does the accepted route rely on a weakened statement? No.**
  - No refuted or superseded module is in E. Their names occur in E only in provenance comments of
    reused helper files (e.g. "Original file: Submission/Obl/k4_uniform_sampled_isotropic_branches/…").
    There they appear as namespaces or comments, never as the frozen theorems.
  - More fundamentally, every child on the route is a proved theorem. The root's type is
    byte-identical to the challenge. A false or weakened intermediate statement could influence
    the root only if it were *assumed*, and E contains no `sorry` and no `axiom`. The checkers
    enforce the three standard axioms transitively.
  - The repaired versions match the paper: the o137 fix uses nested dyadic grids, as the paper
    does.

### 5.5 Does the proof exploit the formalization? No.

- **The root is pure glue.** The upper bound is the ambient one. The lower bound is the paper's
  architecture:
  - Theorem 2.17's reduction from an arbitrary Kakeya set to a discrete bad-configuration
    statement, with outer measure and finite selection;
  - the exclusion of bad configurations (§§3–10);
  - the paper's cited inputs, each one an explicit child.
- **The reduction handles non-measurable K exactly as the paper does.** It uses outer measure of
  the slope set (`volume S ≠ 0` for an arbitrary S) and `choose` for witnesses (global choice is
  one of the permitted axioms). It uses Mathlib's `hausdorffMeasure_of_dimH_lt` and a countable
  ball cover, with no junk values.
- **No step relies on a degenerate reading of the statement.** The segments are genuine unit
  segments (W2). dimH is the genuine one (W3). The hypothesis cannot be met by low-dimensional
  sets (W6).
- **External code.** Four files import generic lean-pool modules. NOTICE attributes one adapted
  file (`ConicKernels.lean`, from LeanPool.MetricCodes) and the WZ library.
- **Observation, not a defect.** The formal proof goes beyond the paper. The paper cites GWZ Thm
  1.1 (via the 3-D maximal paper), Carbery–Valdimarsson, OdSS Thm 1.5, Wang–Zahl's planar theorem,
  graph BSG and semialgebraic selection. All of these are proved in Lean here, the first and the
  planar theorem through our WZ library. The size (about 1.0M new lines plus 371k WZ lines) and the
  speed (about 43 h) do not bear on fidelity: the statement is byte-identical, and the proof is
  kernel-checked (pending FINAL-CHECK.md).

## 6. Comparison with the Phase-B review (`prep/074/FIDELITY.md`), read after §§2–5

- **Agreement.** I agree with every row of its table: arbitrary K, the PiLp 2 Euclidean metric,
  the Euclidean unit sphere, `∃ a` inside `∀ e`, the closed segment via `segment_eq_image'`,
  `hausdorffMeasure_apply` on all sets, the inf characterisation of dimH, and `4 : ℝ≥0∞`. I also
  agree with its "not vacuous (K = univ)", "not weaker" and "not stronger".
- **Refinement 1 (row 6).** Phase B says "Mathlib omits the normalising constant". This is true,
  but the paper's own covering definition (l. 25–29) has no normalising constant either. The two
  definitions are therefore *identical*, not merely dimension-equivalent. W3 shows this formally.
- **Refinement 2 (row 7).** Phase B derives the inf characterisation from
  `hausdorffMeasure_of_lt_dimH` and `hausdorffMeasure_of_dimH_lt`. The pinned Mathlib has it
  directly as `dimH_eq_iInf`, which W3 and W4 use.
- **Refinement 3 ("conclusion not trivial").** Phase B asserted this in prose. W6 proves it with a
  point and a 3-dimensional hyperplane. W6 also shows that "every direction" is essential:
  countably many directions allow dimH ≤ 1.
- **Disagreements.** None on the root statement. Phase B's port table and preset-children notes are
  about the split, not the root, and I did not re-audit them. The tree later found five internal
  frozen children false (§5.4). None was a preset child and none is on the final route.
- **What this audit adds:**
  1. a formal equivalence (W4) between the frozen type and Theorem 1.1 stated with the paper's own
     definitions;
  2. the non-degeneracy witnesses W1, W2, W5 and W6;
  3. `pp.explicit` elaboration of the sphere, segment and dimH instances;
  4. the analysis of the final proof's route, of the WZ dependency (spot-checked byte identity,
     built from source) and of the five refutations.

## 7. Lean runs made for this audit (read-only deps, docker)

- **Container setup.** Image `deuring-runner:1`, `--network none`, `--user 1000:1000`, 4 CPUs,
  16 GB (`--memory 16g --memory-swap 16g`), `LEAN_NUM_THREADS=4`.
- **Mounts.**
  - Read-only: `~/.elan` and the sealed deps `deps/mathlib-5e0c4e5/.lake/packages`.
  - Writable: only this audit directory (`final/074/fidelity-audit-1`, as `/work`).

  Lean was run directly (`lean …`, `LEAN_PATH` set). There was no lake, no `check.sh`, no
  comparator and no git. The script is `final/074/fidelity-audit-1/run-in-docker.sh`. Each
  container is named `oai074audit1-<pid>`, started with `--rm`, and removed by exact name if
  anything remains.
- **Statement oleans.** `src/ChallengeDeps.lean` and `src/Challenge.lean` are byte copies (sha256
  `c1a46df9…` / `bf8e140c…`). I compiled them into `build/` with `lean --root=/work/src -o … -i …`.
  `Challenge` warns `declaration uses 'sorry'`, as expected.
- **Containers.** `oai074audit1-2855812` (ChallengeDeps), `oai074audit1-2856248` (Challenge),
  `oai074audit1-2857072` (Elab), then `oai074audit1-2861256`, `-2861888` and `-2862663` (Witness:
  two tries with `norm_num` placement errors, then exit 0), and a final rerun of Witness with an
  added `#check`. `docker ps -a` shows no `oai074audit1*` container.
- **Deps digest** (`sha256sum …/packages/*/.git/index | sha256sum | cut -c1-8`): **7f64b9cb**
  before the first run and after the last. Neither tree nor the running final check was touched.

Results:
- `Elab.lean`: exit 0. Output `Elab.log` (sha256 `852693d8…`). Excerpts; the three `pp.explicit`
  lines are abridged (numerals shown as digits, instance proofs and repeated arguments elided):

```
kakeya_four_dimensions : ∀ (K : Set (EuclideanSpace ℝ (Fin (4 : ℕ)))),
  (∀ e ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (4 : ℕ))) (1 : ℝ), ∃ a, segment ℝ a (a + e) ⊆ K) →
    dimH K = (4 : ENNReal)
@Metric.sphere (EuclideanSpace Real (Fin 4)) (@PiLp.instPseudoMetricSpace 2 (Fin 4) (fun x => Real) … fun i => Real.pseudoMetricSpace) 0 1
@segment Real (EuclideanSpace Real (Fin 4)) … (@WithLp.instAddCommGroup 2 …) (@WithLp.instSMul 2 Real …) a (a + e)
@Eq ENNReal (@dimH (EuclideanSpace Real (Fin 4)) (@PiLp.instEMetricSpace 2 (Fin 4) … ) K) (@OfNat.ofNat ENNReal 4 (instOfNatAtLeastTwo …))
def segment … := fun 𝕜 {E} … x y => {z | ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a • x + b • y = z}
@dimH_eq_iInf : … (s : Set X), dimH s = ⨅ d, ⨅ (_ : μH[↑d] s = 0), ↑d
@Measure.hausdorffMeasure_apply : … (d : ℝ) (s : Set X), μH[d] s = ⨆ r, ⨆ (_ : 0 < r), ⨅ t, ⨅ (_ : s ⊆ ⋃ n, t n),
    ⨅ (_ : ∀ (n : ℕ), Metric.ediam (t n) ≤ r), ∑' (n : ℕ), ⨆ (_ : (t n).Nonempty), Metric.ediam (t n) ^ d
@EuclideanSpace.norm_eq : … ‖x‖ = √(∑ i, ‖x.ofLp i‖ ^ 2)
'kakeya_four_dimensions' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]   -- the unfilled challenge, expected
```

- `Witness.lean`: exit 0, no warnings. Output `Witness.log` (sha256 `7be923ce…`):

```
'Fid1.mem_sphere_iff' … 'Fid1.countable_directions' (20 theorems): each depends on axioms: [propext, Classical.choice, Quot.sound]
Fid1.paper_iff_challenge : Fid1.PaperThm ↔
  ∀ (K : Set (EuclideanSpace ℝ (Fin 4))), (∀ e ∈ sphere 0 1, ∃ a, segment ℝ a (a + e) ⊆ K) → dimH K = 4
```

- Hashes: `Witness.lean` sha256 `14fb9de2…`, `Elab.lean` `c43e8359…`, `run-in-docker.sh`
  `84117943…`. All files are in `final/074/fidelity-audit-1/`. The witness file imports only
  `Challenge` (that is, Mathlib) and nothing from `Submission`.

## Appendix A. `Witness.lean` (compiled, standard axioms only)

The full file is `final/074/fidelity-audit-1/Witness.lean`. The statements are:

```lean
abbrev E4 := EuclideanSpace ℝ (Fin 4)
-- (W1)
theorem mem_sphere_iff (e : E4) : e ∈ sphere (0 : E4) 1 ↔ ∑ i, (e.ofLp i) ^ 2 = 1
def u : E4 := WithLp.toLp 2 ![1 / 2, 1 / 2, 1 / 2, 1 / 2]
theorem u_mem : u ∈ sphere (0 : E4) 1
theorem u_sup : ‖(![1 / 2, 1 / 2, 1 / 2, 1 / 2] : Fin 4 → ℝ)‖ = 1 / 2
def w : E4 := WithLp.toLp 2 ![1, 1, 0, 0]
theorem w_not_mem : w ∉ sphere (0 : E4) 1
theorem w_sup : ‖(![1, 1, 0, 0] : Fin 4 → ℝ)‖ = 1
-- (W2)
theorem segment_eq (a e : E4) : segment ℝ a (a + e) = (fun t : ℝ => a + t • e) '' Icc (0 : ℝ) 1
theorem segment_diam (a e : E4) (he : e ∈ sphere (0 : E4) 1) : diam (segment ℝ a (a + e)) = 1
theorem segment_dimH (a e : E4) (he : e ∈ sphere (0 : E4) 1) : dimH (segment ℝ a (a + e)) = 1
-- (W3)
def paperH (s : ℝ) (K : Set E4) : ℝ≥0∞ :=
  ⨆ (r : ℝ≥0∞) (_ : 0 < r), ⨅ (t : ℕ → Set E4) (_ : K ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r),
    ∑' n, ⨆ (_ : (t n).Nonempty), ediam (t n) ^ s
def paperDim (K : Set E4) : ℝ≥0∞ := ⨅ (s : ℝ≥0) (_ : paperH s K = 0), (s : ℝ≥0∞)
theorem paperH_eq (s : ℝ) (K : Set E4) : paperH s K = μH[s] K
theorem paperDim_eq (K : Set E4) : paperDim K = dimH K
-- (W4)
def PaperThm : Prop := ∀ K : Set E4,
    (∀ e : E4, ∑ i, (e.ofLp i) ^ 2 = 1 → ∃ a : E4, ∀ t ∈ Icc (0 : ℝ) 1, a + t • e ∈ K) →
      paperDim K = 4
theorem paper_iff_challenge : PaperThm ↔ type_of% @kakeya_four_dimensions
-- (W5)
theorem closedBall_hyp : ∀ e ∈ sphere (0 : E4) 1, ∃ a : E4, segment ℝ a (a + e) ⊆ closedBall (0 : E4) 1
theorem univ_hyp : ∀ e ∈ sphere (0 : E4) 1, ∃ a : E4, segment ℝ a (a + e) ⊆ (univ : Set E4)
theorem dimH_univ4 : dimH (univ : Set E4) = 4
theorem dimH_closedBall4 : dimH (closedBall (0 : E4) 1) = 4
-- (W6)
theorem point_fails : ¬ ∀ e ∈ sphere (0 : E4) 1, ∃ a : E4, segment ℝ a (a + e) ⊆ ({0} : Set E4)
theorem dimH_point : dimH ({0} : Set E4) = 0
def H : Set E4 := {x | x.ofLp 0 = 0}
theorem hyperplane_fails : ¬ ∀ e ∈ sphere (0 : E4) 1, ∃ a : E4, segment ℝ a (a + e) ⊆ H
theorem dimH_hyperplane_le : dimH H ≤ 3
theorem hyperplane_conclusion_fails : dimH H ≠ 4
theorem countable_directions (a e : ℕ → E4) : dimH (⋃ n, segment ℝ (a n) (a n + e n)) ≤ 1
```

Proof sketches:
- **W1.** `mem_sphere_zero_iff_norm`, `EuclideanSpace.norm_eq`, `Real.sqrt_eq_one`.
- **W2.** `segment_eq_image'`. The diameter: dist(a + s e, a + t e) = |s − t| ≤ 1, and the
  endpoints are at distance 1. The dimension: `Real.dimH_segment`.
- **W3.** `Measure.hausdorffMeasure_apply` and `dimH_eq_iInf`.
- **W4.** W1, W2, W3.
- **W5.** Convexity of the ball, and `Real.dimH_of_nonempty_interior`.
- **W6.**
  - Direction (1,0,0,0) cannot fit in {x₀ = 0}.
  - H ⊆ range of the linear map y ↦ (0, y) on ℝ³, which is Lipschitz, so
    `dimH ≤ dimH univ(ℝ³) = 3`.
  - `dimH_iUnion` and `Real.dimH_segment` handle the countable union.
