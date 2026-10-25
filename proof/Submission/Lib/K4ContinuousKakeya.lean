import Submission.Lib.K4ContinuousKakeya.Continuous
import Submission.Lib.K4ContinuousKakeya.Incidence
import Submission.Lib.K4ContinuousKakeya.GraphExtraction
import Submission.Lib.K4ContinuousKakeya.Tangent

/-!
# Continuous multilinear Kakeya, its incidence form, and affine graphs from triple moments

Mathlib-only tools for Section 6 of the paper (velocity graph, strip filling, heavy intercept
groups), written by session x0320 on o092:

* `Continuous`: `FiniteMK n C` is the finite determinant-weighted multilinear Kakeya inequality in
  the frozen shape (of `Submission.k4_multilinear_kakeya` and of the hypotheses of o092 and its
  children); `setLIntegral_contTubeSum_le` extends it to finite measures on line parameters
  (bounded base points, unit directions) with constant `2 ^ n * C`; `sum_volume_mul_rpow_le` is its
  cell form and `le_contTubeSum` gives cell lower bounds from successful tuples.
* `Incidence`: `incidence_kakeya` for incidence measures on trajectories × time, with
  `map_fst_restrict_le` (pushforward domination from `inc ≤ K • θ × time` and time sections),
  `pi_mono`, `pi_smul`, `mem_tube_iff`, `measurableSet_mem_tube`.
* `GraphExtraction`: `exists_line_of_triple_moment`, an affine graph `W = G₀ + G₁ V` with small
  `L¹` residual for any finite law of `(V, W)` with `V`-breadth and small triple moment.
* `Tangent`: tangent-line and lifted-velocity errors of quadratic trajectories
  (`norm_physPoint_sub_tangent`, `norm_liftVel_sub`, `norm_normalize_sub_le`,
  `physPoint_mem_tube_tangent`).
-/
