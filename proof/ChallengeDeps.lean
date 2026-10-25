import Mathlib

/-!
# Every four-dimensional Kakeya set has full Hausdorff dimension (OpenAI math, family 074)

Theorem 1.1 of OpenAI, *Every four-dimensional Kakeya set has full Hausdorff dimension*
(September 24, 2026): the Hausdorff-dimension Kakeya conjecture in `ℝ⁴`.

Paper's setting: `K ⊂ ℝ⁴` is arbitrary (not assumed measurable or closed), and for every unit
vector `e ∈ S³` it contains a unit segment `{a_e + t e : 0 ≤ t ≤ 1}` in direction `e`.
Here `ℝ⁴` is `EuclideanSpace ℝ (Fin 4)` with its Euclidean metric, `S³` is the unit sphere,
the segment is Mathlib's `segment ℝ a (a + e)`, and `dimH` is Mathlib's Hausdorff dimension.
-/
