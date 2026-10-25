import Mathlib
import ChallengeDeps

/-!
# Seed for `oai_074_kakeya_four_dimensions`: the easy half and bookkeeping

The challenge is `dimH K = 4` for a set `K ⊆ ℝ⁴ = EuclideanSpace ℝ (Fin 4)` containing a closed
unit segment `segment ℝ a (a + e)` in every unit direction `e`.

* `dimH_univ`, `dimH_le_four`: the upper bound `dimH K ≤ 4` holds for every subset of `ℝ⁴`.
* `dimH_eq_four_iff`: the challenge is equivalent to the lower bound `4 ≤ dimH K`.
* `four_le_dimH_iff`, `four_le_dimH_of_forall_real`: `4 ≤ dimH K` iff `μH[d] K ≠ 0` for every
  `d < 4` (the entry point of the discretization `k4_lower_of_discrete`: assume `μH[d] K = 0`
  for some `d < 4` and derive a contradiction).
* `segment_eq_image_add`: Mathlib's `segment ℝ a (a + e)` is `{a + t • e | t ∈ [0, 1]}`.

Only `dimH_le_four` is used by the preset glue. Written 2026-10-19 for this package after the
wang_zahl seed (`Submission.Seed.Kakeya`, the same proofs in dimension three); NOT YET COMPILED at
Lean v4.35.0-rc3 / Mathlib 5e0c4e5 -- phase B builds it; a lemma that fails there is dropped
(except `dimH_le_four`, which the glue needs).
-/

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace Submission.Seed.K4

/-- The Hausdorff dimension of the whole space `ℝ⁴` is `4`. -/
theorem dimH_univ : dimH (univ : Set (EuclideanSpace ℝ (Fin 4))) = 4 := by
  rw [Real.dimH_univ_eq_finrank (EuclideanSpace ℝ (Fin 4)), finrank_euclideanSpace_fin]
  rfl

/-- **Upper bound.** Every subset of `ℝ⁴` has Hausdorff dimension at most `4`. -/
theorem dimH_le_four (K : Set (EuclideanSpace ℝ (Fin 4))) : dimH K ≤ 4 :=
  (dimH_mono (subset_univ K)).trans_eq dimH_univ

/-- The challenge `dimH K = 4` is equivalent to the lower bound `4 ≤ dimH K`. -/
theorem dimH_eq_four_iff (K : Set (EuclideanSpace ℝ (Fin 4))) : dimH K = 4 ↔ 4 ≤ dimH K :=
  ⟨fun h => h.ge, fun h => le_antisymm (dimH_le_four K) h⟩

/-- `4 ≤ dimH K` iff no `d`-dimensional Hausdorff measure with `d < 4` vanishes on `K`. -/
theorem four_le_dimH_iff (K : Set (EuclideanSpace ℝ (Fin 4))) :
    4 ≤ dimH K ↔ ∀ d : ℝ≥0, d < 4 → μH[d] K ≠ 0 := by
  constructor
  · intro h d hd
    have hlt : (d : ℝ≥0∞) < dimH K := by
      refine lt_of_lt_of_le ?_ h
      exact_mod_cast hd
    rw [hausdorffMeasure_of_lt_dimH hlt]
    exact ENNReal.top_ne_zero
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨d, hKd, hd4⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
    have hd4' : d < 4 := by exact_mod_cast hd4
    exact h d hd4' (hausdorffMeasure_of_dimH_lt hKd)

/-- Real-exponent form of `four_le_dimH_iff` (the direction used in a proof by contradiction). -/
theorem four_le_dimH_of_forall_real (K : Set (EuclideanSpace ℝ (Fin 4)))
    (h : ∀ s : ℝ, 0 ≤ s → s < 4 → μH[s] K ≠ 0) : 4 ≤ dimH K := by
  refine (four_le_dimH_iff K).2 fun d hd => ?_
  exact h d d.2 (by exact_mod_cast hd)

/-- The closed segment `segment ℝ a (a + e)` is the image of `[0, 1]` under `t ↦ a + t • e`. -/
theorem segment_eq_image_add (a e : EuclideanSpace ℝ (Fin 4)) :
    segment ℝ a (a + e) = (fun t : ℝ => a + t • e) '' Icc (0 : ℝ) 1 := by
  rw [segment_eq_image']
  simp

end Submission.Seed.K4
