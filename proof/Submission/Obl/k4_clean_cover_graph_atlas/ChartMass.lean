-- Adapted from this LOT tree o194, session x0672, commit 69d09a7b,
-- Submission/Obl/k4_greedy_cover_graph_atlas/ChartMass.lean. Earlier attributions follow.

-- Adapted from this LOT tree, o173, session x0598, commit 6ded8016fe11,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/ChartMass.lean.

import Submission.Obl.k4_clean_cover_graph_atlas.Interface

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory Set

/-- A cylinder incidence floor implies the corresponding original prior floor,
without conditioning that prior on the incidence event. -/
theorem prior_floor_of_cylinder {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (A : Set X) (F : Set (X × ℝ)) {s τ q : ℝ}
    (hτ : 0 < τ) (hq : 0 ≤ q) (hsub : F ⊆ A ×ˢ Icc s (s + τ))
    (hfloor : ENNReal.ofReal (q * τ) ≤ (ν.prod volume) F) :
    ENNReal.ofReal q ≤ ν A := by
  have hunit : ENNReal.ofReal τ * ENNReal.ofReal τ⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hτ.le, mul_inv_cancel₀ hτ.ne']
    norm_num
  have hprod : (ν.prod volume) F ≤ ν A * ENNReal.ofReal τ := by
    calc
      _ ≤ (ν.prod volume) (A ×ˢ Icc s (s + τ)) := measure_mono hsub
      _ = _ := by rw [Measure.prod_prod, Real.volume_Icc]; congr 1; congr 1; ring
  calc
    _ = ENNReal.ofReal (q * τ) * ENNReal.ofReal τ⁻¹ := by
      rw [ENNReal.ofReal_mul hq, mul_assoc, hunit, mul_one]
    _ ≤ (ν A * ENNReal.ofReal τ) * ENNReal.ofReal τ⁻¹ := by
      gcongr
      exact hfloor.trans hprod
    _ = ν A := by rw [mul_assoc, hunit, mul_one]

/-- The saturated path floor bounds the original prior of every old packet below
by its determinant/profile scale. -/
theorem chart_prior_floor {Nk κ j r B fval : ℝ} {M D T : ℕ}
    {E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ}
    {A : Set (ℕ × (Fin 6 → ℝ))} {F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex : Prop}
    (ν : Measure (ℕ × (Fin 6 → ℝ))) (hNk : 0 < Nk) (hκ : 0 < κ)
    (hc : chart Nk M D κ T j r B E c u Q R A F ex)
    (hfloor : ENNReal.ofReal (Nk ^ (-fval) * |Matrix.det Q| / ((2 : ℝ) ^ T * κ)) ≤
      (ν.prod volume) F) :
    ENNReal.ofReal (Nk ^ (-fval) * |Matrix.det Q| / κ) ≤ ν A := by
  rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, hF, _⟩
  have htime : 0 < 1 / (2 : ℝ) ^ T := by positivity
  apply prior_floor_of_cylinder ν A F htime (by positivity)
  · intro p hp
    obtain ⟨_, hA, ht, _⟩ := hF p hp
    refine ⟨hA, ht.1, ?_⟩
    convert ht.2 using 1 <;> ring
  · convert hfloor using 2
    field_simp
    <;> ring

end Submission.Obl.k4_clean_cover_graph_atlas
