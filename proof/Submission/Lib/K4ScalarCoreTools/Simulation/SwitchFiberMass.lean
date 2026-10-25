/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarSimulation/SwitchFiberMass.lean at ccb7071c.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511,
Submission/Obl/k4_scalar_mesh_projection/SwitchFiberMass.lean.
-/

import Mathlib

namespace Submission.Lib.K4ScalarCoreTools.Simulation.Switching

open Set MeasureTheory

/-- An original path law dominated by a product reference pays the base
bad-set mass times the full increment-box volume, plus the uniform volume
of all passing sections. The successful law is never normalized. -/
theorem path_mass_le_of_bad_base_and_section_volume {Θ : Type*} [MeasurableSpace Θ]
    (ν : Measure Θ) [IsProbabilityMeasure ν] (μ : Measure (Θ × (Fin 4 → ℝ)))
    (S : Set (Θ × (Fin 4 → ℝ))) (Bad : Set Θ) (L b r : ℝ)
    (hL : 0 ≤ L) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (hdom : μ ≤ ENNReal.ofReal L • (ν.prod volume))
    (hS : MeasurableSet S) (hBad : MeasurableSet Bad)
    (hbox : ∀ z ∈ S, z.2 ∈ Icc (-1 : Fin 4 → ℝ) 1)
    (hbad : ν Bad ≤ ENNReal.ofReal b)
    (hsection : ∀ θ ∉ Bad, volume (Prod.mk θ ⁻¹' S) ≤ ENNReal.ofReal r) :
    μ S ≤ ENNReal.ofReal (L * (16 * b + r)) := by
  let Good : Set (Θ × (Fin 4 → ℝ)) := S ∩ (Prod.fst ⁻¹' Badᶜ)
  have hGood : MeasurableSet Good := hS.inter (hBad.compl.preimage measurable_fst)
  have hgoodvol : (ν.prod volume) Good ≤ ENNReal.ofReal r := by
    rw [Measure.prod_apply hGood]
    calc
      _ ≤ ∫⁻ _ : Θ, ENNReal.ofReal r ∂ν := by
        apply lintegral_mono
        intro θ
        by_cases hθ : θ ∈ Bad
        · have hempty : Prod.mk θ ⁻¹' Good = ∅ := by
            ext δ
            simp [Good, hθ]
          simp only [hempty, measure_empty]
          exact zero_le
        · have heq : Prod.mk θ ⁻¹' Good = Prod.mk θ ⁻¹' S := by
            ext δ
            simp [Good, hθ]
          simpa only [heq] using hsection θ hθ
      _ = ENNReal.ofReal r := by simp
  have hcube : volume (Icc (-1 : Fin 4 → ℝ) 1) = ENNReal.ofReal (16 : ℝ) := by
    norm_num [Real.volume_Icc_pi]
  have hcov : S ⊆ (Bad ×ˢ Icc (-1 : Fin 4 → ℝ) 1) ∪ Good := by
    intro z hz
    by_cases h : z.1 ∈ Bad
    · exact Or.inl ⟨h, hbox z hz⟩
    · exact Or.inr ⟨hz, h⟩
  have hvol : (ν.prod volume) S ≤ ENNReal.ofReal (16 * b + r) := by
    calc
      _ ≤ (ν.prod volume) (Bad ×ˢ Icc (-1 : Fin 4 → ℝ) 1) + (ν.prod volume) Good :=
        (measure_mono hcov).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal b * ENNReal.ofReal (16 : ℝ) + ENNReal.ofReal r := by
        rw [Measure.prod_prod, hcube]
        exact add_le_add (mul_le_mul_of_nonneg_right hbad bot_le) hgoodvol
      _ = ENNReal.ofReal (16 * b + r) := by
        rw [← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_add (mul_nonneg hb (by norm_num)) hr]
        congr 1
        ring
  have hμ : μ S ≤ ENNReal.ofReal L * (ν.prod volume) S := by
    simpa only [Measure.smul_apply, smul_eq_mul] using Measure.le_iff.mp hdom S hS
  exact (hμ.trans (mul_le_mul_of_nonneg_left hvol bot_le)).trans_eq
    (ENNReal.ofReal_mul hL).symm

end Submission.Lib.K4ScalarCoreTools.Simulation.Switching
