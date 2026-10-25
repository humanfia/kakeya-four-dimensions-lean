/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit 2e65ac82f715df53d854782d6e862452630b9dde,
Submission/Obl/k4_scalar_mesh_projection/OriginalBaseArea.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Mathlib

namespace Submission.Lib.K4ScalarActualSwitching

open Set MeasureTheory
open scoped ENNReal

/-- A retained witness law supported over a measurable base event is
charged to the unchanged start law and its original base ceiling.
The witnesses need not be selected measurably from the base points. -/
theorem retained_mass_le_original_base_measure {Ω W B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace B]
    (μ : Measure Ω) (θ : Measure (Ω × W)) (hfst : θ.fst ≤ μ)
    (base : Ω → B) (hbase : Measurable base) (σ : Measure B) (C : ENNReal)
    (hcap : μ.map base ≤ C • σ) (S : Set B) (hS : MeasurableSet S)
    (hsupport : ∀ᵐ z ∂θ, base z.1 ∈ S) :
    θ univ ≤ C * σ S := by
  let A : Set (Ω × W) := (fun z => base z.1) ⁻¹' S
  have hz : θ Aᶜ = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hsupport] with z hz
    change ¬¬(base z.1 ∈ S)
    exact not_not_intro hz
  have hfull : θ A = θ univ := measure_of_measure_compl_eq_zero hz
  have hmapped := (Measure.map_mono hfst hbase).trans hcap
  rw [Measure.fst, Measure.map_map hbase measurable_fst] at hmapped
  have h := Measure.le_iff.mp hmapped S hS
  rw [Measure.map_apply (hbase.comp measurable_fst) hS, Measure.smul_apply, smul_eq_mul] at h
  exact hfull.symm.trans_le h

theorem original_base_area_floor {Ω W B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace B]
    (μ : Measure Ω) (θ : Measure (Ω × W)) (hfst : θ.fst ≤ μ)
    (base : Ω → B) (hbase : Measurable base) (σ : Measure B) (C p : ℝ)
    (hC : 0 < C) (hcap : μ.map base ≤ ENNReal.ofReal C • σ)
    (S : Set B) (hS : MeasurableSet S)
    (hsupport : ∀ᵐ z ∂θ, base z.1 ∈ S) (hmass : ENNReal.ofReal p ≤ θ univ) :
    ENNReal.ofReal (p / C) ≤ σ S := by
  have h := hmass.trans
    (retained_mass_le_original_base_measure μ θ hfst base hbase σ (ENNReal.ofReal C) hcap S hS hsupport)
  rw [ENNReal.ofReal_div_of_pos hC]
  apply (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hC).ne' ENNReal.ofReal_ne_top).mpr
  simpa only [mul_comm] using h

theorem half_mass_of_small_relative_loss (M R δ : ENNReal) (hM : M ≠ ∞)
    (hδ : δ ≤ 1 / 2) (hbudget : M ≤ R + δ * M) : M / 2 ≤ R := by
  apply ENNReal.le_of_add_le_add_right (a := M / 2)
  · finiteness
  · calc
      M / 2 + M / 2 = M := ENNReal.add_halves M
      _ ≤ R + δ * M := hbudget
      _ ≤ R + M / 2 := by
        apply add_le_add le_rfl
        calc
          δ * M ≤ (1 / 2) * M := mul_le_mul' hδ le_rfl
          _ = M / 2 := by simp only [div_eq_mul_inv, one_mul]; ac_rfl

end Submission.Lib.K4ScalarActualSwitching
