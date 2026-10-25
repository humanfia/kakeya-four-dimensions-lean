/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit ada3f86eb242f61a5efc6a1192de06f5479cb35e,
Submission/Obl/k4_scalar_mesh_projection/NormalizedIncrements.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Submission.Lib.K4ScalarActualSwitching.ActualCoordinates

namespace Submission.Lib.K4ScalarActualSwitching

open Submission.Lib.K4ScalarSwitching

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable def normalizeIncrements {Θ : Type*} (h : ℝ)
    (z : Θ × (Fin 4 → ℝ)) : Θ × (Fin 4 → ℝ) :=
  (z.1, h⁻¹ • z.2)

theorem measurable_normalizeIncrements {Θ : Type*} [MeasurableSpace Θ] (h : ℝ) :
    Measurable (normalizeIncrements (Θ := Θ) h) := by
  unfold normalizeIncrements
  fun_prop

theorem map_volume_normalize_increments (h : ℝ) (hh : 0 < h) :
    (volume : Measure (Fin 4 → ℝ)).map (fun δ => h⁻¹ • δ) =
      ENNReal.ofReal (h ^ 4) • volume := by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (by fun_prop) hS, Measure.smul_apply, smul_eq_mul,
    volume.addHaar_preimage_smul (inv_ne_zero hh.ne')]
  simp only [inv_pow, inv_inv, abs_pow, abs_of_pos hh,
    Module.finrank_fin_fun]

/-- Dividing four signed increments by the actual block duration pays
exactly its fourth power in the density ceiling. -/
theorem map_normalizeIncrements_le {Θ : Type*} [MeasurableSpace Θ]
    (ν : Measure Θ) [SFinite ν] (ρ : Measure (Θ × (Fin 4 → ℝ)))
    (C : ENNReal) (h : ℝ) (hh : 0 < h)
    (hρ : ρ ≤ C • ν.prod volume) :
    ρ.map (normalizeIncrements h) ≤ (C * ENNReal.ofReal (h ^ 4)) • ν.prod volume ∧
      ρ.map (normalizeIncrements h) univ = ρ univ := by
  have hf := measurable_normalizeIncrements (Θ := Θ) h
  have hmap : (ν.prod volume).map (normalizeIncrements h) =
      ENNReal.ofReal (h ^ 4) • ν.prod volume := by
    change (ν.prod volume).map (Prod.map id (fun δ : Fin 4 → ℝ => h⁻¹ • δ)) = _
    rw [← Measure.map_prod_map ν volume measurable_id (by fun_prop), Measure.map_id,
      map_volume_normalize_increments h hh, Measure.prod_smul_right]
  have hdom := Measure.map_mono hρ hf
  rw [Measure.map_smul C hf.aemeasurable, hmap, smul_smul] at hdom
  exact ⟨hdom, by rw [Measure.map_apply hf MeasurableSet.univ, preimage_univ]⟩

theorem normalizeIncrements_mem_unit_cube {Θ : Type*} {h : ℝ} (hh : 0 < h)
    (z : Θ × (Fin 4 → ℝ)) (hz : z.2 ∈ Icc (fun _ => -h) (fun _ => h)) :
    (normalizeIncrements h z).2 ∈ Icc (-1 : Fin 4 → ℝ) 1 := by
  constructor <;> intro i
  · change -1 ≤ h⁻¹ * z.2 i
    rw [← div_eq_inv_mul]
    apply (le_div_iff₀ hh).mpr
    simpa only [neg_one_mul] using hz.1 i
  · change h⁻¹ * z.2 i ≤ 1
    rw [← div_eq_inv_mul]
    apply (div_le_one hh).mpr
    exact hz.2 i

theorem normalizeIncrements_fst {Θ : Type*} [MeasurableSpace Θ]
    (ρ : Measure (Θ × (Fin 4 → ℝ))) (h : ℝ) :
    (ρ.map (normalizeIncrements h)).fst = ρ.fst := by
  unfold Measure.fst
  rw [Measure.map_map measurable_fst (measurable_normalizeIncrements h)]
  rfl

theorem ae_normalizeIncrements_mem_unit_cube {Θ : Type*} [MeasurableSpace Θ]
    (ρ : Measure (Θ × (Fin 4 → ℝ))) (h : ℝ) (hh : 0 < h)
    (hρ : ∀ᵐ z ∂ρ, z.2 ∈ Icc (fun _ => -h) (fun _ => h)) :
    ∀ᵐ z ∂ρ.map (normalizeIncrements h), z.2 ∈ Icc (-1 : Fin 4 → ℝ) 1 := by
  apply (ae_map_iff (measurable_normalizeIncrements h).aemeasurable
    (measurableSet_Icc.preimage measurable_snd)).mpr
  filter_upwards [hρ] with z hz
  exact normalizeIncrements_mem_unit_cube hh z hz

theorem normalized_four_step_density_factor (K D : ENNReal) (h : ℝ) (hh : 0 < h) :
    (K * ((ENNReal.ofReal h)⁻¹ * D)) ^ 4 * ENNReal.ofReal (h ^ 4) = (K * D) ^ 4 := by
  have hH : ENNReal.ofReal h ≠ 0 := (ENNReal.ofReal_pos.mpr hh).ne'
  rw [ENNReal.ofReal_pow hh.le, mul_pow, mul_pow]
  calc
    _ = (K ^ 4 * D ^ 4) * (((ENNReal.ofReal h)⁻¹ * ENNReal.ofReal h) ^ 4) := by
      rw [mul_pow]
      ring
    _ = (K * D) ^ 4 := by
      rw [ENNReal.inv_mul_cancel hH ENNReal.ofReal_ne_top, one_pow, mul_one, mul_pow]

/-- The physical endpoint-time ceiling D/h and the four-coordinate
Jacobian h^4 cancel exactly in normalized signed increments. -/
theorem actual_four_step_normalized_increment_law {X Q : Type*}
    [MeasurableSpace X] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    [StandardBorelSpace (X × ℝ)] [Nonempty (X × ℝ)]
    (ν : Measure X) [IsFiniteMeasure ν]
    (κ : Kernel X ℝ) [IsMarkovKernel κ]
    (state : X × ℝ → Q) (hstate : Measurable state)
    (control : X → ℝ) (hcontrol : Measurable control)
    (π : Measure ℝ) [SigmaFinite π]
    (L : Set X) (hL : MeasurableSet L) (K D p : ENNReal) (r h : ℝ) (hh : 0 < h)
    (hrect : ∀ q (A : Set ℝ), MeasurableSet A →
      (ν ⊗ₘ κ) {ω | state ω = q ∧ control ω.1 ∈ A} ≤
        K * (ν ⊗ₘ κ) (state ⁻¹' {q}) * π A)
    (hthin : ∀ w : ℝ, π {v | |v - w| < r} ≤ p)
    (htime : ∀ x ∈ L, κ x ≤ ((ENNReal.ofReal h)⁻¹ * D) • volume) :
    let μ := ν ⊗ₘ κ
    let θ₁ := retainedActualSwitch μ ν κ state hstate id measurable_id control L r
    let θ₂ := retainedActualSwitch θ₁ ν κ state hstate Prod.snd measurable_snd control L r
    let θ₃ := retainedActualSwitch θ₂ ν κ state hstate Prod.snd measurable_snd control L r
    let θ₄ := retainedActualSwitch θ₃ ν κ state hstate Prod.snd measurable_snd control L r
    let ρ := (θ₄.map (actualPathCoordinates control)).map (normalizeIncrements h)
    μ univ ≤ ρ univ + 4 * μ (Prod.fst ⁻¹' Lᶜ) + 4 * (K * p) * μ univ ∧
      ρ ≤ (K * D) ^ 4 • ((μ.prod (Measure.pi (fun _ : Fin 4 => π))).prod volume) := by
  let μ := ν ⊗ₘ κ
  let θ₁ := retainedActualSwitch μ ν κ state hstate id measurable_id control L r
  let θ₂ := retainedActualSwitch θ₁ ν κ state hstate Prod.snd measurable_snd control L r
  let θ₃ := retainedActualSwitch θ₂ ν κ state hstate Prod.snd measurable_snd control L r
  let θ₄ := retainedActualSwitch θ₃ ν κ state hstate Prod.snd measurable_snd control L r
  have hraw := actual_four_step_increment_law ν κ state hstate control hcontrol π L hL
    K ((ENNReal.ofReal h)⁻¹ * D) p r hrect hthin htime
  have hnorm := map_normalizeIncrements_le (μ.prod (Measure.pi (fun _ : Fin 4 => π)))
    (θ₄.map (actualPathCoordinates control)) ((K * ((ENNReal.ofReal h)⁻¹ * D)) ^ 4) h hh hraw.2
  refine ⟨?_, ?_⟩
  · change μ univ ≤
      ((θ₄.map (actualPathCoordinates control)).map (normalizeIncrements h)) univ +
        4 * μ (Prod.fst ⁻¹' Lᶜ) + 4 * (K * p) * μ univ
    rw [hnorm.2]
    exact hraw.1
  · simpa only [normalized_four_step_density_factor K D h hh] using hnorm.1

end Submission.Lib.K4ScalarActualSwitching
