import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.FieldStep

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

/-- Recovering the two transverse coefficients controls the correction at
every bounded transverse coordinate. -/
theorem transv_error {tc C : Fin 4 → ℝ} {x y U K E₁ E₂ : ℝ}
    (h₁ : |lin1 tc x y - lin1 C x y| ≤ E₁) (h₂ : |tc 3 - C 3| ≤ E₂)
    (hU : |U| ≤ K) :
    |transv tc x y U - transv C x y U| ≤ E₁ * K + E₂ * K ^ 2 := by
  have hid : transv tc x y U - transv C x y U =
      (lin1 tc x y - lin1 C x y) * U + (tc 3 - C 3) * U ^ 2 := by
    unfold transv lin1
    ring
  have hE₁ : 0 ≤ E₁ := (abs_nonneg _).trans h₁
  have hE₂ : 0 ≤ E₂ := (abs_nonneg _).trans h₂
  have hK : 0 ≤ K := (abs_nonneg _).trans hU
  rw [hid]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_pow]
  gcongr

/-- A captured consensus field approximates the actual coarse predictor at
the actual base point, paying its one-mesh center error. -/
theorem stateField_recovery {Γ : Type*} (tc : Γ → Fin 4 → ℝ)
    (center : (Fin 4 → ℤ) → Γ) {H δ x y E eR : ℝ} (hH : 0 ≤ H)
    (hδ : 0 < δ) (γ : Γ) (Q : Fin 4 → ℤ) (htc : ∀ e, |tc γ e| ≤ H)
    (hx : ⌊x / δ⌋ = Q 0) (hy : ⌊y / δ⌋ = Q 1)
    (hagree : |lin1 (tc γ) (stateCenter δ Q 0) (stateCenter δ Q 1) -
        lin1 (tc (center Q)) (stateCenter δ Q 0) (stateCenter δ Q 1)| +
      |tc γ 3 - tc (center Q) 3| ≤ eR)
    (C : Fin 4 → ℝ)
    (hcap : |stateFieldValue tc center δ Q 0 - C 0 - C 1 * x - C 2 * y| ≤ E ∧
      |stateFieldValue tc center δ Q 1 - C 3| ≤ E) :
    |lin1 (tc γ) x y - lin1 C x y| ≤ E + eR + H * δ ∧
      |tc γ 3 - C 3| ≤ E + eR := by
  have hnear := lin1_stateCenter_error hH htc hδ Q hx hy
  have hrep : |lin1 (tc γ) (stateCenter δ Q 0) (stateCenter δ Q 1) -
      stateFieldValue tc center δ Q 0| ≤ eR :=
    (le_add_of_nonneg_right (abs_nonneg _)).trans hagree
  have hrep₂ : |tc γ 3 - stateFieldValue tc center δ Q 1| ≤ eR :=
    (le_add_of_nonneg_left (abs_nonneg _)).trans hagree
  have hcap₁ : |stateFieldValue tc center δ Q 0 - lin1 C x y| ≤ E := by
    convert hcap.1 using 1
    congr 1
    unfold lin1
    ring
  constructor
  · have hh := abs_sub_le (lin1 (tc γ) x y)
      (lin1 (tc γ) (stateCenter δ Q 0) (stateCenter δ Q 1)) (lin1 C x y)
    have hh' := abs_sub_le (lin1 (tc γ) (stateCenter δ Q 0) (stateCenter δ Q 1))
      (stateFieldValue tc center δ Q 0) (lin1 C x y)
    have hnear' : |lin1 (tc γ) x y - lin1 (tc γ) (stateCenter δ Q 0) (stateCenter δ Q 1)| ≤ H * δ := by
      rw [abs_sub_comm]
      exact hnear
    linarith
  · calc _ ≤ |tc γ 3 - stateFieldValue tc center δ Q 1| +
        |stateFieldValue tc center δ Q 1 - C 3| := abs_sub_le _ _ _
      _ ≤ eR + E := add_le_add hrep₂ hcap.2
      _ = E + eR := add_comm _ _

namespace ComparedBlock

open Submission.Obl.k4_critical_conditional_row_preparation

attribute [local instance] ComparedBlock.instΓ ComparedBlock.instΛ

variable {α : Type} [MeasurableSpace α] {cfg : Data α} {k : ℕ} {s u v χ H : ℝ}

def fieldCapture (CB : ComparedBlock cfg k s u v χ H)
    (center : (Fin 4 → ℤ) → CB.Γ) (δ δU δX : ℝ) (C : Fin 4 → ℝ) (E : ℝ) : Set (α × ℝ) :=
  {p | |CB.consensusField center δ δU δX p 0 - C 0 - C 1 * CB.frame.zt p.2 -
        C 2 * CB.frame.zZ (cfg.b k p.1) p.2| ≤ E ∧
    |CB.consensusField center δ δU δX p 1 - C 3| ≤ E}

theorem measurableSet_fieldCapture (CB : ComparedBlock cfg k s u v χ H)
    (center : (Fin 4 → ℤ) → CB.Γ) (δ δU δX : ℝ) (C : Fin 4 → ℝ) (E : ℝ)
    (hb : Measurable (cfg.b k)) : MeasurableSet (CB.fieldCapture center δ δU δX C E) := by
  have hf := CB.measurable_consensusField center δ δU δX hb
  have hz := measurable_coords CB.frame hb
  have hzt : Measurable (fun p : α × ℝ => CB.frame.zt p.2) :=
    (measurable_pi_apply 0).comp hz
  have hzZ : Measurable (fun p : α × ℝ => CB.frame.zZ (cfg.b k p.1) p.2) :=
    (measurable_pi_apply 1).comp hz
  apply MeasurableSet.inter
  · exact measurableSet_le
      (((((measurable_pi_apply 0).comp hf).sub_const (C 0)).sub (hzt.const_mul (C 1))).sub
        (hzZ.const_mul (C 2))).abs measurable_const
  · exact measurableSet_le (((measurable_pi_apply 1).comp hf).sub_const (C 3)).abs measurable_const

/-- Restrict only the original law to the captured common field. -/
def fieldLaw (CB : ComparedBlock cfg k s u v χ H)
    (center : (Fin 4 → ℤ) → CB.Γ) (δ δU δX : ℝ) (C : Fin 4 → ℝ) (E : ℝ)
    (lam : Measure (α × ℝ)) : Measure (α × ℝ) :=
  lam.restrict (CB.fieldCapture center δ δU δX C E)

theorem fieldLaw_le (CB : ComparedBlock cfg k s u v χ H)
    (center : (Fin 4 → ℤ) → CB.Γ) (δ δU δX : ℝ) (C : Fin 4 → ℝ) (E : ℝ)
    (lam : Measure (α × ℝ)) : CB.fieldLaw center δ δU δX C E lam ≤ lam := Measure.restrict_le_self

theorem fieldLaw_mass (CB : ComparedBlock cfg k s u v χ H)
    (center : (Fin 4 → ℤ) → CB.Γ) (δ δU δX : ℝ) (C : Fin 4 → ℝ) (E : ℝ)
    (lam : Measure (α × ℝ)) :
    CB.fieldLaw center δ δU δX C E lam univ = lam (CB.fieldCapture center δ δU δX C E) := by
  rw [fieldLaw, Measure.restrict_apply MeasurableSet.univ, univ_inter]

/-- The captured law has the corrected layer-2 fit with an explicit error.
This is the analytic input used by the original-palette residual count. -/
theorem fieldLaw_corrected_fit (CB : ComparedBlock cfg k s u v χ H)
    (center : (Fin 4 → ℤ) → CB.Γ) {δ δU δX E eR K : ℝ} (hδ : 0 < δ)
    (C : Fin 4 → ℝ) (hb : Measurable (cfg.b k))
    (lam : Measure (α × ℝ)) (hlam : lam ≤ CB.lam)
    (hU : ∀ᵐ p ∂lam, |CB.frame.tr (cfg.b k p.1) p.2| ≤ K)
    (hagree : ∀ᵐ p ∂lam,
      let Q := sigmaState CB.frame δ δU δX (cfg.b k p.1) p.2
      |lin1 (CB.tc (CB.crs (CB.lab p.1))) (stateCenter δ Q 0) (stateCenter δ Q 1) -
        lin1 (CB.tc (center Q)) (stateCenter δ Q 0) (stateCenter δ Q 1)| +
        |CB.tc (CB.crs (CB.lab p.1)) 3 - CB.tc (center Q) 3| ≤ eR) :
    ∀ᵐ p ∂CB.fieldLaw center δ δU δX C E lam,
      |CB.frame.resid (cfg.b k p.1) p.2 - transv C (CB.frame.zt p.2)
          (CB.frame.zZ (cfg.b k p.1) p.2) (CB.frame.tr (cfg.b k p.1) p.2) -
        quadZ (CB.pc (CB.crs (CB.lab p.1))) (CB.frame.zt p.2) (CB.frame.zZ (cfg.b k p.1) p.2) -
        CB.D2 (CB.lab p.1)| ≤ H * cfg.N k ^ (-v) + (E + eR + H * δ) * (K + K ^ 2) := by
  have hkeep : ∀ᵐ p ∂CB.fieldLaw center δ δU δX C E lam,
      p ∈ CB.fieldCapture center δ δU δX C E :=
    ae_restrict_mem (CB.measurableSet_fieldCapture center δ δU δX C E hb)
  have hac : CB.fieldLaw center δ δU δX C E lam ≪ lam :=
    Measure.absolutelyContinuous_of_le (CB.fieldLaw_le center δ δU δX C E lam)
  have hfit := (Measure.absolutelyContinuous_of_le hlam).ae_le CB.fit2
  have hH : 0 ≤ H := zero_le_one.trans CB.H_one
  filter_upwards [hkeep, hac.ae_le hU, hac.ae_le hagree, hac.ae_le hfit] with p hp hUp ha hf
  let γ := CB.crs (CB.lab p.1)
  let Q := sigmaState CB.frame δ δU δX (cfg.b k p.1) p.2
  have hc := stateField_recovery CB.tc center hH hδ γ Q (CB.tc_bd γ) rfl rfl ha C hp
  have hc₂ : |CB.tc γ 3 - C 3| ≤ E + eR + H * δ := hc.2.trans
    (le_add_of_nonneg_right (mul_nonneg hH hδ.le))
  have htr := transv_error hc.1 hc₂ hUp
  have hid : CB.frame.resid (cfg.b k p.1) p.2 -
      transv C (CB.frame.zt p.2) (CB.frame.zZ (cfg.b k p.1) p.2) (CB.frame.tr (cfg.b k p.1) p.2) -
      quadZ (CB.pc γ) (CB.frame.zt p.2) (CB.frame.zZ (cfg.b k p.1) p.2) - CB.D2 (CB.lab p.1) =
      (CB.frame.resid (cfg.b k p.1) p.2 -
        quadZ (CB.pc γ) (CB.frame.zt p.2) (CB.frame.zZ (cfg.b k p.1) p.2) - CB.D2 (CB.lab p.1) -
        transv (CB.tc γ) (CB.frame.zt p.2) (CB.frame.zZ (cfg.b k p.1) p.2) (CB.frame.tr (cfg.b k p.1) p.2)) +
      (transv (CB.tc γ) (CB.frame.zt p.2) (CB.frame.zZ (cfg.b k p.1) p.2) (CB.frame.tr (cfg.b k p.1) p.2) -
        transv C (CB.frame.zt p.2) (CB.frame.zZ (cfg.b k p.1) p.2) (CB.frame.tr (cfg.b k p.1) p.2)) := by ring
  rw [hid]
  refine (abs_add_le _ _).trans ?_
  calc _ ≤ H * cfg.N k ^ (-v) +
        ((E + eR + H * δ) * K + (E + eR + H * δ) * K ^ 2) := add_le_add hf htr
    _ = _ := by ring

end ComparedBlock

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
