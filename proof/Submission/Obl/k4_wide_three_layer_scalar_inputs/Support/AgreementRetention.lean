import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.AgreeFinal

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open Set MeasureTheory Filter
open scoped ENNReal

noncomputable section

/-- The half-state conclusion of measured consensus transfers the original
conditional palette to its measurable restriction, with a factor two. -/
theorem consensus_restrict_palette {Ω Q V : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (μ : Measure Ω) [IsFiniteMeasure μ] (state : Ω → Q) (hstate : Measurable state)
    (vel : Ω → V) (palette : Set V → ℝ≥0∞) (C : ℝ≥0∞)
    (H : Set Ω)
    (hhalf : ∀ q, μ.real (H ∩ state ⁻¹' {q}) = 0 ∨
      μ.real (state ⁻¹' {q}) / 2 ≤ μ.real (H ∩ state ⁻¹' {q}))
    (hdom : ∀ q A, μ {p | state p = q ∧ vel p ∈ A} ≤ C * μ (state ⁻¹' {q}) * palette A) :
    ∀ q A, (μ.restrict H) {p | state p = q ∧ vel p ∈ A} ≤
      (2 * C) * (μ.restrict H) (state ⁻¹' {q}) * palette A := by
  intro q A
  have hs : MeasurableSet (state ⁻¹' {q}) := hstate (measurableSet_singleton q)
  have hreal : (μ.restrict H).real (state ⁻¹' {q}) = μ.real (H ∩ state ⁻¹' {q}) := by
    simp only [Measure.real, Measure.restrict_apply hs, inter_comm]
  have hsub : {p | state p = q ∧ vel p ∈ A} ⊆ state ⁻¹' {q} := by
    intro p hp
    exact hp.1
  rcases hhalf q with hz | hh
  · have hz' : (μ.restrict H) (state ⁻¹' {q}) = 0 := by
      have hh : ((μ.restrict H) (state ⁻¹' {q})).toReal = 0 := hreal.trans hz
      exact (ENNReal.toReal_eq_zero_iff _).mp hh |>.resolve_right (measure_ne_top _ _)
    exact (measure_mono hsub).trans (by rw [hz']; simp)
  · have hmass : μ (state ⁻¹' {q}) ≤ 2 * (μ.restrict H) (state ⁻¹' {q}) := by
      apply (ENNReal.toReal_le_toReal (measure_ne_top _ _)
        (ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _))).mp
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat]
      change μ.real (state ⁻¹' {q}) ≤ 2 * (μ.restrict H).real (state ⁻¹' {q})
      rw [hreal]
      linarith
    calc
      _ ≤ μ {p | state p = q ∧ vel p ∈ A} := Measure.restrict_le_self _
      _ ≤ C * μ (state ⁻¹' {q}) * palette A := hdom q A
      _ ≤ C * (2 * (μ.restrict H) (state ⁻¹' {q})) * palette A := by gcongr
      _ = _ := by ring

/-- Restriction keeps the exact mass of the consensus event in real units. -/
theorem consensus_restrict_real_mass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H : Set Ω) {loss : ℝ}
    (hmass : μ.real univ ≤ μ.real H + loss) :
    μ.real univ ≤ (μ.restrict H).real univ + loss := by
  simpa only [Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter] using hmass

/-- A real-valued agreement loss preserves a floor on the same original reference.
The only scalar condition is that the new floor and loss fit inside the old floor. -/
theorem consensus_restrict_mass_floor {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (H : Set Ω) {W : ℝ≥0∞} (hW : W ≠ ⊤)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hbudget : b + c ≤ a)
    (hfloor : ENNReal.ofReal a * W ≤ μ univ)
    (hloss : μ.real univ ≤ μ.real H + c * W.toReal) :
    ENNReal.ofReal b * W ≤ (μ.restrict H) univ := by
  have hfloorR : a * W.toReal ≤ μ.real univ := by
    simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha]
      using ENNReal.toReal_mono (measure_ne_top _ _) hfloor
  have hret : b * W.toReal ≤ μ.real H := by
    nlinarith only [hfloorR, hloss, mul_le_mul_of_nonneg_right hbudget (ENNReal.toReal_nonneg (a := W))]
  apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW)
    (measure_ne_top _ _)).mp
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal hb,
    Measure.restrict_apply MeasurableSet.univ, univ_inter] using hret

namespace ComparedBlock

open Submission.Obl.k4_critical_conditional_row_preparation

variable {α : Type} [MeasurableSpace α] {cfg : Data α} {k : ℕ} {s u v χ H : ℝ}
    (CB : ComparedBlock cfg k s u v χ H) (P : AgreeParams)

/-- The consensus event supplies exactly the state-center agreement consumed by
the native common-field application. -/
theorem agreement_restrict_agree (lam : Measure (α × ℝ))
    (center : (Fin 4 → ℤ) → CB.Γ) (Hc : Set (α × ℝ)) (hHc : MeasurableSet Hc)
    (hrel : ∀ p ∈ Hc, CB.Rg P (CB.sig P p) (CB.cls p) (center (CB.sig P p))) :
    ∀ᵐ p ∂lam.restrict Hc,
      let Q := sigmaState CB.frame P.δz P.δU P.δX (cfg.b k p.1) p.2
      |lin1 (CB.tc (CB.crs (CB.lab p.1))) (zcx P Q) (zcy P Q) -
        lin1 (CB.tc (center Q)) (zcx P Q) (zcy P Q)| +
        |CB.tc (CB.crs (CB.lab p.1)) 3 - CB.tc (center Q) 3| < P.eR := by
  filter_upwards [ae_restrict_mem hHc] with p hp
  exact hrel p hp

end ComparedBlock

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
