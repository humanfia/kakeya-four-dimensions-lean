/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file Breadth.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.SpatialCaps

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice

/-- A ceiling for the original velocity bins controls every short velocity
interval in a retained fine physical state. -/
theorem state_velocity_interval_cap {X Q : Type*} [MeasurableSpace X]
    (μ : Measure X) (state : X → Q) (v : X → ℝ) {b : ℝ} (hb : 0 < b)
    (C pmax : ENNReal)
    (hbin : ∀ q c, μ {p | state p = q ∧ (⌊v p / b⌋ : ℤ) = c} ≤
      C * μ (state ⁻¹' {q}) * pmax) (q : Q) (w : ℝ) :
    μ {p | state p = q ∧ |v p - w| ≤ b} ≤
      5 * C * μ (state ⁻¹' {q}) * pmax := by
  have hcell (z : Fin 1 → ℤ) :
      μ {p | state p = q ∧ cell b (fun _ : Fin 1 => v p) = z} ≤
        C * μ (state ⁻¹' {q}) * pmax := by
    apply (measure_mono (t := {p | state p = q ∧ (⌊v p / b⌋ : ℤ) = z 0}) ?_).trans (hbin q (z 0))
    intro p hp
    exact ⟨hp.1, congr_fun hp.2 0⟩
  have h := cube_cap_of_cell_caps μ {p | state p = q} (fun (p : X) (_ : Fin 1) => v p)
    hb (by positivity : 0 ≤ 3 * b) (C * μ (state ⁻¹' {q}) * pmax) hcell
    (fun _ : Fin 1 => w - b)
  have hsub : {p | state p = q ∧ |v p - w| ≤ b} ⊆
      {p | state p = q ∧ ∀ _j : Fin 1, v p ∈ Ico (w - b) (w - b + 3 * b)} := by
    intro p hp
    refine ⟨hp.1, fun _ => ?_⟩
    have hh := abs_le.mp hp.2
    constructor <;> linarith
  apply (measure_mono hsub).trans
  simpa only [mul_div_cancel_right₀ (3 : ℝ) hb.ne', pow_one,
    show (3 : ℝ) + 2 = 5 by norm_num, ENNReal.ofReal_ofNat, mul_assoc,
    mem_ofPred_eq] using h

/-- If no short velocity interval carries half the mass, at least half of
the original independent pair law has separated velocities. -/
theorem separated_pair_mass_ge_half {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (v : X → ℝ) (hv : Measurable v) (b : ℝ)
    (hcap : ∀ w, μ {p | |v p - w| ≤ b} ≤ (1 / 2 : ENNReal) * μ univ) :
    (1 / 2 : ENNReal) * (μ univ) ^ 2 ≤
      (μ.prod μ) {p | b < |v p.1 - v p.2|} := by
  let G : Set (X × X) := {p | b < |v p.1 - v p.2|}
  have hG : MeasurableSet G :=
    measurableSet_lt measurable_const ((hv.comp measurable_fst).sub (hv.comp measurable_snd)).abs
  have hnear : (μ.prod μ) Gᶜ ≤ (1 / 2 : ENNReal) * (μ univ) ^ 2 := by
    rw [Measure.prod_apply hG.compl]
    calc
      _ ≤ ∫⁻ _p, (1 / 2 : ENNReal) * μ univ ∂μ := by
        apply lintegral_mono
        intro p
        have heq : Prod.mk p ⁻¹' Gᶜ = {p' | |v p' - v p| ≤ b} := by
          ext p'
          simp only [G, mem_preimage, mem_compl_iff, mem_ofPred_eq, not_lt, abs_sub_comm]
        change μ (Prod.mk p ⁻¹' Gᶜ) ≤ (1 / 2 : ENNReal) * μ univ
        rw [heq]
        exact hcap (v p)
      _ = (1 / 2 : ENNReal) * (μ univ) ^ 2 := by rw [lintegral_const]; ring
  have hprod : (μ.prod μ) univ = (μ univ) ^ 2 := by
    simpa only [univ_prod_univ, pow_two] using Measure.prod_prod (μ := μ) (ν := μ) univ univ
  have hbudget : (μ univ) ^ 2 ≤ (μ.prod μ) G + (1 / 2 : ENNReal) * (μ univ) ^ 2 := by
    calc
      _ = (μ.prod μ) G + (μ.prod μ) Gᶜ :=
        hprod.symm.trans (measure_add_measure_compl hG).symm
      _ ≤ _ := add_le_add le_rfl hnear
  apply (ENNReal.add_le_add_iff_right (by finiteness :
    (1 / 2 : ENNReal) * (μ univ) ^ 2 ≠ ⊤)).1
  have hhalf : (1 / 2 : ENNReal) * (μ univ) ^ 2 +
      (1 / 2 : ENNReal) * (μ univ) ^ 2 = (μ univ) ^ 2 := by
    rw [← add_mul]
    simp only [one_div, ENNReal.inv_two_add_inv_two, one_mul]
  rw [hhalf]
  exact hbudget

theorem separated_pi_pair_mass_ge_half {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (v : X → ℝ) (hv : Measurable v) (b : ℝ)
    (hcap : ∀ w, μ {p | |v p - w| ≤ b} ≤ (1 / 2 : ENNReal) * μ univ) :
    (1 / 2 : ENNReal) * (μ univ) ^ 2 ≤
      Measure.pi (fun _ : Fin 2 => μ) {p | b < |v (p 0) - v (p 1)|} := by
  have hG : MeasurableSet {p : X × X | b < |v p.1 - v p.2|} :=
    measurableSet_lt measurable_const ((hv.comp measurable_fst).sub (hv.comp measurable_snd)).abs
  have hmap := (measurePreserving_finTwoArrow μ).measure_preimage hG.nullMeasurableSet
  have heq : MeasurableEquiv.finTwoArrow ⁻¹' {p : X × X | b < |v p.1 - v p.2|} =
      {p : Fin 2 → X | b < |v (p 0) - v (p 1)|} := by
    ext p
    rfl
  rw [heq] at hmap
  rw [hmap]
  exact separated_pair_mass_ge_half μ v hv b hcap

end Submission.Obl.k4_scalar_graph_residual_discovery
