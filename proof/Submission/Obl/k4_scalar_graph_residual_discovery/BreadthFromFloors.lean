/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file BreadthFromFloors.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.PosteriorFinalCaps
import Submission.Obl.k4_scalar_graph_residual_discovery.PaletteUnion
import Submission.Obl.k4_scalar_graph_residual_discovery.Breadth

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- Simultaneously restored original-state floors renew velocity breadth
in every union of whole fine states, under the SAME final current law. -/
theorem velocity_breadth_of_final_state_floors {X Q : Type*}
    [MeasurableSpace X] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (μ κ : Measure X) (hκ : κ ≤ μ) (state : X → Q) (hstate : Measurable state)
    (v : X → ℝ) (hv : Measurable v) {b : ℝ} (hb : 0 < b)
    (π : Measure ℤ) (old : Q → ℝ≥0∞) (C η pmax : ℝ≥0∞)
    (hη₀ : η ≠ 0) (hηt : η ≠ ∞)
    (hatom : ∀ q c, μ {p | state p = q ∧ (⌊v p / b⌋ : ℤ) = c} ≤ C * old q * π {c})
    (hfloor : ∀ q, κ (state ⁻¹' {q}) = 0 ∨ η * old q ≤ κ (state ⁻¹' {q}))
    (hπ : ∀ c, π {c} ≤ pmax) (hsmall : 5 * (C / η) * pmax ≤ 1 / 2)
    (S : Set Q) (w : ℝ) :
    (κ.restrict (state ⁻¹' S)) {p | |v p - w| ≤ b} ≤
      (1 / 2 : ℝ≥0∞) * κ (state ⁻¹' S) := by
  let code : X → ℤ := fun p => ⌊v p / b⌋
  have hcode : Measurable code := (hv.div_const b).floor
  have hfinal (q : Q) (c : ℤ) : κ {p | state p = q ∧ code p = c} ≤
      (C / η) * κ (state ⁻¹' {q}) * π {c} := by
    have hh := posterior_palette_cap_of_final_floors μ κ hκ state code old (fun _ => 1)
      (fun c => π {c}) C η hη₀ hηt hatom
      (by simpa only [mul_one] using hfloor) q (by norm_num) (by norm_num) c
    exact hh.trans_eq (by simp only [mul_one, div_eq_mul_inv]; ring)
  have hrect := Submission.Lib.K4ScalarActualSwitching.rectangular_palette_caps_of_atoms
    κ state hstate code hcode π (C / η) hfinal
  let A := state ⁻¹' S
  have hbin (c : ℤ) : (κ.restrict A) {p | (⌊v p / b⌋ : ℤ) = c} ≤
      (C / η) * (κ.restrict A) univ * pmax := by
    have hh := whole_state_union_palette_cap κ state hstate code hcode π (C / η) hrect
      S {c} (measurableSet_singleton c)
    have hh' := hh.trans (mul_le_mul_of_nonneg_left (hπ c) zero_le)
    change (κ.restrict A) (code ⁻¹' {c}) ≤ _
    rw [Measure.restrict_apply (hcode (measurableSet_singleton c)), Measure.restrict_apply_univ]
    have heq : code ⁻¹' {c} ∩ A = {p | state p ∈ S ∧ code p ∈ ({c} : Set ℤ)} := by
      ext p
      simp only [A, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq, and_comm]
    rw [heq]
    exact hh'
  have hunitbin (u : Unit) (c : ℤ) :
      (κ.restrict A) {p | (fun _ : X => ()) p = u ∧ (⌊v p / b⌋ : ℤ) = c} ≤
        (C / η) * (κ.restrict A) ((fun _ : X => ()) ⁻¹' {u}) * pmax := by
    cases u
    simpa using hbin c
  have hh := state_velocity_interval_cap (κ.restrict A) (fun _ : X => ()) v hb
    (C / η) pmax hunitbin () w
  have hinterval : (κ.restrict A) {p | |v p - w| ≤ b} ≤ 5 * (C / η) * κ A * pmax := by
    simpa using hh
  apply hinterval.trans
  calc
    5 * (C / η) * κ A * pmax = (5 * (C / η) * pmax) * κ A := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall zero_le

end

end Submission.Obl.k4_scalar_graph_residual_discovery
