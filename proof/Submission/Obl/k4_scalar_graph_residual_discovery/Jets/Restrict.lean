/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file Jets/Restrict.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.Jets.Interface

set_option autoImplicit false

/-!
# Restricting a scalar-normal world

`ScalarNormal.restrict`: the hypotheses survive passing to a measurable label subset `E₁ ⊆ E`
that is still dense at the larger constant `K' ≥ K`.
-/

namespace Submission.Obl.k4_scalar_graph_residual_discovery.Jets

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

noncomputable section

theorem intervalAD_mono_const {ζ d K K' : ℝ} {X : Set ℝ} (hζ : 0 < ζ) (h : IntervalAD ζ d K X)
    (hK : K ≤ K') : IntervalAD ζ d K' X := by
  intro r R a hr hR
  obtain ⟨m, c, hc, hm⟩ := h r R a hr hR
  refine ⟨m, c, hc, hm.trans ?_⟩
  have hr0 : 0 < r := lt_of_lt_of_le hζ hr
  have : 0 ≤ (R / r) ^ d := Real.rpow_nonneg (div_nonneg (hr0.le.trans hR) hr0.le) _
  exact mul_le_mul_of_nonneg_right hK this

variable {Λ : Type*} [MeasurableSpace Λ]

theorem ScalarNormal.restrict {ν : Measure Λ} {c : Λ → Fin 5 → ℝ} {E : Set (Λ × ℝ)} {F : ℝ → ℝ}
    {piece : ℝ → Λ → Fin 5 → ℤ} {K ζ d : ℝ} (hSN : ScalarNormal ν c E F piece K ζ d)
    {E₁ : Set (Λ × ℝ)} (hsub : E₁ ⊆ E) (hE₁ : MeasurableSet E₁) {K' : ℝ} (hK : K ≤ K')
    (hdense : ENNReal.ofReal K'⁻¹ ≤ (ν.prod volume) E₁) : ScalarNormal ν c E₁ F piece K' ζ d where
  prob := hSN.prob
  one_le_K := hSN.one_le_K.trans hK
  zeta_pos := hSN.zeta_pos
  zeta_le_one := hSN.zeta_le_one
  measurable_c := hSN.measurable_c
  measurableSet_E := hE₁
  measurable_F := hSN.measurable_F
  measurable_piece := hSN.measurable_piece
  time_mem := fun p hp => hSN.time_mem p (hsub hp)
  coeff_le := fun p hp e => (hSN.coeff_le p (hsub hp) e).trans hK
  row_le := fun p hp => (hSN.row_le p (hsub hp)).trans hK
  dense := hdense
  support := fun t => intervalAD_mono_const hSN.zeta_pos
    ((hSN.support t).mono fun s ⟨l, hl, hs⟩ => ⟨l, hsub hl, hs⟩) hK
  abs_cap := by
    intro t a b q hq hq1
    have hq0 : 0 < q := lt_of_lt_of_le hSN.zeta_pos hq
    refine le_trans (measure_mono ?_) ((hSN.abs_cap t a b q hq hq1).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hq0.le _))))
    intro l hl
    exact ⟨hsub hl.1, hl.2⟩
  row_cmp := by
    intro p hp p' hp'
    refine (hSN.row_cmp p (hsub hp) p' (hsub hp')).trans ?_
    exact mul_le_mul_of_nonneg_right hK (by have := hSN.zeta_pos; positivity)
  resid_cmp := by
    intro p hp p' hp'
    refine (hSN.resid_cmp p (hsub hp) p' (hsub hp')).trans ?_
    exact mul_le_mul_of_nonneg_right hK (by have := hSN.zeta_pos; positivity)
  piece_diam := hSN.piece_diam
  bin_cap := by
    intro r hr hr1 b t a a' q hq hqr
    have hq0 : 0 < q := lt_of_lt_of_le hSN.zeta_pos hq
    have hr0 : 0 < r := lt_of_lt_of_le hSN.zeta_pos hr
    refine le_trans (measure_mono ?_) ((hSN.bin_cap r hr hr1 b t a a' q hq hqr).trans ?_)
    · intro l hl
      exact ⟨hl.1, hsub hl.2.1, hl.2.2⟩
    · gcongr

end

end Submission.Obl.k4_scalar_graph_residual_discovery.Jets
