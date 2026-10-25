-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.RecordStripBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordWidth

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter

noncomputable section

/-- The final K/4 state strip fits the original front strip, with its
literal factor 4^100 and the actual path/frame factors. -/
theorem record_display_strip_budget
    {N κ display frontExponent geometryExponent pathExponent margin : ℝ}
    (hN : 1 ≤ N) (hκ : 0 ≤ κ) (hκN : κ ≤ N^pathExponent)
    (hconstant : (4:ℝ)^100 ≤ N^margin)
    (hmargin : margin-100*display+pathExponent+geometryExponent ≤ -frontExponent) :
    (N^display/4)^(-100:ℝ)*κ*N^geometryExponent ≤ N^(-frontExponent) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hpower : (N^display)^100=N^(100*display) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hNp.le]
    congr 1
    ring
  have hwidth : (N^display/4)^(-100:ℝ)=(4:ℝ)^100*N^(-100*display) := by
    have hnegative : (N^display/4)^(-100:ℝ)=((N^display/4)^100)⁻¹ := by
      rw [Real.rpow_neg (by positivity : (0:ℝ)≤N^display/4) (100:ℝ)]
      norm_cast
    rw [hnegative,div_pow,inv_div,hpower,div_eq_mul_inv,←Real.rpow_neg hNp.le]
    congr 1
    congr 1
    ring
  rw [hwidth]
  calc
    _ ≤ ((4:ℝ)^100*N^(-100*display))*N^pathExponent*N^geometryExponent :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκN (by positivity))
        (Real.rpow_nonneg hNp.le _)
    _ ≤ (N^margin*N^(-100*display))*N^pathExponent*N^geometryExponent := by gcongr
    _ = N^(margin-100*display+pathExponent+geometryExponent) := by
      rw [←Real.rpow_add hNp,←Real.rpow_add hNp,←Real.rpow_add hNp]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN hmargin

/-- Wider original-velocity strips use the same path factor, without
changing the final displayed K or the already selected source. -/
theorem record_wide_strip_budget
    {N κ widthExponent frontExponent geometryExponent pathExponent : ℝ}
    (hN : 1 ≤ N) (hκ : 0 ≤ κ) (hκN : κ ≤ N^pathExponent)
    (hwidth : frontExponent+pathExponent+geometryExponent ≤ widthExponent) :
    N^(-widthExponent)*κ*N^geometryExponent ≤ N^(-frontExponent) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  calc
    _ ≤ N^(-widthExponent)*N^pathExponent*N^geometryExponent :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκN (Real.rpow_nonneg hNp.le _))
        (Real.rpow_nonneg hNp.le _)
    _ = N^(-widthExponent+pathExponent+geometryExponent) := by
      rw [←Real.rpow_add hNp,←Real.rpow_add hNp]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- One pre-sample path exponent resolves BOTH the literal final state
strip and the much wider native preparation strip N^(-2 frontExponent).
Apply original_record_strip_width to either scalar bound for every
actual ancestor matrix, without a root count or absolute-depth cost. -/
theorem eventually_record_original_strip_budgets
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    {display frontExponent geometryExponent : ℝ}
    (hfront : 0 < frontExponent) (hdisplay : frontExponent ≤ display)
    (hgeometry : geometryExponent ≤ frontExponent/4) :
    ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ κ : ℝ, 1 ≤ κ → κ ≤ N k^sigma →
        (N k^display/4)^(-100:ℝ)*κ*N k^geometryExponent ≤ N k^(-frontExponent) ∧
        N k^(-(2*frontExponent))*κ*N k^geometryExponent ≤ N k^(-frontExponent) := by
  let sigma := min 1 (frontExponent/4)
  have hsigma : 0 < sigma := lt_min one_pos (by positivity)
  have hsigmaF : sigma ≤ frontExponent/4 := min_le_right _ _
  have hdisplay0 : 0 < display := hfront.trans_le hdisplay
  have hlarge := ((tendsto_rpow_atTop hdisplay0).comp hN).eventually
    (eventually_ge_atTop ((4:ℝ)^100))
  refine ⟨sigma,hsigma,min_le_left _ _,?_⟩
  filter_upwards [hN.eventually (eventually_ge_atTop 1),hlarge] with k hk hc
  intro κ hκ hκN
  have hκ0 : 0 ≤ κ := zero_le_one.trans hκ
  exact ⟨record_display_strip_budget hk hκ0 hκN hc (by linarith),
    record_wide_strip_budget hk hκ0 hκN (by linarith)⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
