-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.RecordGeometryPowers, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordGeometry

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter

noncomputable section

/-- Pay a fixed coefficient and a finite envelope power by a strict
exponent margin. The bound is uniform over all actual envelopes G. -/
theorem envelope_power_budget_of_margin
    {N G g margin exponent target coefficient : ℝ} (n : ℕ)
    (hN : 1 ≤ N) (hG0 : 0 ≤ G) (hG : G ≤ N^g)
    (hc0 : 0 ≤ coefficient) (hc : coefficient ≤ N^margin)
    (hexp : margin+g*(n:ℝ)+exponent ≤ target) :
    coefficient*G^n*N^exponent ≤ N^target := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hpower : G^n ≤ N^(g*(n:ℝ)) := by
    calc
      _ ≤ (N^g)^n := pow_le_pow_left₀ hG0 hG n
      _ = _ := by rw [←Real.rpow_natCast,←Real.rpow_mul hNp.le]
  calc
    _ ≤ coefficient*N^(g*(n:ℝ))*N^exponent :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpower hc0)
        (Real.rpow_nonneg hNp.le _)
    _ ≤ N^margin*N^(g*(n:ℝ))*N^exponent :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hNp.le _))
        (Real.rpow_nonneg hNp.le _)
    _ = N^(margin+g*(n:ℝ)+exponent) := by rw [←Real.rpow_add hNp,←Real.rpow_add hNp]
    _ ≤ N^target := Real.rpow_le_rpow_of_exponent_le hN hexp

/-- The four scalar resolutions of the genuine ancestor-record source
follow from linear depth margins. Only the deterministic frame
envelope G occurs; the actual record-count envelope stays separate. -/
theorem record_geometry_budgets_of_exponent_margins
    {N G g margin baseExponent hiddenExponent κ₁ δ₀ L si smid sstop : ℝ}
    (R J qcore : ℕ) (hN : 1 ≤ N) (hG0 : 0 ≤ G) (hG : G ≤ N^g)
    (hconstant : 24 ≤ N^margin)
    (hbase : margin+3*g+(κ₁*(si-sstop)+2*δ₀)*L ≤ baseExponent)
    (hcore : margin+((R+5:ℕ):ℝ)*g+(κ₁*(smid-sstop)+2*δ₀)*L ≤ 0)
    (hdepth : margin+8*g-((smid-si-2*δ₀)*L) ≤ hiddenExponent)
    (hclock : margin+(((qcore+7)*J+R+13:ℕ):ℝ)*g+
      (κ₁*(smid-sstop)+2*δ₀)*L ≤ hiddenExponent) :
    G^3*N^((κ₁*(si-sstop)+2*δ₀)*L) ≤ N^baseExponent ∧
    12*G^(R+5)*N^((κ₁*(smid-sstop)+2*δ₀)*L) ≤ 1 ∧
    8*G^8*N^(-((smid-si-2*δ₀)*L)) ≤ N^hiddenExponent ∧
    24*G^((qcore+7)*J+R+13)*N^((κ₁*(smid-sstop)+2*δ₀)*L) ≤ N^hiddenExponent := by
  refine ⟨?_,?_,?_,?_⟩
  · have hh := envelope_power_budget_of_margin 3 hN hG0 hG
      (by norm_num : (0:ℝ)≤1) (by linarith : (1:ℝ)≤N^margin)
      (by norm_num; linarith : margin+g*(3:ℕ)+(κ₁*(si-sstop)+2*δ₀)*L ≤ baseExponent)
    simpa only [one_mul] using hh
  · have hh := envelope_power_budget_of_margin (R+5) hN hG0 hG
      (by norm_num : (0:ℝ)≤12) (by linarith : (12:ℝ)≤N^margin)
      (by nlinarith : margin+g*((R+5:ℕ):ℝ)+(κ₁*(smid-sstop)+2*δ₀)*L ≤ 0)
    simpa only [Real.rpow_zero] using hh
  · exact envelope_power_budget_of_margin 8 hN hG0 hG (by norm_num) (by linarith)
      (by norm_num; linarith)
  · exact envelope_power_budget_of_margin ((qcore+7)*J+R+13) hN hG0 hG
      (by norm_num) hconstant (by nlinarith)

/-- A fixed positive margin is paid eventually, before choosing any
path or actual deterministic geometry envelope. -/
theorem eventually_record_geometry_power_budgets
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    {g margin baseExponent hiddenExponent κ₁ δ₀ L si smid sstop : ℝ}
    (R J qcore : ℕ) (hmargin : 0 < margin)
    (hbase : margin+3*g+(κ₁*(si-sstop)+2*δ₀)*L ≤ baseExponent)
    (hcore : margin+((R+5:ℕ):ℝ)*g+(κ₁*(smid-sstop)+2*δ₀)*L ≤ 0)
    (hdepth : margin+8*g-((smid-si-2*δ₀)*L) ≤ hiddenExponent)
    (hclock : margin+(((qcore+7)*J+R+13:ℕ):ℝ)*g+
      (κ₁*(smid-sstop)+2*δ₀)*L ≤ hiddenExponent) :
    ∀ᶠ k in atTop, ∀ G : ℝ, 0 ≤ G → G ≤ N k^g →
      G^3*N k^((κ₁*(si-sstop)+2*δ₀)*L) ≤ N k^baseExponent ∧
      12*G^(R+5)*N k^((κ₁*(smid-sstop)+2*δ₀)*L) ≤ 1 ∧
      8*G^8*N k^(-((smid-si-2*δ₀)*L)) ≤ N k^hiddenExponent ∧
      24*G^((qcore+7)*J+R+13)*N k^((κ₁*(smid-sstop)+2*δ₀)*L) ≤ N k^hiddenExponent := by
  have hlarge := ((tendsto_rpow_atTop hmargin).comp hN).eventually (eventually_ge_atTop 24)
  filter_upwards [hN.eventually (eventually_ge_atTop 1),hlarge] with k hk hc
  intro G hG0 hG
  exact record_geometry_budgets_of_exponent_margins R J qcore hk hG0 hG hc
    hbase hcore hdepth hclock

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
