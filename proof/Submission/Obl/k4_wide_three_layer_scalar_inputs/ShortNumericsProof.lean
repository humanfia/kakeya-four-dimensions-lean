/- Inlined from LOT tree g-oai-074, obligation o202, session x0952,
commit 2fb339809fcfce34b26992c753e7b7c590ce76f7, file Submission/Obl/k4_horizontal_subcritical_rate_candidates/Wide/ShortNumericsProof.lean.
Numerical proof supplied in response to o274/x0969; namespace/imports renamed.
The target record originated on o274/x0969 commit9d747899. -/
import Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortBudget
import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Filter

/-- All short comparison losses are uniform in the original subpower constant
and the dyadic choice of `q`. The positive depth gap is used only in `q*g ≤ D`. -/
theorem shortNumericsAtHiddenDepthStatement : ShortNumericsAtHiddenDepthStatement := by
  intro N hN hNt κ s₀ s sp M e₀ hκ hκ1 hs₀ hs₀s hssp hspupper hM he₀
  have hss₀ : s < 3 * s₀ / 2 := hssp.trans_lt hspupper
  have hss : 0 < s - s₀ := sub_pos.mpr hs₀s
  let η₀ : ℝ := min (s₀ / 100) (κ * (s - s₀) / 2)
  have hη₀ : 0 < η₀ := by dsimp [η₀]; positivity
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη hηη₀
  have hηs : η ≤ s₀ / 100 := hηη₀.trans (min_le_left _ _)
  have hηgap : η ≤ κ * (s - s₀) / 2 := hηη₀.trans (min_le_right _ _)
  have hM0 : 0 < M := by linarith
  have hκs : κ * s ≤ s := mul_le_of_le_one_left (by linarith : 0 ≤ s) hκ1
  have hκs₀ : κ * s₀ ≤ s₀ := mul_le_of_le_one_left hs₀.le hκ1
  have hgap : 20 * s₀ - M / 4 < 0 := by linarith
  have hevR := hNt.eventually (Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le
    10000 (a := 0) (b := s₀) hs₀)
  have hevB := hNt.eventually (Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le
    1000 (a := 20 * s₀ - M / 4) (b := 0) hgap)
  filter_upwards [hevR, hevB] with k hRbig hbudget
  intro K q hK hKH hqlo hqhi
  have hN1 : 1 ≤ N k := by linarith [hN k]
  have hN0 : 0 < N k := by linarith [hN k]
  let R : ℝ := N k ^ s₀
  let H : ℝ := N k ^ η
  let a : ℝ := N k ^ (-sp)
  let g : ℝ := N k ^ (-κ * s)
  let D : ℝ := N k ^ (-2 * κ * s₀)
  let χ : ℝ := N k ^ (-M)
  let ζ : ℝ := N k ^ (-e₀)
  let w : ℝ := N k ^ (-M / 4)
  let mesh : ℝ := N k ^ (-2 * M)
  have hR0 : 0 < R := Real.rpow_pos_of_pos hN0 _
  have hH : 1 ≤ H := Real.one_le_rpow hN1 hη.le
  have hg0 : 0 < g := Real.rpow_pos_of_pos hN0 _
  have ha0 : 0 < a := Real.rpow_pos_of_pos hN0 _
  have hD0 : 0 < D := Real.rpow_pos_of_pos hN0 _
  have hχ0 : 0 < χ := Real.rpow_pos_of_pos hN0 _
  have hw0 : 0 < w := Real.rpow_pos_of_pos hN0 _
  have hK0 : 0 < K := by linarith
  have hRpow (j : ℕ) : R ^ j = N k ^ (s₀ * j) := by
    exact (Real.rpow_mul_natCast hN0.le _ _).symm
  have hbase : 1 / R ^ 2 = N k ^ (-2 * s₀) := by
    rw [hRpow, one_div, ← Real.rpow_neg hN0.le]
    congr 1
    ring
  have hHR : H ≤ R := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hH6 : H ^ 6 ≤ R := by
    dsimp [H, R]
    rw [← Real.rpow_mul_natCast hN0.le]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    norm_num
    linarith
  have hqbase : N k ^ (-κ * s - η) ≤ q := by
    calc
      _ = g / H := by dsimp [g, H]; rw [← Real.rpow_sub hN0]
      _ ≤ g / K := div_le_div_of_nonneg_left hg0.le hK0 hKH
      _ ≤ q := hqlo
  have hq : 1 / R ^ 2 ≤ q := by
    rw [hbase]
    exact (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)).trans hqbase
  have hq0 : 0 < q := (by positivity : 0 < 1 / R ^ 2).trans_le hq
  have hg : 1 / R ^ 2 ≤ g := by
    rw [hbase]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have ha : 1 / R ^ 2 ≤ a := by
    rw [hbase]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hD : 1 / R ^ 2 ≤ D := by
    rw [hbase]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hqH : q ≤ N k ^ (η - κ * s) := by
    calc
      q ≤ K * g := hqhi
      _ ≤ H * g := mul_le_mul_of_nonneg_right hKH hg0.le
      _ = _ := by dsimp [H, g]; rw [← Real.rpow_add hN0]; congr 1; ring
  have hq1 : q ≤ 1 := hqH.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by nlinarith))
  have ha1 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hmD : q * g ≤ D := by
    calc
      _ ≤ N k ^ (η - κ * s) * g := mul_le_mul_of_nonneg_right hqH hg0.le
      _ = N k ^ (η - 2 * κ * s) := by dsimp [g]; rw [← Real.rpow_add hN0]; congr 1; ring
      _ ≤ D := Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith)
  have hB : 1000 * R ^ 20 * w ≤ 1 := by
    simpa only [Real.rpow_zero] using (show 1000 * R ^ 20 * w ≤ N k ^ (0 : ℝ) from by
      convert hbudget using 1
      rw [hRpow]
      dsimp [w]
      rw [mul_assoc, ← Real.rpow_add hN0]
      congr 2
      ring)
  have hχw : χ ≤ w ^ 2 := by
    dsimp [χ, w]
    rw [← Real.rpow_mul_natCast hN0.le]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    norm_num
    linarith
  have hζχ : ζ ≤ χ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hmχ : mesh ≤ χ * w := by
    dsimp [mesh, χ, w]
    rw [← Real.rpow_add hN0]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    linarith
  have hfinal := shortNumerics_of_polynomial_budget (N := N k)
    (show 10000 ≤ R by simpa only [Real.rpow_zero, mul_one] using hRbig)
    hH hHR hH6 hq0 hg0 ha0 hD0 hq hg ha hD hq1 ha1 hmD hw0 hB
    hχ0.le hχw (Real.rpow_nonneg hN0.le _) hζχ (Real.rpow_nonneg hN0.le _) hmχ
  convert hfinal using 1 <;> dsimp [R, H, a, g, D, χ, ζ, w, mesh] <;>
    rw [← Real.rpow_mul_natCast hN0.le] <;> congr 1 <;> ring

/-- The original one-depth target follows by taking the two depths equal. -/
theorem shortNumericsStatement : ShortNumericsStatement := by
  intro N hN hNt κ s₀ s M e₀ hκ hκ1 hs₀ hs₀s hss₀ hM he₀
  exact shortNumericsAtHiddenDepthStatement N hN hNt κ s₀ s s M e₀
    hκ hκ1 hs₀ hs₀s le_rfl hss₀ hM he₀

end Submission.Obl.k4_wide_three_layer_scalar_inputs
