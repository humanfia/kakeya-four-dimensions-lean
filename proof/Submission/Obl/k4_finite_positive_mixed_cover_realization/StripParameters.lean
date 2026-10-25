import Submission.Obl.k4_finite_positive_mixed_cover_realization.Grid
import Submission.Obl.k4_finite_positive_mixed_cover_realization.Path
import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripNumerics
import Submission.Obl.k4_fixed_menu_density_pruning.Outer

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

lemma strip_reciprocal_width {N b h L : ℝ} (hN : 1 ≤ N) (hb : 0 ≤ b)
    (hb1 : b ≤ 1 / 4) (hh : 0 ≤ h) (hh1 : h ≤ 1 / 8) (hL : 0 ≤ L) :
    (N ^ (-b * h * L / 8))⁻¹ ≤ N ^ (⌈L⌉₊ + 1) := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hbh := mul_le_mul hb1 hh1 hh (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hbhL := mul_le_mul_of_nonneg_right hbh hL
  calc
    _ = N ^ (b * h * L / 8) := by
      rw [show -b * h * L / 8 = -(b * h * L / 8) by ring, Real.rpow_neg hN0.le, inv_inv]
    _ ≤ N ^ ((⌈L⌉₊ + 1 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by
      have hceil := Nat.le_ceil L
      push_cast
      nlinarith)
    _ = _ := Real.rpow_natCast _ _

lemma PathData.Valid.strip_time_budget
    {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ gain ρ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → MeasureTheory.Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hs : FineGrid m s gain ρ) (hNk : 1 ≤ Nk) (hL : 0 ≤ L)
    (hκ₁ : 0 ≤ κ₁) (hκ₁1 : κ₁ ≤ 1) (hδ : δ₀ ≤ 1) {i : ℕ} (hi : i < m) :
    (2 : ℝ) ^ p.T i ≤ Nk ^ (Mp + ⌈2 * L⌉₊ + 4) := by
  have hsi := hs.bounds hi
  have hsκ : κ₁ * s i ≤ 1 :=
    (mul_le_mul_of_nonneg_left hsi.2 hκ₁).trans (by simpa using hκ₁1)
  apply (hp.level_bounds i hi).2.2.2.1.trans
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le hNk
  have h1 := mul_le_mul_of_nonneg_right (add_le_add hsκ hδ) hL
  have hc := Nat.le_ceil (2 * L)
  push_cast
  nlinarith

lemma strip_saving {b α ρ gain h L δ₀ : ℝ} (hb : 0 ≤ b) (hL : 0 ≤ L)
    (hgain : 0 ≤ gain) (hh : gain ≤ h) (hδ : δ₀ ≤ ρ * gain)
    (hρ : ρ ≤ b / 128) (hα : α ≤ b / 128) :
    δ₀ * L + (α * gain) * L ≤ b * h * L / 16 := by
  have h1 := mul_le_mul_of_nonneg_right hδ hL
  have h2 := mul_le_mul_of_nonneg_right hρ (mul_nonneg hgain hL)
  have h3 := mul_le_mul_of_nonneg_right hα (mul_nonneg hgain hL)
  have h4 := mul_le_mul_of_nonneg_left hh (mul_nonneg hb hL)
  have h5 := mul_nonneg (mul_nonneg hb hgain) hL
  nlinarith

lemma strip_mass_numerics {N ε ε₀ τ : ℝ} (hN : 1 ≤ N) (hε₀ : 0 < ε₀)
    (hε : ε ≤ ε₀) (hτ : 4 * ε₀ ≤ τ) (hlarge : 6 ≤ N ^ ε₀) :
    2 * N ^ (-16 * ε₀) + N ^ (-16 * ε₀) ≤ N ^ (-ε) / 2 ∧
      N ^ (-τ) ≤ N ^ (-ε) / 2 := by
  have h6 : 6 ≤ N ^ (16 * ε₀ / 2) := hlarge.trans
    (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
  have he := k4_fixed_menu_density_pruning.rpow_neg_le_div hN
    (show ε ≤ (16 * ε₀) / 2 by linarith) (by norm_num : (0 : ℝ) < 6) h6
  have h2 : 2 ≤ N ^ (τ / 2) := (show (2 : ℝ) ≤ 6 by norm_num).trans
    (hlarge.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)))
  refine ⟨?_, k4_fixed_menu_density_pruning.rpow_neg_le_div hN (by linarith)
    (by norm_num : (0 : ℝ) < 2) h2⟩
  have he' : N ^ (-16 * ε₀) ≤ N ^ (-ε) / 6 := by
    convert he using 1 <;> congr 1 <;> ring
  linarith

end Submission.Obl.k4_finite_positive_mixed_cover_realization
