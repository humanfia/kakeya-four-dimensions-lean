-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.RealWeight.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Weight

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

noncomputable abbrev realWeight (σ δ m N : ℝ) : ℝ :=
  m⁻¹ * (N * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * (N * δ)) ^ (-σ)

theorem count_power_identity {C N : ℝ} (hC : 0 < C) (hN : 0 < N) (σ : ℝ) :
    N * (C * N) ^ (-σ) = C ^ (-σ) * N ^ (1 - σ) := by
  rw [Real.mul_rpow hC.le hN.le]
  have hh : N * N ^ (-σ) = N ^ (1 - σ) := by
    calc
      _ = N ^ (1 : ℝ) * N ^ (-σ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hN]; congr 1
  calc
    _ = C ^ (-σ) * (N * N ^ (-σ)) := by ring
    _ = _ := by rw [hh]

theorem count_power_mono {C N M σ : ℝ} (hC : 0 < C) (hN : 0 < N) (hNM : N ≤ M)
    (hσ : σ ≤ 1) : N * (C * N) ^ (-σ) ≤ M * (C * M) ^ (-σ) := by
  rw [count_power_identity hC hN, count_power_identity hC (hN.trans_le hNM)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hN.le hNM (by linarith)) (by positivity)

theorem count_power_fraction {C N M f σ : ℝ} (hC : 0 < C) (hN : 0 < N)
    (hf : 0 < f) (hf1 : f ≤ 1) (hNM : f * N ≤ M) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    f * (N * (C * N) ^ (-σ)) ≤ M * (C * M) ^ (-σ) := by
  have hM : 0 < M := (mul_pos hf hN).trans_le hNM
  rw [count_power_identity hC hN, count_power_identity hC hM]
  have hf' : f ≤ f ^ (1 - σ) := by
    conv_lhs => rw [← Real.rpow_one f]
    exact Real.rpow_le_rpow_of_exponent_ge hf hf1 (by linarith)
  have hh : f * N ^ (1 - σ) ≤ M ^ (1 - σ) := by
    calc
      _ ≤ f ^ (1 - σ) * N ^ (1 - σ) := mul_le_mul_of_nonneg_right hf' (by positivity)
      _ = (f * N) ^ (1 - σ) := (Real.mul_rpow hf.le hN.le).symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hNM (by linarith)
  nlinarith only [mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hC.le (-σ))]

theorem realWeight_fraction {δ m N M f σ : ℝ} (hδ : 0 < δ) (hm : 0 < m) (hN : 0 < N)
    (hf : 0 < f) (hf1 : f ≤ 1) (hNM : f * N ≤ M) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    f * realWeight σ δ m N ≤ realWeight σ δ m M := by
  have hh := count_power_fraction (C := m ^ (-(3 / 2 : ℝ)) * δ)
    (by positivity) hN hf hf1 hNM hσ0 hσ1
  have he (x : ℝ) : m ^ (-(3 / 2 : ℝ)) * δ * x = m ^ (-(3 / 2 : ℝ)) * (x * δ) := by ring
  simp only [he] at hh
  have hc : 0 ≤ m⁻¹ * δ ^ 2 := by positivity
  dsimp [realWeight]
  nlinarith only [mul_le_mul_of_nonneg_left hh hc]

theorem exact_two_scale_product {δ b a m D M N : ℝ}
    (hδ : 0 < δ) (hb : 0 < b) (ha : 0 < a) (hm : 0 < m) (hD : 0 < D)
    (hM : 0 < M) (hN : 0 < N) (σ ω u ε A B : ℝ) :
    (B * b ^ (ω + ε) * (M * b ^ 2) * (M * b) ^ (-σ)) *
      (A * (δ / b) ^ (u + ε) * m⁻¹ * (N * (δ / b) ^ 2) *
        (m ^ (-(3 / 2 : ℝ)) * D * (N * δ / a)) ^ (-σ)) =
    (A * B) * (D * b / a) ^ (-σ) * δ ^ (u + ε) * b ^ (ω - u) *
      realWeight σ δ m (M * N) := by
  have hbr : m ^ (-(3 / 2 : ℝ)) * D * (N * δ / a) =
      (D * b / a) * (m ^ (-(3 / 2 : ℝ)) * (N * (δ / b))) := by field_simp
  have hbrpow : (m ^ (-(3 / 2 : ℝ)) * D * (N * δ / a)) ^ (-σ) =
      (D * b / a) ^ (-σ) * (m ^ (-(3 / 2 : ℝ)) * (N * (δ / b))) ^ (-σ) := by
    rw [hbr, Real.mul_rpow (by positivity) (by positivity)]
  have hh := coarse_fine_product_identity hδ hb hm hM hN σ (ω + ε) (u + ε) 0 B
    (A * (D * b / a) ^ (-σ))
  simp only [add_zero, Real.rpow_zero, mul_one] at hh
  rw [show ω + ε - (u + ε) = ω - u by ring] at hh
  calc
    _ = (B * b ^ (ω + ε) * (M * b ^ 2) * (M * b) ^ (-σ)) *
        ((A * (D * b / a) ^ (-σ)) * (δ / b) ^ (u + ε) * m⁻¹ * (N * (δ / b) ^ 2) *
          (m ^ (-(3 / 2 : ℝ)) * (N * (δ / b))) ^ (-σ)) := by rw [hbrpow]; ring
    _ = _ := by rw [hh]; dsimp [realWeight]; ring

end WangZahlLot.Obl.wz_nonflat_factored_improvement
