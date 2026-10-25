import Submission.Obl.k4_horizontal_wide_interval_return.Extraction

namespace Submission.Obl.k4_horizontal_wide_interval_return

open MeasureTheory Set

noncomputable section

/-- One occupied original sample bounds the constant coefficient, once the
three nonconstant affine coefficients have their horizontal slope bounds. -/
theorem affine_coefficients_of_sample (L : Fin 4 → ℝ)
    {K a H t Z Y X : ℝ} (hK : 1 ≤ K) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (ht : |t| ≤ 1) (hZ : |Z| ≤ K) (hY : |Y| ≤ K) (hX : |X| ≤ K)
    (hL : ∀ i : Fin 3, |L i.succ| ≤ H)
    (hfit : |X - (L 0 + L 1 * t + L 2 * Z + L 3 * Y)| ≤ K * a) :
    ∀ i, |L i| ≤ K * (1 + a) + H * (1 + 2 * K) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have h1 : |L 1 * t| ≤ H := by
    rw [abs_mul]
    exact (mul_le_mul (hL 0) ht (abs_nonneg _) hH).trans_eq (mul_one _)
  have h2 : |L 2 * Z| ≤ H * K := by
    rw [abs_mul]
    exact mul_le_mul (hL 1) hZ (abs_nonneg _) hH
  have h3 : |L 3 * Y| ≤ H * K := by
    rw [abs_mul]
    exact mul_le_mul (hL 2) hY (abs_nonneg _) hH
  have h0 : |L 0| ≤ K * (1 + a) + H * (1 + 2 * K) := by
    rw [abs_le] at hfit h1 h2 h3 hX ⊢
    constructor <;> linarith
  have hlarge : H ≤ K * (1 + a) + H * (1 + 2 * K) := by
    nlinarith [mul_nonneg hK0 ha, mul_nonneg hH hK0]
  intro i
  fin_cases i
  · exact h0
  · exact (hL 0).trans hlarge
  · exact (hL 1).trans hlarge
  · exact (hL 2).trans hlarge

theorem frame_graph_power_budget {N H J Q z : ℝ} (hN : 2 ≤ N)
    (hH0 : 0 ≤ H) (hH : H ≤ N ^ J) (hz0 : 0 ≤ z) (hz : z ≤ N ^ Q) :
    53 * H ^ 3 * z ^ 2 ≤ N ^ (3 * J + 2 * Q + 6) := by
  have hNpos : 0 < N := by linarith
  have h53 : (53 : ℝ) ≤ N ^ (6 : ℝ) := by
    simpa only [Real.rpow_ofNat] using
      (show (53 : ℝ) ≤ (2 : ℝ) ^ 6 by norm_num).trans
        (pow_le_pow_left₀ (by norm_num) hN 6)
  calc 53 * H ^ 3 * z ^ 2 ≤ 53 * (N ^ J) ^ 3 * (N ^ Q) ^ 2 := by gcongr
    _ ≤ N ^ (6 : ℝ) * (N ^ J) ^ 3 * (N ^ Q) ^ 2 := by gcongr
    _ = N ^ (3 * J + 2 * Q + 6) := by
      rw [← Real.rpow_mul_natCast hNpos.le, ← Real.rpow_mul_natCast hNpos.le,
        ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
      congr 1
      norm_num
      ring

theorem scalar_coefficient_room {N J : ℝ} (hN : 2 ≤ N) (hJ : 17 ≤ J) :
    2160 * N ^ (5 : ℕ) ≤ N ^ J := by
  have hNpos : 0 < N := by linarith
  have hroom : (2160 : ℝ) ≤ N ^ (12 : ℝ) := by
    simpa only [Real.rpow_ofNat] using
      (show (2160 : ℝ) ≤ (2 : ℝ) ^ 12 by norm_num).trans
        (pow_le_pow_left₀ (by norm_num) hN 12)
  calc 2160 * N ^ (5 : ℕ) ≤ N ^ (12 : ℝ) * N ^ (5 : ℕ) := by gcongr
    _ = N ^ (17 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_add hNpos]; norm_num
    _ ≤ N ^ J := Real.rpow_le_rpow_of_exponent_le (by linarith) hJ

theorem cell_inverse_power_bound {N K κ s q g : ℝ} {T : ℕ}
    (hN : 0 < N) (hK : K ≤ N) (hT : (2 : ℝ) ^ T ≤ K * N ^ (κ * s))
    (hq : q = ((2 : ℝ) ^ T)⁻¹) (hg : g = N ^ (-κ * s)) :
    (q * g)⁻¹ ≤ N ^ (1 + 2 * κ * s) := by
  have hg' : g = (N ^ (κ * s))⁻¹ := by
    rw [hg, neg_mul, Real.rpow_neg hN.le]
  rw [hq, hg', mul_inv, inv_inv, inv_inv]
  calc (2 : ℝ) ^ T * N ^ (κ * s) ≤ (K * N ^ (κ * s)) * N ^ (κ * s) := by gcongr
    _ ≤ (N * N ^ (κ * s)) * N ^ (κ * s) := by gcongr
    _ = (N ^ (1 : ℝ) * N ^ (κ * s)) * N ^ (κ * s) := by rw [Real.rpow_one]
    _ = N ^ (1 + 2 * κ * s) := by
      rw [← Real.rpow_add hN, ← Real.rpow_add hN]
      congr 1
      ring

/-- The fixed exponent used in the final coefficient budget follows from the
original dyadic time upper bound and fixed power bounds on the frame data. -/
theorem extractionAt_of_power_bounds {α : Type} [MeasurableSpace α]
    {N K η d s v m S U κ J : ℝ} {ν : Measure α} {ρ lam : Measure (α × ℝ)}
    {b : α → Fin 6 → ℝ} {T n : ℕ} {j : Fin n → Fin (2 ^ T)}
    {A B : Fin n → Set α} (i : Fin n) (Bs : Set α) (F : CellFrame)
    (hN : 2 ≤ N) (hK : K ≤ N) (hs : 0 < s) (hκ : 0 < κ) (hJ : 17 ≤ J)
    (hT : (2 : ℝ) ^ T ≤ K * N ^ (κ * s))
    (hinput : CellInput N η d v m S U ν lam b (A i) Bs F)
    (hlam : lam ≤ ρ) (hBs : Bs ⊆ B i)
    (hc : ∀ e, |F.c e| ≤ N ^ J) (hL : ∀ e, |F.L e| ≤ N ^ J)
    (hC : ∀ e, |F.C e| ≤ N ^ J)
    (ha : F.a = N ^ (-s)) (hq : F.q = ((2 : ℝ) ^ T)⁻¹)
    (hg : F.g = N ^ (-κ * s)) (hstart : F.t₀ = (j i : ℕ) / (2 : ℝ) ^ T) :
    ExtractionAt N η d s v m S U (3 * J + 4 * κ * s + 8) ν ρ b T n j A B := by
  have hNpos : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hH : 1 ≤ N ^ J := Real.one_le_rpow hN1 hJ0
  have hq1 : F.q ≤ 1 := by
    rw [hq]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hg1 : F.g ≤ 1 := by
    rw [hg]
    exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by nlinarith)
  have ha1 : F.a ≤ 1 := by
    rw [ha]
    exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have ht : |F.t₀| ≤ N ^ J := by
    apply le_trans _ hH
    rw [hstart, abs_of_nonneg (by positivity : 0 ≤ (j i : ℕ) / (2 : ℝ) ^ T)]
    apply (div_le_one (by positivity : 0 < (2 : ℝ) ^ T)).mpr
    exact_mod_cast (j i).isLt.le
  have hinv := cell_inverse_power_bound hNpos hK hT hq hg
  have hbudget : 53 * (N ^ J) ^ 3 * ((F.q * F.g)⁻¹) ^ 2 ≤
      N ^ (3 * J + 4 * κ * s + 8) := by
    convert frame_graph_power_budget hN (Real.rpow_nonneg hNpos.le _) le_rfl
      (inv_nonneg.mpr (mul_nonneg hinput.time_pos.le hinput.transverse_pos.le))
      hinv using 1 <;> congr 1 <;> ring
  exact ⟨i, lam, Bs, F, N ^ J, hinput, hlam, hBs, hH, hq1, hg1, ha1, ht,
    hc, hL, hC, scalar_coefficient_room hN hJ, hbudget, ha, hq, hstart⟩

end

end Submission.Obl.k4_horizontal_wide_interval_return
