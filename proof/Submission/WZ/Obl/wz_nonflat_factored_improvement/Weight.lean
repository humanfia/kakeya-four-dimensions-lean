-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.Weight.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Basic

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

/-- Separation of the coefficient dependence from the cardinality dependence. -/
theorem weight_factor {δ m : ℝ} (hδ : 0 < δ) (hm : 0 < m)
    (σ : ℝ) (n : ℕ) :
    weight σ δ m n = m ^ ((3 / 2 : ℝ) * σ - 1) *
      ((n : ℝ) * δ ^ 2 * ((n : ℝ) * δ) ^ (-σ)) := by
  unfold weight
  rw [Real.mul_rpow (Real.rpow_nonneg hm.le _) (by positivity),
    ← Real.rpow_mul hm.le]
  have hpow : m⁻¹ * m ^ ((-(3 / 2 : ℝ)) * (-σ)) =
      m ^ ((3 / 2 : ℝ) * σ - 1) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hm]
    congr 1
    ring
  calc
    _ = (m⁻¹ * m ^ ((-(3 / 2 : ℝ)) * (-σ))) *
        ((n : ℝ) * δ ^ 2 * ((n : ℝ) * δ) ^ (-σ)) := by ring
    _ = _ := by rw [hpow]

/-- The target decreases when its supplied convex-count coefficient increases. -/
theorem weight_mono_coefficient {δ m M σ : ℝ} (hδ : 0 < δ) (hm : 0 < m)
    (hmM : m ≤ M) (hσ : σ ≤ 2 / 3) (n : ℕ) :
    weight σ δ M n ≤ weight σ δ m n := by
  rw [weight_factor hδ (hm.trans_le hmM), weight_factor hδ hm]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact Real.rpow_le_rpow_of_nonpos hm hmM (by linarith)

/-- This is the loss-free comparison needed to apply `D` to a family whose convex count is small. -/
theorem weight_le_normalized {δ m σ : ℝ} (hδ : 0 < δ) (hm : 1 ≤ m)
    (hσ : σ ≤ 2 / 3) (n : ℕ) :
    weight σ δ m n ≤ (n : ℝ) * δ ^ 2 * ((n : ℝ) * δ) ^ (-σ) := by
  simpa [weight] using weight_mono_coefficient hδ zero_lt_one hm hσ n

/-- The two normalizations cancel exactly when the number of fine tubes is `q * N`. -/
theorem coarse_fine_product_identity {δ b m q N : ℝ}
    (hδ : 0 < δ) (hb : 0 < b) (hm : 0 < m) (hq : 0 < q) (hN : 0 < N)
    (σ ω u e A B : ℝ) :
    (A * b ^ (ω + e) * (q * b ^ 2) * (q * b) ^ (-σ)) *
      (B * δ ^ e * (δ / b) ^ u * m⁻¹ * (N * (δ / b) ^ 2) *
        (m ^ (-(3 / 2 : ℝ)) * (N * (δ / b))) ^ (-σ)) =
    (A * B) * δ ^ (u + e) * b ^ (ω - u + e) *
      (m⁻¹ * ((q * N) * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * ((q * N) * δ)) ^ (-σ)) := by
  have hbase : (q * b) * (m ^ (-(3 / 2 : ℝ)) * (N * (δ / b))) =
      m ^ (-(3 / 2 : ℝ)) * ((q * N) * δ) := by field_simp
  have hσcancel : (q * b) ^ (-σ) *
      (m ^ (-(3 / 2 : ℝ)) * (N * (δ / b))) ^ (-σ) =
      (m ^ (-(3 / 2 : ℝ)) * ((q * N) * δ)) ^ (-σ) := by
    rw [← Real.mul_rpow (by positivity) (by positivity), hbase]
  have hpowers : b ^ (ω + e) * δ ^ e * (δ / b) ^ u =
      δ ^ (u + e) * b ^ (ω - u + e) := by
    rw [Real.div_rpow hδ.le hb.le, Real.rpow_add hδ]
    rw [show ω - u + e = (ω + e) - u by ring, Real.rpow_sub hb]
    ring
  have hscale : (q * b ^ 2) * (N * (δ / b) ^ 2) = (q * N) * δ ^ 2 := by
    field_simp
  calc
    _ = (A * B) * (b ^ (ω + e) * δ ^ e * (δ / b) ^ u) *
        (m⁻¹ * ((q * b ^ 2) * (N * (δ / b) ^ 2)) *
          ((q * b) ^ (-σ) * (m ^ (-(3 / 2 : ℝ)) * (N * (δ / b))) ^ (-σ))) := by ring
    _ = _ := by rw [hpowers, hscale, hσcancel]; ring

end WangZahlLot.Obl.wz_nonflat_factored_improvement
