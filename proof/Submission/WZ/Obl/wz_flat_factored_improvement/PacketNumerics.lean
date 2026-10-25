-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.PacketNumerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.FlatFineEstimate
import Submission.WZ.Obl.wz_flat_factored_improvement.FlatCordoba

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric

theorem power_retention_budget {δ ν s : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hνs : ν ≤ s) {K : ℕ} (hK : 0 < K) (hbudget : 224 * K * δ ^ s ≤ 1) :
    δ ^ (2 * s) ≤ δ ^ ν / (224 * K) ∧ δ ^ (2 * s) ≤ δ ^ ν / (4 * K) := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hρ : 0 < δ ^ s := Real.rpow_pos_of_pos hδ _
  have he : δ ^ (2 * s) = (δ ^ s) ^ (2 : ℕ) := by
    rw [← Real.rpow_mul_natCast hδ.le]
    congr 1
    norm_num
    ring
  have hν := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hνs
  have hret : δ ^ (2 * s) ≤ δ ^ ν / (224 * K) := by
    rw [le_div_iff₀ (by positivity), he]
    nlinarith [mul_le_mul_of_nonneg_right hbudget hρ.le]
  exact ⟨hret, hret.trans (div_le_div_of_nonneg_left (Real.rpow_nonneg hδ.le _)
    (by positivity) (by nlinarith))⟩

theorem power_raw_count_budget {δ ν s N n : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hνs : ν ≤ s) (hn : 0 ≤ n) (hret : δ ^ (2 * s) * n ≤ N) :
    δ ^ (-ν) * n ≤ δ ^ (-3 * s) * N := by
  calc
    _ ≤ δ ^ (-s) * n := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)) hn
    _ = δ ^ (-3 * s) * (δ ^ (2 * s) * n) := by
      rw [← mul_assoc, ← Real.rpow_add hδ]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hret (Real.rpow_nonneg hδ.le _)

noncomputable def flatCellDensity (σ u ε A δ a b s N : ℝ) : ℝ :=
  (A / 432) * δ ^ (ε + (4 + σ) * s) * (δ / a) ^ u *
    (a * b) ^ (-σ) * N ^ (σ / 2) * δ ^ (2 * σ)

theorem flatCellDensity_pos {σ u ε A δ a b s N : ℝ}
    (hA : 0 < A) (hδ : 0 < δ) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    0 < flatCellDensity σ u ε A δ a b s N := by unfold flatCellDensity; positivity

theorem flat_cell_factorization {σ u ε A δ a b s N : ℝ}
    (hA : 0 < A) (hδ : 0 < δ) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    flatCellDensity σ u ε A δ a b s N * (432 * a * b) =
      δ ^ s * (A * δ ^ ε * (δ / a) ^ u * (δ ^ (-3 * s))⁻¹ *
        (a * b) ^ (1 - σ) * (δ ^ (2 * s) * N) ^ (σ / 2) * δ ^ (2 * σ)) := by
  unfold flatCellDensity
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
    (by simp only [Set.mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_inv,
    Real.log_rpow, Real.log_pow]
  ring

theorem cordoba_power_budget {δ s η a b : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (ha : 0 < a) (hb : 0 < b) (hη : 8 * s ≤ η) (K : ℕ)
    (hbudget : (10 : ℝ) ^ (15 : ℕ) * ((K : ℝ) + 1) * δ ^ s ≤ 1) :
    δ ^ η * (a * b) ≤ (δ ^ (2 * s)) ^ (2 : ℕ) * a * b /
      ((10 : ℝ) ^ (15 : ℕ) * δ ^ (-3 * s) * (K + 1 : ℕ)) := by
  have hk : (0 : ℝ) < (K + 1 : ℕ) := by positivity
  apply le_trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hη) (mul_pos ha hb).le)
  apply (le_div_iff₀ (by positivity)).mpr
  have he : δ ^ (8 * s) * ((10 : ℝ) ^ (15 : ℕ) * δ ^ (-3 * s) * (K + 1 : ℕ)) =
      ((10 : ℝ) ^ (15 : ℕ) * ((K : ℝ) + 1) * δ ^ s) * (δ ^ (2 * s)) ^ (2 : ℕ) := by
    push_cast
    apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
      (by simp only [Set.mem_Ioi]; positivity)
    simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_pow]
    ring
  have hh := mul_le_mul_of_nonneg_right hbudget (by positivity : 0 ≤ (δ ^ (2 * s)) ^ (2 : ℕ) * (a * b))
  have he' := congrArg (fun z => z * (a * b)) he
  nlinarith only [he', hh]

theorem tube_number_power_bound : ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 100 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ (n : ℕ) (x v : Fin n → Space),
    (∀ i, ‖v i‖ = 1) → (∀ i, Tube δ (x i) (v i) ⊆ ball (0 : Space) 1) →
    (∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i))) → (n : ℝ) ≤ δ ^ (-10 : ℝ) := by
  obtain ⟨C, hC, H⟩ := WangZahlLot.wz_tube_packing_bound
  refine ⟨min (1 / 100) C⁻¹, by positivity, min_le_left _ _, ?_⟩
  intro δ hδ hδd n x v hv hball hsep
  have hδ100 := hδd.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := hδ100.trans (by norm_num)
  have hδC := hδd.trans (min_le_right _ _)
  have hCδ : C * δ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hδC hC.le
    simpa only [mul_inv_cancel₀ hC.ne'] using hh
  have hp := H δ hδ hδ100 n x v hv hball hsep
  have h5 : (n : ℝ) ≤ δ ^ (-5 : ℝ) := by
    rw [Real.rpow_neg hδ.le, Real.rpow_ofNat, inv_eq_one_div, le_div_iff₀ (pow_pos hδ 5)]
    nlinarith only [mul_le_mul_of_nonneg_right hp hδ.le, hCδ]
  exact h5.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num))

end WangZahlLot.Obl.wz_flat_factored_improvement
