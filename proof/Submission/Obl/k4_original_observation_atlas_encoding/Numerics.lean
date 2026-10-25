import Mathlib

namespace Submission.Obl.k4_original_observation_atlas_encoding

open Filter
open scoped ENNReal

theorem mass_retention_cutoff (τ : ℝ) (hτ : 0 < τ) :
    ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ ε : ℝ,
      ε ≤ τ / 4 → ε ≤ 1 / 8 → ∀ m : ℝ≥0∞,
      ENNReal.ofReal (N ^ (-ε)) ≤ m + 2 * ENNReal.ofReal ((N ^ (2 : ℕ))⁻¹) →
      ENNReal.ofReal (N ^ (-τ)) ≤ m := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (by positivity : 0 < τ / 2)).eventually (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max 8 A, (by norm_num), ?_⟩
  intro N hN ε hετ hε1 m hm
  have h8 : 8 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hlarge : 4 ≤ N ^ (τ / 2) := hA N ((le_max_right _ _).trans hN)
  have hgap : 4 ≤ N ^ (τ - ε) := hlarge.trans
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  have htarget : 4 * N ^ (-τ) ≤ N ^ (-ε) := by
    calc
      _ ≤ N ^ (τ - ε) * N ^ (-τ) :=
        mul_le_mul_of_nonneg_right hgap (Real.rpow_nonneg hN0.le _)
      _ = _ := by rw [← Real.rpow_add hN0]; congr 1; ring
  have hi : 2 * N⁻¹ ≤ (1 / 4 : ℝ) := by
    rw [← div_eq_mul_inv, div_le_iff₀ hN0]
    linarith
  have hinv : N⁻¹ ≤ N ^ (-ε) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have herr : 2 * (N ^ (2 : ℕ))⁻¹ ≤ (1 / 4 : ℝ) * N ^ (-ε) := by
    calc
      _ = (2 * N⁻¹) * N⁻¹ := by rw [← inv_pow, pow_two]; ring
      _ ≤ (1 / 4 : ℝ) * N⁻¹ := mul_le_mul_of_nonneg_right hi (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by norm_num)
  have hstrict : N ^ (-τ) + 2 * (N ^ (2 : ℕ))⁻¹ < N ^ (-ε) := by
    have hp : 0 < N ^ (-ε) := Real.rpow_pos_of_pos hN0 _
    linarith
  by_contra hnot
  have hupper : m ≤ ENNReal.ofReal (N ^ (-τ)) := (lt_of_not_ge hnot).le
  have hs : ENNReal.ofReal (N ^ (-ε)) ≤
      ENNReal.ofReal (N ^ (-τ) + 2 * (N ^ (2 : ℕ))⁻¹) := by
    calc
      _ ≤ m + 2 * ENNReal.ofReal ((N ^ (2 : ℕ))⁻¹) := hm
      _ ≤ ENNReal.ofReal (N ^ (-τ)) + 2 * ENNReal.ofReal ((N ^ (2 : ℕ))⁻¹) :=
        add_le_add hupper le_rfl
      _ = _ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  exact (not_le_of_gt ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < N ^ (-ε))).2 hstrict)) hs

theorem sum_error_bound {N : ℝ} (hN : 0 < N) (M C : ℕ)
    (hC : (C : ℝ) ≤ N ^ M) (e : Fin C → ℝ≥0∞)
    (he : ∀ b, e b ≤ ENNReal.ofReal ((N ^ (M + 2))⁻¹)) :
    ∑ b, e b ≤ ENNReal.ofReal ((N ^ (2 : ℕ))⁻¹) := by
  calc
    _ ≤ ∑ _b : Fin C, ENNReal.ofReal ((N ^ (M + 2))⁻¹) := Finset.sum_le_sum (fun b _ => he b)
    _ = ENNReal.ofReal ((C : ℝ) * (N ^ (M + 2))⁻¹) := by
      simp [ENNReal.ofReal_mul, ENNReal.ofReal_natCast, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (N ^ M * (N ^ (M + 2))⁻¹) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC (by positivity))
    _ = _ := by congr 1; rw [pow_add]; field_simp

end Submission.Obl.k4_original_observation_atlas_encoding
