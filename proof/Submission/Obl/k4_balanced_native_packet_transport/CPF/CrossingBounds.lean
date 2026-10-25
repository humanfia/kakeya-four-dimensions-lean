/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/CrossingBounds.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/CrossingBounds.lean. Earlier provenance is retained below. -/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.Definitions
import Submission.Obl.k4_scalar_lift_plank.Cells
import Submission.Obl.k4_profile_density_bounds.Common

/-! Uniform polynomial format bounds for the crossing construction.
The exponents here are fixed before any subpower slack tolerance.
-/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open Set

noncomputable section

def boundedHiddenBins (N : ℝ) (J : ℕ) : Finset ℤ := Finset.Icc (-⌈N ^ J⌉) ⌈N ^ J⌉

theorem mem_boundedHiddenBins {N x : ℝ} {J : ℕ} (h : |x| + 1 ≤ N ^ J) :
    ⌊x⌋ ∈ boundedHiddenBins N J := by
  have hf := Submission.Obl.k4_scalar_lift_plank.abs_floor_sub x
  have hb : |(⌊x⌋ : ℝ)| ≤ (⌈N ^ J⌉ : ℝ) := by
    have he := abs_add_le ((⌊x⌋ : ℝ) - x) x
    rw [sub_add_cancel] at he
    exact (he.trans (by linarith)).trans (Int.le_ceil _)
  rw [boundedHiddenBins, Finset.mem_Icc]
  constructor
  · exact_mod_cast (abs_le.mp hb).1
  · exact_mod_cast (abs_le.mp hb).2

theorem boundedHiddenBins_card {N : ℝ} (hN : 2 ≤ N) (J : ℕ) :
    ((boundedHiddenBins N J).card : ℝ) ≤ N ^ (J + 3) := by
  have hN1 : 1 ≤ N := by linarith
  have hpow : 1 ≤ N ^ J := one_le_pow₀ hN1
  have hceil0 : 0 ≤ ⌈N ^ J⌉ := Int.ceil_nonneg (by positivity)
  have hc : ((boundedHiddenBins N J).card : ℝ) = 2 * (⌈N ^ J⌉ : ℝ) + 1 := by
    rw [boundedHiddenBins, Int.card_Icc]
    have he : (⌈N ^ J⌉ + 1 - -⌈N ^ J⌉ : ℤ) = 2 * ⌈N ^ J⌉ + 1 := by ring
    rw [he]
    exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ 2 * ⌈N ^ J⌉ + 1)
  have hceil : (⌈N ^ J⌉ : ℝ) < N ^ J + 1 := Int.ceil_lt_add_one _
  have hcube : (8 : ℝ) ≤ N ^ 3 := by
    exact_mod_cast pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 3
  rw [hc]
  calc
    _ ≤ 8 * N ^ J := by linarith
    _ ≤ N ^ 3 * N ^ J := mul_le_mul_of_nonneg_right hcube (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem crossing_sample_count_bound {N κ : ℝ} (hN : 2 ≤ N) (hκ : 1 ≤ κ) (hκN : κ ≤ N) :
    4 * κ ^ 2 ≤ (⌈4 * κ ^ 2⌉₊ : ℝ) ∧ (⌈4 * κ ^ 2⌉₊ : ℝ) ≤ N ^ 5 := by
  have hN0 : 0 ≤ N := by linarith
  have hceil : (⌈4 * κ ^ 2⌉₊ : ℝ) < 4 * κ ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hsq : κ ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ (by linarith) hκN 2
  have hN2 : 1 ≤ N ^ 2 := one_le_pow₀ (by linarith : 1 ≤ N)
  have hN3 : (8 : ℝ) ≤ N ^ 3 := by
    exact_mod_cast pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 3
  refine ⟨Nat.le_ceil _, ?_⟩
  calc
    _ ≤ 5 * N ^ 2 := by linarith
    _ ≤ N ^ 3 * N ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

theorem crossing_format_bound {N : ℝ} (hN : 2 ≤ N) {M J C m : ℕ} {bins : Finset ℤ}
    (hC : (C : ℝ) ≤ N ^ M) (hbins : (bins.card : ℝ) ≤ N ^ J) (hm : (m : ℝ) ≤ N ^ 5) :
    N ^ M + (C : ℝ) * (bins.card * (5 + 4 * m)) ≤ N ^ (M + J + 10) := by
  have hN1 : 1 ≤ N := by linarith
  have hpow5 : 1 ≤ N ^ 5 := one_le_pow₀ hN1
  have hN4 : (16 : ℝ) ≤ N ^ 4 := by
    exact_mod_cast pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 4
  have hm' : 5 + 4 * (m : ℝ) ≤ N ^ 9 := by
    calc
      _ ≤ 9 * N ^ 5 := by linarith
      _ ≤ N ^ 4 * N ^ 5 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  have hprod : (C : ℝ) * (bins.card * (5 + 4 * m)) ≤ N ^ (M + J + 9) := by
    calc
      _ ≤ N ^ M * (N ^ J * N ^ 9) :=
        mul_le_mul hC (mul_le_mul hbins hm' (by positivity) (by positivity)) (by positivity) (by positivity)
      _ = _ := by simp only [pow_add]; ring
  have hM : N ^ M ≤ N ^ (M + J + 9) := pow_le_pow_right₀ hN1 (by omega)
  calc
    _ ≤ 2 * N ^ (M + J + 9) := by linarith
    _ ≤ N * N ^ (M + J + 9) := mul_le_mul_of_nonneg_right hN (by positivity)
    _ = _ := by rw [show M + J + 10 = M + J + 9 + 1 by omega, pow_succ]; ring

/-- Bounded source coefficients imply a fixed polynomial range for the hidden-bin index. -/
theorem hidden_signal_bound {N B r : ℝ} {Mb Ml R : ℕ} (hN : 2 ≤ N)
    (hB : 0 ≤ B) (hBN : B ≤ N ^ Mb) (hr : r ≤ R)
    (l : Trajectory) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hl : ∀ e, |l.2 e| ≤ N ^ Ml) :
    |B * (x l t) 3 / δ N r| + 1 ≤ N ^ (Mb + Ml + R + 2) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hδ : 0 < δ N r := by unfold δ; positivity
  have hδlow : N ^ (-(R : ℝ)) ≤ δ N r :=
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)).trans
      (Submission.Obl.k4_profile_density_bounds.width_bounds hN0 r).1
  have hx : |(x l t) 3| ≤ 2 * N ^ Ml := by
    change |l.2 2 + t * l.2 5| ≤ _
    have ht0 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
    exact (abs_add_le _ _).trans (by
      rw [abs_mul]
      have := mul_le_mul ht0 (hl 5) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      linarith [hl 2])
  have hsig : |B * (x l t) 3 / δ N r| ≤ 2 * N ^ (Mb + Ml + R) := by
    rw [abs_div, abs_of_pos hδ, abs_mul, abs_of_nonneg hB]
    calc
      _ ≤ N ^ Mb * (2 * N ^ Ml) / N ^ (-(R : ℝ)) :=
        div_le_div₀ (by positivity) (mul_le_mul hBN hx (abs_nonneg _) (by positivity))
          (Real.rpow_pos_of_pos hN0 _) hδlow
      _ = _ := by rw [Real.rpow_neg hN0.le, Real.rpow_natCast, div_inv_eq_mul]; simp only [pow_add]; ring
  have hpow : 1 ≤ N ^ (Mb + Ml + R) := one_le_pow₀ hN1
  have hNsq : (4 : ℝ) ≤ N ^ 2 := by
    exact_mod_cast pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 2
  calc
    _ ≤ 4 * N ^ (Mb + Ml + R) := by linarith
    _ ≤ N ^ 2 * N ^ (Mb + Ml + R) := mul_le_mul_of_nonneg_right hNsq (by positivity)
    _ = _ := by rw [pow_add]; ring

end
end Submission.Obl.k4_balanced_native_packet_transport.CPF
