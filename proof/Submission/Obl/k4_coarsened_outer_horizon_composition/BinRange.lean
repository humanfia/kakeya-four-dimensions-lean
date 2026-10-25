import Submission.Obl.k4_coarsened_outer_horizon_composition.Observations
import Submission.Obl.k4_profile_density_bounds.Common
import Submission.Obl.k4_scalar_lift_plank.Cells

namespace Submission.Obl.k4_coarsened_outer_horizon_composition

open Set

/-- A uniform polynomial-sized family of integer observation bins. -/
noncomputable def polynomialBins (N : ℝ) (M : ℕ) : Finset ℤ :=
  Finset.Icc (-⌈N ^ M⌉) ⌈N ^ M⌉

lemma mem_polynomialBins {N : ℝ} {M : ℕ} {j : ℤ} (hj : |(j : ℝ)| ≤ N ^ M) :
    j ∈ polynomialBins N M := by
  have hceil := Int.le_ceil (N ^ M)
  have h := abs_le.mp (hj.trans hceil)
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2

lemma polynomialBins_card {N : ℝ} (hN : 2 ≤ N) (M : ℕ) :
    ((polynomialBins N M).card : ℝ) ≤ N ^ (M + 4) := by
  have hN1 : 1 ≤ N := by linarith
  have hpow : 1 ≤ N ^ M := one_le_pow₀ hN1
  have hj : 0 ≤ ⌈N ^ M⌉ := Int.ceil_nonneg_of_neg_one_lt (by linarith)
  have hcard : ((polynomialBins N M).card : ℝ) = (⌈N ^ M⌉ : ℝ) + 1 - (-⌈N ^ M⌉ : ℤ) := by
    unfold polynomialBins
    rw [Int.card_Icc]
    exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ ⌈N ^ M⌉ + 1 - -⌈N ^ M⌉)
  have hN4 : (16 : ℝ) ≤ N ^ 4 := by
    exact (by norm_num : (16 : ℝ) = 2 ^ 4).le.trans
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 4)
  rw [hcard]
  calc
    _ ≤ 2 * (N ^ M + 1) + 1 := by
      have hc := Int.ceil_lt_add_one (N ^ M)
      push_cast
      linarith
    _ ≤ N ^ M * 16 := by nlinarith
    _ ≤ N ^ M * N ^ 4 := mul_le_mul_of_nonneg_left hN4 (by positivity)
    _ = _ := (pow_add _ _ _).symm

lemma delta_inv_le_pow_ceil {N : ℝ} (hN : 1 ≤ N) (r : ℝ) :
    (δ N r)⁻¹ ≤ N ^ ⌈r⌉₊ := by
  have hN0 : 0 < N := by linarith
  have hlo : N ^ (-r) ≤ δ N r :=
    (Submission.Obl.k4_profile_density_bounds.width_bounds hN0 r).1
  calc
    _ ≤ (N ^ (-r))⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hN0 _) hlo
    _ = N ^ r := by rw [Real.rpow_neg hN0.le, inv_inv]
    _ ≤ N ^ ⌈r⌉₊ := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hN (Nat.le_ceil r)

/-- Bounded coefficients, a polynomial scale B, and the exact dyadic thickness
put every native observation in a fixed polynomial-sized integer interval. -/
theorem native_bin_mem_polynomialBins {N B r : ℝ} {M Mb : ℕ}
    (hN : 2 ≤ N) (hB : 0 < B) (hBmax : B ≤ N ^ Mb) (l : Line) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (hl : ∀ e, |l.2 e| ≤ N ^ M) :
    (obs B (δ N r) (l, t)).2 ∈ polynomialBins N (M + Mb + ⌈r⌉₊ + 2) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hδ : 0 < δ N r := by unfold δ; positivity
  have hpos : |x l t 3| ≤ 2 * N ^ M := by
    change |l.2 2 + t * l.2 5| ≤ _
    calc
      _ ≤ |l.2 2| + |t| * |l.2 5| := (abs_add_le _ _).trans_eq (by rw [abs_mul])
      _ ≤ N ^ M + 1 * N ^ M := by rw [abs_of_nonneg ht.1]; gcongr <;> first | exact hl _ | exact ht.2
      _ = _ := by ring
  have hcoord : |B * x l t 3 / δ N r| ≤ 2 * N ^ (M + Mb + ⌈r⌉₊) := by
    rw [abs_div, abs_mul, abs_of_pos hB, abs_of_pos hδ, div_eq_mul_inv]
    calc
      _ ≤ N ^ Mb * (2 * N ^ M) * N ^ ⌈r⌉₊ := by
        gcongr
        exact delta_inv_le_pow_ceil hN1 r
      _ = _ := by simp only [pow_add]; ring
  have hfloor : |(⌊B * x l t 3 / δ N r⌋ : ℝ)| ≤ 2 * N ^ (M + Mb + ⌈r⌉₊) + 1 := by
    have herr := Submission.Obl.k4_scalar_lift_plank.abs_floor_sub (B * x l t 3 / δ N r)
    have hdecomp := abs_add_le ((⌊B * x l t 3 / δ N r⌋ : ℝ) - B * x l t 3 / δ N r)
      (B * x l t 3 / δ N r)
    have heq : (⌊B * x l t 3 / δ N r⌋ : ℝ) - B * x l t 3 / δ N r + B * x l t 3 / δ N r =
        (⌊B * x l t 3 / δ N r⌋ : ℝ) := by ring
    rw [heq] at hdecomp
    linarith
  have hpow : 1 ≤ N ^ (M + Mb + ⌈r⌉₊) := one_le_pow₀ hN1
  have hN2 : (4 : ℝ) ≤ N ^ 2 := by nlinarith
  apply mem_polynomialBins
  change |(⌊B * x l t 3 / δ N r⌋ : ℝ)| ≤ _
  apply hfloor.trans
  rw [pow_add N (M + Mb + ⌈r⌉₊) 2]
  nlinarith [mul_le_mul_of_nonneg_left hN2 (show 0 ≤ N ^ (M + Mb + ⌈r⌉₊) by positivity)]

end Submission.Obl.k4_coarsened_outer_horizon_composition
