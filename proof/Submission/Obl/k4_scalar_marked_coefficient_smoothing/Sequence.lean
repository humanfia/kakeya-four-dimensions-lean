import Submission.Obl.k4_scalar_marked_coefficient_smoothing.FrontEnd
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Growth
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Statement

namespace Submission.Obl.k4_scalar_marked_coefficient_smoothing

open MeasureTheory Set Filter
open scoped ENNReal

/-- Assemble finite rounding and marking with any polynomial fixed-model analytic loss. -/
theorem smoothing_of_local_raw_bound {A : ℝ} (hA : 2 ≤ A) {p : ℕ} (hp : 2 ≤ p)
    (hraw : LocalRawSmoothingBound A p) : SmoothingStatement := by
  intro N K hN hNt hK d s m C S U hd hd1 hs hsm hC hS hU hUm
    α inst ν μ b c angular hc hinput
  have hN1 (k : ℕ) : 1 ≤ N k := by linarith [hN k]
  have hNp (k : ℕ) : 0 < N k := by linarith [hN k]
  have hKp (k : ℕ) : 0 < K k := by linarith [hK.1 k]
  have hm : 0 < m := lt_trans hs hsm
  have hL : 0 ≤ 10 * (m + s + 1) := by positivity
  let D : (k : ℕ) → RoundedMarkedData (N k) (K k) s m (α k) (ν k) (μ k) (b k) :=
    fun k => Classical.choice (exists_rounded_marked_data (hN k) (hK.1 k)
      hs hsm (α k) (ν k) (μ k) (b k) (hinput k))
  let K' : ℕ → ℝ := fun k => A * K k ^ p
  have hKout (k : ℕ) : 2 * K k ^ 2 ≤ K' k := by
    have hpow := pow_le_pow_right₀ (hK.1 k) hp
    exact (mul_le_mul_of_nonneg_right hA (sq_nonneg (K k))).trans
      (mul_le_mul_of_nonneg_left hpow (by linarith))
  have hKout2 (k : ℕ) : 2 * K k ≤ K' k := by
    have hsmall : 2 * K k ≤ 2 * K k ^ 2 := by nlinarith [hK.1 k]
    exact hsmall.trans (hKout k)
  have hK' : Subpower N K' := subpower_polynomial hN1 hNt hK (by linarith) p
  let Q : ℝ := max (5 * (10 * (m + s + 1) + 3)) (m + 1)
  have hsizes : ∀ᶠ k in atTop,
      max ((D k).H : ℝ) ((D k).J : ℝ) ≤ N k ^ Q := by
    filter_upwards [hK.2 1 (by norm_num)] with k hk
    have hKN : K k ≤ N k := by simpa using hk
    apply max_le
    · have hH : ((D k).H : ℝ) ≤ N k ^ (5 * (10 * (m + s + 1) + 3)) :=
        (D k).coefficient_count.trans (by
          simpa only [neg_mul] using mesh_count_polynomial (hN k) (hK.1 k) hKN hL)
      exact hH.trans (Real.rpow_le_rpow_of_exponent_le (hN1 k) (le_max_left _ _))
    · exact ((D k).time_count.trans (time_count_polynomial (hN k))).trans
        (Real.rpow_le_rpow_of_exponent_le (hN1 k) (le_max_right _ _))
  obtain ⟨M, hM⟩ := uniform_nat_exponent hN hsizes
  refine ⟨K', hK', M, (fun k => (D k).H), (fun k => (D k).J),
    (fun k => (D k).b₀), (fun k => (D k).w), (fun k => (D k).mark),
    (fun k => (D k).tag), ?_, ?_, ?_⟩
  · intro k
    have hKk := hKp k
    refine ⟨(D k).time_pos, (le_max_left _ _).trans (hM k),
      (le_max_right _ _).trans (hM k), (D k).time_scale_lower,
      (D k).time_scale_upper, (D k).weight_nonneg, (D k).weight_sum, ?_, ?_⟩
    · intro j i
      have hδ1 : N k ^ (-10 * (m + s + 1)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (hN1 k) (by nlinarith)
      exact ((D k).coefficient_bound j i).trans
        ((by linarith [hK.1 k] : K k + N k ^ (-10 * (m + s + 1)) ≤ 2 * K k).trans
          (hKout2 k))
    · apply (ENNReal.ofReal_le_ofReal ?_).trans ((D k).mass_lower)
      simpa only [one_div] using div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
        (by positivity : 0 < 2 * K k ^ 2) (hKout k)
  · intro k
    have hKk := hKp k
    refine ⟨(D k).tag_measurable, (D k).weight_eq, (D k).rounding, ?_⟩
    intro j z hz
    have hJr : (0 : ℝ) < (D k).J := by exact_mod_cast (D k).time_pos
    have hfloor : (D k).w j / (((D k).J : ℝ) * K' k) ≤
        (D k).w j / (((D k).J : ℝ) * (2 * K k)) :=
      div_le_div_of_nonneg_left ((D k).weight_nonneg j) (by positivity)
        (mul_le_mul_of_nonneg_left (hKout2 k) hJr.le)
    exact (ENNReal.ofReal_le_ofReal hfloor).trans ((D k).mark_floor j z hz)
  · intro k
    exact hraw (N k) (K k) d s m S U (c k) (angular k)
      (hN k) (hK.1 k) hd hd1 hs hsm hS hU hUm
      ((Real.rpow_pos_of_pos (hNp k) _).trans_le (hc k).1)
      (α k) (ν k) (μ k) (b k) (hinput k)
      (D k).H (D k).J (D k).tag (D k).b₀ (D k).w (D k).mark
      (D k).time_pos (D k).time_scale_lower (D k).time_scale_upper
      (D k).weight_nonneg (D k).weight_sum (D k).coefficient_bound (D k).tag_measurable
      (D k).weight_eq (D k).rounding (D k).mark_floor

end Submission.Obl.k4_scalar_marked_coefficient_smoothing
