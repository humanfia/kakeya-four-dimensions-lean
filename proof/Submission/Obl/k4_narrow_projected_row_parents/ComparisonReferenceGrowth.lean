import Submission.Obl.k4_narrow_projected_row_parents.Model
import Submission.Obl.k4_discrete_of_terminal_charts.Horizon

namespace Submission.Obl.k4_narrow_projected_row_parents

open Filter
open Submission.Obl.k4_discrete_of_terminal_charts

/-- The native cap constant in the finite comparison has a fixed polynomial
bound in the original loss. -/
theorem common_native_cap_bounds {K : ℝ} (hK : 1 ≤ K) :
    1 ≤ 27000000 * K * (2 * K + 5) ∧
      27000000 * K * (2 * K + 5) ≤ 189000000 * K ^ 2 := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hsmall : 2 * K + 5 ≤ 7 * K := by linarith
  constructor
  · have hprod : (1 : ℝ) * 7 ≤ K * (2 * K + 5) :=
      mul_le_mul hK (by linarith) (by norm_num) hK0
    nlinarith
  · calc
      _ ≤ 27000000 * K * (7 * K) := mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = _ := by ring

/-- For `0 ≤ d ≤ 1`, the reference numerator is bounded by one fixed
polynomial in the three subpower losses. -/
theorem common_comparison_reference_bounds {K H A d : ℝ}
    (hK : 1 ≤ K) (hH : 1 ≤ H) (hA : 1 ≤ A) (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    1 ≤ A ^ d * (475200 * K ^ 5 + 360 * H ^ 4 * K) ∧
      A ^ d * (475200 * K ^ 5 + 360 * H ^ 4 * K) ≤
        475560 * A * K ^ 5 * H ^ 4 := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hK5 : 1 ≤ K ^ 5 := one_le_pow₀ hK
  have hH4 : 1 ≤ H ^ 4 := one_le_pow₀ hH
  have hKle : K ≤ K ^ 5 := by
    simpa only [pow_one] using pow_le_pow_right₀ hK (by decide : 1 ≤ 5)
  have hsum1 : 1 ≤ 475200 * K ^ 5 + 360 * H ^ 4 * K := by
    have hp : 0 ≤ 360 * H ^ 4 * K := by positivity
    linarith
  have hsum : 475200 * K ^ 5 + 360 * H ^ 4 * K ≤ 475560 * K ^ 5 * H ^ 4 := by
    have hleft : 475200 * K ^ 5 ≤ 475200 * K ^ 5 * H ^ 4 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hH4
        (by positivity : 0 ≤ 475200 * K ^ 5)
    have hright : 360 * H ^ 4 * K ≤ 360 * H ^ 4 * K ^ 5 :=
      mul_le_mul_of_nonneg_left hKle (by positivity)
    calc
      _ ≤ 475200 * K ^ 5 * H ^ 4 + 360 * H ^ 4 * K ^ 5 := add_le_add hleft hright
      _ = _ := by ring
  constructor
  · simpa only [one_mul] using mul_le_mul (Real.one_le_rpow hA hd) hsum1
      (by norm_num : (0 : ℝ) ≤ 1) (Real.rpow_nonneg hA0 d)
  · calc
      _ ≤ A * (475560 * K ^ 5 * H ^ 4) :=
        mul_le_mul (Real.rpow_le_self_of_one_le hA hd1) hsum
          (zero_le_one.trans hsum1) hA0
      _ = _ := by ring

theorem common_native_cap_subpow {N K : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hKsub : Model.Subpow N K) :
    (∀ k, 1 ≤ 27000000 * K k * (2 * K k + 5)) ∧
      Model.Subpow N (fun k => 27000000 * K k * (2 * K k + 5)) := by
  have hK0 : ∀ k, 0 ≤ K k := fun k => zero_le_one.trans (hK k)
  have hNp : ∀ k, 0 < N k := fun k => zero_lt_one.trans_le (hN k)
  have hpow := subpower_pow hN hK0 hKsub 2
  have hpoly := subpower_mul hNp (fun _ => by norm_num) (fun k => sq_nonneg (K k))
    (subpower_const hNt 189000000) hpow
  refine ⟨fun k => (common_native_cap_bounds (hK k)).1, ?_⟩
  intro ε hε
  filter_upwards [hpoly ε hε] with k hk
  exact (common_native_cap_bounds (hK k)).2.trans hk

theorem common_comparison_reference_subpow {N K H A : ℕ → ℝ} {d : ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hH : ∀ k, 1 ≤ H k) (hA : ∀ k, 1 ≤ A k)
    (hKsub : Model.Subpow N K) (hHsub : Model.Subpow N H) (hAsub : Model.Subpow N A)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    (∀ k, 1 ≤ A k ^ d * (475200 * K k ^ 5 + 360 * H k ^ 4 * K k)) ∧
      Model.Subpow N (fun k => A k ^ d * (475200 * K k ^ 5 + 360 * H k ^ 4 * K k)) := by
  have hK0 : ∀ k, 0 ≤ K k := fun k => zero_le_one.trans (hK k)
  have hH0 : ∀ k, 0 ≤ H k := fun k => zero_le_one.trans (hH k)
  have hA0 : ∀ k, 0 ≤ A k := fun k => zero_le_one.trans (hA k)
  have hNp : ∀ k, 0 < N k := fun k => zero_lt_one.trans_le (hN k)
  have hK5 := subpower_pow hN hK0 hKsub 5
  have hH4 := subpower_pow hN hH0 hHsub 4
  have hAK := subpower_mul hNp hA0 (fun k => pow_nonneg (hK0 k) 5) hAsub hK5
  have hAKH := subpower_mul hNp (fun k => mul_nonneg (hA0 k) (pow_nonneg (hK0 k) 5))
    (fun k => pow_nonneg (hH0 k) 4) hAK hH4
  have hpoly := subpower_mul hNp (fun _ => by norm_num)
    (fun k => by positivity [hA0 k, hK0 k, hH0 k]) (subpower_const hNt 475560) hAKH
  refine ⟨fun k => (common_comparison_reference_bounds (hK k) (hH k) (hA k) hd hd1).1, ?_⟩
  intro ε hε
  filter_upwards [hpoly ε hε] with k hk
  apply (common_comparison_reference_bounds (hK k) (hH k) (hA k) hd hd1).2.trans
  simpa only [mul_assoc] using hk

/-- The same bound in the literal ratio convention of the single-index
comparison, when its error width is a subpower factor times the true width. -/
theorem common_comparison_reference_subpow_of_factor
    {N K H A width aTable : ℕ → ℝ} {d : ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hH : ∀ k, 1 ≤ H k) (hA : ∀ k, 1 ≤ A k)
    (hKsub : Model.Subpow N K) (hHsub : Model.Subpow N H) (hAsub : Model.Subpow N A)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (hw : ∀ k, 0 < width k)
    (hfactor : ∀ k, aTable k = A k * width k) :
    (∀ k, 1 ≤ (aTable k / width k) ^ d *
      (475200 * K k ^ 5 + 360 * H k ^ 4 * K k)) ∧
      Model.Subpow N (fun k => (aTable k / width k) ^ d *
        (475200 * K k ^ 5 + 360 * H k ^ 4 * K k)) := by
  have hratio (k : ℕ) : aTable k / width k = A k := by
    rw [hfactor k, mul_div_cancel_right₀ _ (hw k).ne']
  simpa only [hratio] using
    common_comparison_reference_subpow hN hNt hK hH hA hKsub hHsub hAsub hd hd1

end Submission.Obl.k4_narrow_projected_row_parents
