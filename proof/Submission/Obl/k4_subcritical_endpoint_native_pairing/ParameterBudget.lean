/- Adapted from this LOT tree, obligation o249, session x0876, commit 62801b543db15394ef6e0ef94c4a2e234b73e26a,
   Submission/Obl/k4_horizontal_endpoint_three_projections/ParameterBudget.lean.
   Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_endpoint_native_pairing.ParameterGrid

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing

open scoped BigOperators

/-- The number of parameter cells per native label is integrated against the
original palette. It costs no inverse power of the velocity-bin width. -/
theorem native_parameter_reference_budget {ι : Type*} [Fintype ι]
    (V : Finset ℤ) (weight : ℤ → ℝ) (menus : ι → ℤ → Finset (Fin 2 → ℤ))
    (prior : ι → ℝ) {K q g D a d : ℝ}
    (hK : 1 ≤ K) (hq : 0 < q) (hg : 0 < g) (ha : 0 < a)
    (hw : ∀ v ∈ V, 0 ≤ weight v) (hsum : (∑ v ∈ V, weight v) ≤ 1)
    (hcount : ∀ i v, v ∈ V →
      ((menus i v).card : ℝ) * D ^ 2 ≤ 4096 * K ^ 5 * q ^ 2 * g)
    (hprior : ∀ i, a ^ d * q ^ 2 * g / K ≤ prior i)
    (hbudget : (∑ i, q * prior i) ≤ 1) :
    (∑ i, ∑ v ∈ V, ∑ _r ∈ menus i v, q * D ^ 2 * a ^ d * weight v) ≤
      4096 * K ^ 6 := by
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have had : 0 < a ^ d := Real.rpow_pos_of_pos ha _
  have hp (i : ι) : 0 ≤ prior i := by
    exact (by positivity : 0 ≤ a ^ d * q ^ 2 * g / K).trans (hprior i)
  have hterm (i : ι) (v : ℤ) (hv : v ∈ V) :
      (∑ _r ∈ menus i v, q * D ^ 2 * a ^ d * weight v) ≤
        4096 * K ^ 6 * (q * prior i) * weight v := by
    have hwv := hw v hv
    rw [Finset.sum_const, nsmul_eq_mul]
    calc
      _ = (q * a ^ d * weight v) * (((menus i v).card : ℝ) * D ^ 2) := by ring
      _ ≤ (q * a ^ d * weight v) * (4096 * K ^ 5 * q ^ 2 * g) :=
        mul_le_mul_of_nonneg_left (hcount i v hv) (by positivity)
      _ = (4096 * K ^ 5 * q * weight v) * (a ^ d * q ^ 2 * g) := by ring
      _ ≤ (4096 * K ^ 5 * q * weight v) * (K * prior i) := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        simpa only [mul_comm K] using (div_le_iff₀ hKp).mp (hprior i)
      _ = _ := by ring
  calc
    _ ≤ ∑ i, ∑ v ∈ V, 4096 * K ^ 6 * (q * prior i) * weight v :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun v hv => hterm i v hv))
    _ = ∑ i, (4096 * K ^ 6 * (q * prior i)) * (∑ v ∈ V, weight v) := by
      simp_rw [Finset.mul_sum]
    _ ≤ ∑ i, 4096 * K ^ 6 * (q * prior i) := by
      apply Finset.sum_le_sum
      intro i _
      have hpi := hp i
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 4096 * K ^ 6 * (∑ i, q * prior i) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hbudget (by positivity : 0 ≤ 4096 * K ^ 6)

end Submission.Obl.k4_subcritical_endpoint_native_pairing
