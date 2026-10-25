/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Set MeasureTheory
open scoped BigOperators Interval

namespace Submission.Lib.K4PolynomialNorming

/-- The ideal affine base path, before leg `k`. -/
noncomputable def pathBasePrefix {E : Type*} [AddCommGroup E] [Module ℝ E]
    (c : E) (δ : ℕ → ℝ) (v : ℕ → E) (k : ℕ) : E :=
  c + ∑ i ∈ Finset.range k, δ i • v i

theorem pathBasePrefix_succ {E : Type*} [AddCommGroup E] [Module ℝ E]
    (c : E) (δ : ℕ → ℝ) (v : ℕ → E) (k : ℕ) :
    pathBasePrefix c δ v (k + 1) = pathBasePrefix c δ v k + δ k • v k := by
  simp only [pathBasePrefix, Finset.sum_range_succ]
  abel

/-- Approximate refreshes accumulate linearly in the number of legs. -/
theorem pathBasePrefix_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (c : ℕ → E) (δ : ℕ → ℝ) (v : ℕ → E) (η : ℝ)
    (hstep : ∀ k < N, ‖c (k + 1) - (c k + δ k • v k)‖ ≤ η) :
    ∀ k ≤ N, ‖c k - pathBasePrefix (c 0) δ v k‖ ≤ (k : ℝ) * η := by
  intro k
  induction k with
  | zero => intro _; simp [pathBasePrefix]
  | succ k ih =>
      intro hk
      have hprev := ih (by omega : k ≤ N)
      have hjump := hstep k (by omega)
      have heq : c (k + 1) - pathBasePrefix (c 0) δ v (k + 1) =
          (c (k + 1) - (c k + δ k • v k)) +
            (c k - pathBasePrefix (c 0) δ v k) := by
        rw [pathBasePrefix_succ]
        abel
      calc
        _ ≤ ‖c (k + 1) - (c k + δ k • v k)‖ +
            ‖c k - pathBasePrefix (c 0) δ v k‖ := by rw [heq]; exact norm_add_le _ _
        _ ≤ η + (k : ℝ) * η := add_le_add hjump hprev
        _ = _ := by simp only [Nat.cast_add, Nat.cast_one]; ring

theorem finite_height_errors_telescope (N : ℕ) (z g : ℕ → ℝ) (ε : ℝ)
    (hstep : ∀ k < N, |z (k + 1) - z k - g k| ≤ ε) :
    |z N - z 0 - ∑ k ∈ Finset.range N, g k| ≤ (N : ℝ) * ε := by
  have htel := Finset.sum_range_sub z N
  calc
    _ = |∑ k ∈ Finset.range N, (z (k + 1) - z k - g k)| := by
      rw [Finset.sum_sub_distrib, htel]
    _ ≤ ∑ k ∈ Finset.range N, |z (k + 1) - z k - g k| := by
      simpa only [Real.norm_eq_abs] using
        norm_sum_le (Finset.range N) (fun k => z (k + 1) - z k - g k)
    _ ≤ ∑ _k ∈ Finset.range N, ε := by
      apply Finset.sum_le_sum
      intro k hk
      exact hstep k (Finset.mem_range.mp hk)
    _ = _ := by simp

/-- The height error for finitely many signed legs, including noisy base
refreshes. Local Lipschitz control is needed only in the stated path region. -/
theorem noisy_path_height_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (c : ℕ → E) (δ : ℕ → ℝ) (v : ℕ → E) (z : ℕ → ℝ)
    (F : ℕ → E → ℝ) (hF : ∀ k, Continuous (F k)) (U : Set E)
    (ε η L : ℝ) (hη : 0 ≤ η) (hL : 0 ≤ L)
    (hδ : ∀ k < N, |δ k| ≤ 1)
    (hbase : ∀ k < N, ‖c (k + 1) - (c k + δ k • v k)‖ ≤ η)
    (hheight : ∀ k < N,
      |z (k + 1) - z k - ∫ s in (0:ℝ)..δ k, F k (c k + s • v k)| ≤ ε)
    (hU : ∀ k < N, ∀ s ∈ uIcc (0:ℝ) (δ k),
      c k + s • v k ∈ U ∧ pathBasePrefix (c 0) δ v k + s • v k ∈ U)
    (hLip : ∀ k < N, ∀ x ∈ U, ∀ y ∈ U, |F k x - F k y| ≤ L * ‖x - y‖) :
    |z N - z 0 - ∑ k ∈ Finset.range N,
      ∫ s in (0:ℝ)..δ k, F k (pathBasePrefix (c 0) δ v k + s • v k)| ≤
        (N : ℝ) * (ε + L * ((N : ℝ) * η)) := by
  apply finite_height_errors_telescope
  intro k hk
  have hbasek := pathBasePrefix_error N c δ v η hbase k (by omega)
  have hbaseN : ‖c k - pathBasePrefix (c 0) δ v k‖ ≤ (N : ℝ) * η := by
    apply hbasek.trans
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (le_of_lt hk)) hη
  have hact : IntervalIntegrable (fun s : ℝ => F k (c k + s • v k)) volume 0 (δ k) :=
    ((hF k).comp (continuous_const.add (continuous_id.smul continuous_const))).intervalIntegrable _ _
  have hideal : IntervalIntegrable
      (fun s : ℝ => F k (pathBasePrefix (c 0) δ v k + s • v k)) volume 0 (δ k) :=
    ((hF k).comp (continuous_const.add (continuous_id.smul continuous_const))).intervalIntegrable _ _
  have hdiff : |(∫ s in (0:ℝ)..δ k, F k (c k + s • v k)) -
      ∫ s in (0:ℝ)..δ k, F k (pathBasePrefix (c 0) δ v k + s • v k)| ≤
        L * ((N : ℝ) * η) := by
    rw [← intervalIntegral.integral_sub hact hideal]
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := δ k)
      (C := L * ((N : ℝ) * η))
      (f := fun s => F k (c k + s • v k) -
        F k (pathBasePrefix (c 0) δ v k + s • v k))
      (fun s hs => by
        have hmem := hU k hk s (uIoc_subset_uIcc hs)
        have h := hLip k hk _ hmem.1 _ hmem.2
        have heq : (c k + s • v k) - (pathBasePrefix (c 0) δ v k + s • v k) =
            c k - pathBasePrefix (c 0) δ v k := by abel
        rw [heq] at h
        simpa only [Real.norm_eq_abs] using h.trans
          (mul_le_mul_of_nonneg_left hbaseN hL))
    simp only [Real.norm_eq_abs, sub_zero] at hbound
    exact hbound.trans (mul_le_of_le_one_right (by positivity) (hδ k hk))
  calc
    _ ≤ |z (k + 1) - z k - ∫ s in (0:ℝ)..δ k, F k (c k + s • v k)| +
        |(∫ s in (0:ℝ)..δ k, F k (c k + s • v k)) -
          ∫ s in (0:ℝ)..δ k, F k (pathBasePrefix (c 0) δ v k + s • v k)| := by
      convert abs_add_le
        (z (k + 1) - z k - ∫ s in (0:ℝ)..δ k, F k (c k + s • v k))
        ((∫ s in (0:ℝ)..δ k, F k (c k + s • v k)) -
          ∫ s in (0:ℝ)..δ k, F k (pathBasePrefix (c 0) δ v k + s • v k)) using 1 <;> congr 1 <;> ring
    _ ≤ _ := add_le_add (hheight k hk) hdiff

end Submission.Lib.K4PolynomialNorming
