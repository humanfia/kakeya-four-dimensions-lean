/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4CubicTests.SwitchedEndpoint
import Submission.Lib.K4PolynomialNorming.PathSimulation

open Set MeasureTheory MvPolynomial
open scoped Interval

namespace Submission.Lib.K4PolynomialNorming

-- The natural-prefix conversion is adapted from this session's own
-- Root.SwitchedEndpointBounds; the polynomial identity is imported from
-- the accepted K4CubicTests endpoint API.
private theorem published_prefix_during_leg {σ κ : Type*} [Fintype κ] [LinearOrder κ]
    (c : σ → ℝ) (v : κ → σ → ℝ) (δ : κ → ℝ) (k : κ) (s : ℝ) (a : σ) :
    c a + ∑ l : κ, (if l ≤ k then v l a * Function.update δ k s l else 0) =
      (c a + ∑ l : κ, if l < k then v l a * δ l else 0) + s * v k a := by
  classical
  have heach (l : κ) : (if l ≤ k then v l a * Function.update δ k s l else 0) =
      (if l < k then v l a * δ l else 0) + (if l = k then s * v k a else 0) := by
    rcases lt_trichotomy l k with hl | rfl | hl
    · simp [hl.le, hl.ne, hl, Function.update_of_ne hl.ne]
    · simp [mul_comm]
    · simp [not_le.mpr hl, not_lt.mpr hl.le, hl.ne']
  simp_rw [heach]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

private theorem published_height_eq_strictPrefix_integral {σ κ : Type*}
    [Fintype σ] [Fintype κ] [LinearOrder κ]
    (T : σ → MvPolynomial σ ℝ) (c : σ → ℝ) (v : κ → σ → ℝ) (δ : κ → ℝ) :
    MvPolynomial.eval δ (Submission.Lib.K4CubicTests.switchedEndpointHeight T c v) =
      ∑ k : κ, ∫ s in (0:ℝ)..δ k, ∑ a, v k a * MvPolynomial.eval
        (fun b => (c b + ∑ l : κ, if l < k then v l b * δ l else 0) + s * v k b) (T a) := by
  rw [Submission.Lib.K4CubicTests.eval_switchedEndpointHeight_eq_integral]
  simp_rw [published_prefix_during_leg]

private theorem fin_sum_lt_eq_range {M : Type*} [AddCommMonoid M]
    (N k : ℕ) (hk : k ≤ N) (f : ℕ → M) :
    (∑ i : Fin N, if (i : ℕ) < k then f i else 0) = ∑ i ∈ Finset.range k, f i := by
  change (∑ i : Fin N, (fun j : ℕ => if j < k then f j else 0) i) = _
  rw [← Finset.sum_range (n := N) (fun j : ℕ => if j < k then f j else 0),
    ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- The polynomial endpoint in the same natural-prefix notation used by
the quantitative noisy path estimate. -/
theorem published_switched_height_eq_nat_integral {σ : Type*} [Fintype σ]
    (N : ℕ) (T : σ → MvPolynomial σ ℝ) (c : σ → ℝ)
    (v : ℕ → σ → ℝ) (δ : ℕ → ℝ) :
    MvPolynomial.eval (fun k : Fin N => δ k)
      (Submission.Lib.K4CubicTests.switchedEndpointHeight T c (fun k : Fin N => v k)) =
      ∑ k ∈ Finset.range N, ∫ s in (0:ℝ)..δ k,
        ∑ a, v k a * MvPolynomial.eval (pathBasePrefix c δ v k + s • v k) (T a) := by
  classical
  let I (k : ℕ) := ∫ s in (0:ℝ)..δ k,
    ∑ a, v k a * MvPolynomial.eval (pathBasePrefix c δ v k + s • v k) (T a)
  calc
    _ = ∑ k : Fin N, I k := by
      rw [published_height_eq_strictPrefix_integral]
      apply Finset.sum_congr rfl
      intro k _
      apply intervalIntegral.integral_congr
      intro s _
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      apply congrArg (fun x => MvPolynomial.eval x (T a))
      funext b
      change (c b + ∑ l : Fin N,
        if (l : ℕ) < (k : ℕ) then v (l : ℕ) b * δ l else 0) + s * v (k : ℕ) b = _
      rw [fin_sum_lt_eq_range N (k : ℕ) (Nat.le_of_lt k.isLt)
        (fun j : ℕ => v j b * δ j)]
      simp only [pathBasePrefix, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        mul_comm]
    _ = _ := (Finset.sum_range (n := N) I).symm


end Submission.Lib.K4PolynomialNorming
