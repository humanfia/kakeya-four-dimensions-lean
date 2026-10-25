import Submission.Obl.k4_parametric_tarski_query.CauchyIndex

/-!
Adapted from the same LOT tree, obligation o050, session x0159,
commit f99d6af7e8420c51ce38439aeede86aba6326413, file `Submission/Obl/k4_sign_projection/TarskiQuery.lean`.
The declarations and imports have been moved to this obligation's namespace.
-/

namespace Submission.Obl.k4_parametric_tarski_query

open Polynomial
open scoped BigOperators

private theorem zsign_sq {x : ℝ} (hx : x ≠ 0) : zsign x ^ 2 = 1 := by
  rcases hx.lt_or_gt with h | h
  · rw [zsign_of_neg h]
    norm_num
  · rw [zsign_of_pos h]
    norm_num

theorem rightSign_sq {p : Polynomial ℝ} (hp : p ≠ 0) (a : ℝ) :
    rightSign p a ^ 2 = 1 :=
  zsign_sq (rootResidual_eval_ne_zero hp a)

theorem leftSign_sq {p : Polynomial ℝ} (hp : p ≠ 0) (a : ℝ) :
    leftSign p a ^ 2 = 1 := by
  rw [leftSign, mul_pow, rightSign_sq hp a, mul_one, ← pow_mul, mul_comm, pow_mul]
  norm_num

/-- At a root the derivative preserves the right sign and reverses the left sign. -/
theorem derivative_local_signs {p : Polynomial ℝ} (hp : p ≠ 0) {a : ℝ}
    (ha : p.IsRoot a) :
    p.derivative.rootMultiplicity a + 1 = p.rootMultiplicity a ∧
      rightSign p.derivative a = rightSign p a ∧
      leftSign p.derivative a = -leftSign p a := by
  let m := p.rootMultiplicity a
  let r := rootResidual p a
  have hm : 0 < m := (rootMultiplicity_pos hp).mpr ha
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hpow : (X - C a) ^ m = (X - C a) ^ (m - 1) * (X - C a) := by
    rw [← pow_succ, hm']
  let v := C (m : ℝ) * r + (X - C a) * r.derivative
  have hpFac : p = (X - C a) ^ m * r :=
    (pow_mul_divByMonic_rootMultiplicity_eq p a).symm
  have hder : p.derivative = (X - C a) ^ (m - 1) * v := by
    calc
      p.derivative = ((X - C a) ^ m * r).derivative := congrArg Polynomial.derivative hpFac
      _ = C (m : ℝ) * (X - C a) ^ (m - 1) * r + (X - C a) ^ m * r.derivative := by
        rw [derivative_mul, derivative_X_sub_C_pow]
      _ = _ := by rw [hpow]; dsimp only [v]; ring
  have hval : v.eval a = (m : ℝ) * r.eval a := by
    simp [v]
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hrval : r.eval a ≠ 0 := rootResidual_eval_ne_zero hp a
  have hv : v.eval a ≠ 0 := by rw [hval]; exact mul_ne_zero hmreal.ne' hrval
  have hr : rightSign p.derivative a = rightSign p a := by
    rw [rightSign_of_factor hder hv, hval, zsign_mul, zsign_of_pos hmreal, one_mul]
    rfl
  have hneg : (-1 : ℤ) ^ (m - 1) = -((-1 : ℤ) ^ m) := by
    nth_rw 2 [← hm']
    rw [pow_succ]
    ring
  refine ⟨?_, hr, ?_⟩
  · rw [rootMultiplicity_of_factor hder hv]
    exact hm'
  · rw [leftSign_of_factor hder hv, hval, zsign_mul, zsign_of_pos hmreal, one_mul,
      hneg]
    simp only [leftSign, rightSign, m, r]
    ring

/-- Local logarithmic derivatives count a distinct root with the requested sign. -/
theorem cauchyAt_log_derivative {p : Polynomial ℝ} (hp : p ≠ 0) (g : Polynomial ℝ)
    {a : ℝ} (ha : p.IsRoot a) : cauchyAt (p.derivative * g) p a = 2 * zsign (g.eval a) := by
  classical
  obtain ⟨hm, hr, hl⟩ := derivative_local_signs hp ha
  by_cases hg0 : p.derivative * g = 0
  · have hg : g = 0 := by
      rcases mul_eq_zero.mp hg0 with hder | hg
      · have hright := rightSign_ne_zero hp a
        rw [← hr, hder, rightSign_zero] at hright
        exact (hright rfl).elim
      · exact hg
    simp [hg]
  have hg : g ≠ 0 := right_ne_zero_of_mul hg0
  have hmul := rootMultiplicity_mul (x := a) hg0
  by_cases hga : g.eval a = 0
  · have hgm : 0 < g.rootMultiplicity a := (rootMultiplicity_pos hg).mpr hga
    have hge : p.rootMultiplicity a ≤ (p.derivative * g).rootMultiplicity a := by omega
    simp [cauchyAt, not_lt_of_ge hge, hga]
  · have hgm : g.rootMultiplicity a = 0 := rootMultiplicity_eq_zero hga
    have hlt : (p.derivative * g).rootMultiplicity a < p.rootMultiplicity a := by omega
    rw [cauchyAt, ite_eq_left hlt, rightSign_mul, rightSign_mul, leftSign_mul, leftSign_mul,
      hr, hl, rightSign_eq_zsign hga, leftSign_eq_zsign hga]
    calc
      _ = (rightSign p a ^ 2 + leftSign p a ^ 2) * zsign (g.eval a) := by ring
      _ = 2 * zsign (g.eval a) := by rw [rightSign_sq hp a, leftSign_sq hp a]; ring

/-- The doubled Cauchy index of `p' g / p` is twice the Tarski query. -/
theorem cauchyIndex_log_derivative (p g : Polynomial ℝ) :
    cauchyIndex (p.derivative * g) p = 2 * ∑ a ∈ p.roots.toFinset, zsign (g.eval a) := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  rw [cauchyIndex, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  exact cauchyAt_log_derivative hp g ((mem_roots hp).mp (Multiset.mem_toFinset.mp ha))

end Submission.Obl.k4_parametric_tarski_query
