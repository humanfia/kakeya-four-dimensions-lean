import Submission.Obl.k4_sign_projection.PolySigns

namespace Submission.Obl.k4_sign_projection

open Polynomial Filter
open scoped Topology

@[simp] theorem rightSign_one (a : ℝ) : rightSign 1 a = 1 := by
  have ha : (1 : Polynomial ℝ).eval a ≠ 0 := by simp
  simpa using rightSign_eq_zsign ha

@[simp] theorem leftSign_one (a : ℝ) : leftSign 1 a = 1 := by
  have ha : (1 : Polynomial ℝ).eval a ≠ 0 := by simp
  simpa using leftSign_eq_zsign ha

theorem rightSign_pow (p : Polynomial ℝ) (n : ℕ) (a : ℝ) :
    rightSign (p ^ n) a = rightSign p a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, rightSign_mul, ih, pow_succ]

theorem leftSign_pow (p : Polynomial ℝ) (n : ℕ) (a : ℝ) :
    leftSign (p ^ n) a = leftSign p a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, leftSign_mul, ih, pow_succ]

@[simp] theorem rightSign_X_sub_C (a : ℝ) : rightSign (X - C a) a = 1 := by
  obtain ⟨x, hx, hxa⟩ := ((eventually_eval_rightSign (X - C a) a).and
    self_mem_nhdsWithin).exists
  simpa only [eval_sub, eval_X, eval_C, zsign_of_pos (sub_pos.mpr hxa)] using hx.symm

@[simp] theorem leftSign_X_sub_C (a : ℝ) : leftSign (X - C a) a = -1 := by
  obtain ⟨x, hx, hxa⟩ := ((eventually_eval_leftSign (X - C a) a).and
    self_mem_nhdsWithin).exists
  simpa only [eval_sub, eval_X, eval_C, zsign_of_neg (sub_neg.mpr hxa)] using hx.symm

theorem rootMultiplicity_of_factor {p q : Polynomial ℝ} {a : ℝ} {n : ℕ}
    (h : p = (X - C a) ^ n * q) (hq : q.eval a ≠ 0) : p.rootMultiplicity a = n := by
  have hq0 : q ≠ 0 := fun hzero => hq (by simp [hzero])
  rw [h, mul_comm, rootMultiplicity_mul_X_sub_C_pow hq0, rootMultiplicity_eq_zero hq,
    zero_add]

theorem rightSign_of_factor {p q : Polynomial ℝ} {a : ℝ} {n : ℕ}
    (h : p = (X - C a) ^ n * q) (hq : q.eval a ≠ 0) :
    rightSign p a = zsign (q.eval a) := by
  rw [h, rightSign_mul, rightSign_pow, rightSign_X_sub_C, one_pow, one_mul,
    rightSign_eq_zsign hq]

theorem leftSign_of_factor {p q : Polynomial ℝ} {a : ℝ} {n : ℕ}
    (h : p = (X - C a) ^ n * q) (hq : q.eval a ≠ 0) :
    leftSign p a = (-1) ^ n * zsign (q.eval a) := by
  rw [h, leftSign_mul, leftSign_pow, leftSign_X_sub_C, leftSign_eq_zsign hq]

/-- Adding a term with strictly larger vanishing order preserves the leading germ. -/
theorem local_signs_add_high {p v : Polynomial ℝ} (hp : p ≠ 0) (a : ℝ)
    (hv : (X - C a) ^ (p.rootMultiplicity a + 1) ∣ v) :
    (p + v).rootMultiplicity a = p.rootMultiplicity a ∧
      rightSign (p + v) a = rightSign p a ∧
      leftSign (p + v) a = leftSign p a := by
  obtain ⟨w, hw⟩ := hv
  let r := rootResidual p a
  have hfac : p + v = (X - C a) ^ p.rootMultiplicity a * (r + (X - C a) * w) := by
    calc
      p + v = (X - C a) ^ p.rootMultiplicity a * r +
          (X - C a) ^ (p.rootMultiplicity a + 1) * w := by
        exact congrArg₂ (· + ·) (pow_mul_divByMonic_rootMultiplicity_eq p a).symm hw
      _ = _ := by rw [pow_succ]; ring
  have hr : (r + (X - C a) * w).eval a ≠ 0 := by
    simpa only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul,
      add_zero] using rootResidual_eval_ne_zero hp a
  refine ⟨rootMultiplicity_of_factor hfac hr, ?_, ?_⟩
  · rw [rightSign_of_factor hfac hr]
    simp [r, rightSign]
  · rw [leftSign_of_factor hfac hr]
    simp [r, leftSign, rightSign]

theorem eventually_rightSign_top (p : Polynomial ℝ) :
    ∀ᶠ x in atTop, rightSign p x = topSign p := by
  by_cases hp : p = 0
  · simp [hp]
  filter_upwards [eventually_eval_topSign p, p.eventually_atTop_not_isRoot hp] with x hx hroot
  rw [rightSign_eq_zsign hroot, hx]

theorem eventually_rightSign_bot (p : Polynomial ℝ) :
    ∀ᶠ x in atBot, rightSign p x = botSign p := by
  by_cases hp : p = 0
  · simp [hp]
  filter_upwards [eventually_eval_botSign p, p.eventually_atBot_not_isRoot hp] with x hx hroot
  rw [rightSign_eq_zsign hroot, hx]

theorem topSign_mul (p q : Polynomial ℝ) : topSign (p * q) = topSign p * topSign q := by
  simp [topSign, leadingCoeff_mul]

theorem botSign_mul (p q : Polynomial ℝ) : botSign (p * q) = botSign p * botSign q := by
  simp [botSign, mul_comp, topSign_mul]

end Submission.Obl.k4_sign_projection
