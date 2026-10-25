import Mathlib

namespace Submission.Obl.k4_sign_projection

open Polynomial Filter
open scoped Topology

/-- Signs as integers, for sums of local variations. -/
noncomputable def zsign (x : ℝ) : ℤ := (SignType.sign x : ℤ)

@[simp] theorem zsign_zero : zsign 0 = 0 := by simp [zsign]
@[simp] theorem zsign_one : zsign 1 = 1 := by simp [zsign]
@[simp] theorem zsign_mul (x y : ℝ) : zsign (x * y) = zsign x * zsign y := by
  simp [zsign, sign_mul]
@[simp] theorem zsign_pow (x : ℝ) (n : ℕ) : zsign (x ^ n) = zsign x ^ n := by
  simp [zsign, sign_pow]
@[simp] theorem zsign_neg (x : ℝ) : zsign (-x) = -zsign x := by
  simp [zsign, Left.sign_neg]

theorem zsign_eq_zero_iff {x : ℝ} : zsign x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply sign_eq_zero_iff.mp
    cases hs : SignType.sign x <;> simp_all [zsign]
  · rintro rfl
    exact zsign_zero

theorem zsign_of_pos {x : ℝ} (hx : 0 < x) : zsign x = 1 := by
  simp [zsign, sign_pos hx]

theorem zsign_of_neg {x : ℝ} (hx : x < 0) : zsign x = -1 := by
  simp [zsign, sign_neg hx]

/-- The polynomial after removing the whole power of its root at `a`. -/
noncomputable def rootResidual (p : Polynomial ℝ) (a : ℝ) : Polynomial ℝ :=
  p /ₘ (X - C a) ^ p.rootMultiplicity a

/-- The sign immediately to the right of `a`. -/
noncomputable def rightSign (p : Polynomial ℝ) (a : ℝ) : ℤ :=
  zsign ((rootResidual p a).eval a)

/-- The sign immediately to the left of `a`. -/
noncomputable def leftSign (p : Polynomial ℝ) (a : ℝ) : ℤ :=
  (-1) ^ p.rootMultiplicity a * rightSign p a

@[simp] theorem rootResidual_zero (a : ℝ) : rootResidual 0 a = 0 := by
  simp [rootResidual]
@[simp] theorem rightSign_zero (a : ℝ) : rightSign 0 a = 0 := by
  simp [rightSign]
@[simp] theorem leftSign_zero (a : ℝ) : leftSign 0 a = 0 := by
  simp [leftSign]

theorem rootResidual_eval_ne_zero {p : Polynomial ℝ} (hp : p ≠ 0) (a : ℝ) :
    (rootResidual p a).eval a ≠ 0 :=
  eval_divByMonic_pow_rootMultiplicity_ne_zero a hp

theorem rightSign_ne_zero {p : Polynomial ℝ} (hp : p ≠ 0) (a : ℝ) :
    rightSign p a ≠ 0 :=
  fun h => rootResidual_eval_ne_zero hp a (zsign_eq_zero_iff.mp h)

theorem leftSign_ne_zero {p : Polynomial ℝ} (hp : p ≠ 0) (a : ℝ) :
    leftSign p a ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (by norm_num)) (rightSign_ne_zero hp a)

theorem eval_eq_pow_mul_residual (p : Polynomial ℝ) (a x : ℝ) :
    p.eval x = (x - a) ^ p.rootMultiplicity a * (rootResidual p a).eval x := by
  simpa only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, rootResidual] using
    congrArg (fun q : Polynomial ℝ => q.eval x)
      (pow_mul_divByMonic_rootMultiplicity_eq p a).symm

theorem rightSign_eq_zsign {p : Polynomial ℝ} {a : ℝ} (ha : p.eval a ≠ 0) :
    rightSign p a = zsign (p.eval a) := by
  have hm : p.rootMultiplicity a = 0 := rootMultiplicity_eq_zero ha
  simp [rightSign, rootResidual, hm]

theorem leftSign_eq_zsign {p : Polynomial ℝ} {a : ℝ} (ha : p.eval a ≠ 0) :
    leftSign p a = zsign (p.eval a) := by
  simp [leftSign, rootMultiplicity_eq_zero ha, rightSign_eq_zsign ha]

/-- The sign of a continuous nonzero polynomial is constant near a point. -/
theorem eventually_zsign_eval {p : Polynomial ℝ} {a : ℝ} (ha : p.eval a ≠ 0) :
    ∀ᶠ x in 𝓝 a, zsign (p.eval x) = zsign (p.eval a) := by
  have h : ContinuousAt (fun x : ℝ => SignType.sign (p.eval x)) a :=
    (continuousAt_sign_of_ne_zero ha).comp (f := fun x : ℝ => p.eval x)
      p.continuous.continuousAt
  change Tendsto (fun x : ℝ => SignType.sign (p.eval x)) (𝓝 a)
    (𝓝 (SignType.sign (p.eval a))) at h
  rw [nhds_discrete SignType, tendsto_pure] at h
  exact h.mono fun _ hx => congrArg (fun s : SignType => (s : ℤ)) hx

/-- Actual polynomial signs agree with `rightSign` on a right neighborhood. -/
theorem eventually_eval_rightSign (p : Polynomial ℝ) (a : ℝ) :
    ∀ᶠ x in 𝓝[>] a, zsign (p.eval x) = rightSign p a := by
  by_cases hp : p = 0
  · simp [hp]
  have h := eventually_zsign_eval (rootResidual_eval_ne_zero hp a)
  filter_upwards [h.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxa
  rw [eval_eq_pow_mul_residual p a x, zsign_mul, zsign_pow,
    zsign_of_pos (sub_pos.mpr hxa), one_pow, one_mul, hx]
  rfl

/-- Actual polynomial signs agree with `leftSign` on a left neighborhood. -/
theorem eventually_eval_leftSign (p : Polynomial ℝ) (a : ℝ) :
    ∀ᶠ x in 𝓝[<] a, zsign (p.eval x) = leftSign p a := by
  by_cases hp : p = 0
  · simp [hp]
  have h := eventually_zsign_eval (rootResidual_eval_ne_zero hp a)
  filter_upwards [h.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxa
  rw [eval_eq_pow_mul_residual p a x, zsign_mul, zsign_pow,
    zsign_of_neg (sub_neg.mpr hxa), hx]
  rfl

theorem eventually_rightSign_right (p : Polynomial ℝ) (a : ℝ) :
    ∀ᶠ x in 𝓝[>] a, rightSign p x = rightSign p a := by
  by_cases hp : p = 0
  · simp [hp]
  filter_upwards [eventually_eval_rightSign p a] with x hx
  have hx0 : p.eval x ≠ 0 := fun hzero =>
    rightSign_ne_zero hp a (by rw [← hx, hzero, zsign_zero])
  rw [rightSign_eq_zsign hx0, hx]

theorem eventually_rightSign_left (p : Polynomial ℝ) (a : ℝ) :
    ∀ᶠ x in 𝓝[<] a, rightSign p x = leftSign p a := by
  by_cases hp : p = 0
  · simp [hp]
  filter_upwards [eventually_eval_leftSign p a] with x hx
  have hx0 : p.eval x ≠ 0 := fun hzero =>
    leftSign_ne_zero hp a (by rw [← hx, hzero, zsign_zero])
  rw [rightSign_eq_zsign hx0, hx]

theorem rightSign_mul (p q : Polynomial ℝ) (a : ℝ) :
    rightSign (p * q) a = rightSign p a * rightSign q a := by
  have h := (eventually_eval_rightSign (p * q) a).and
    ((eventually_eval_rightSign p a).and (eventually_eval_rightSign q a))
  obtain ⟨x, hx, hp, hq⟩ := h.exists
  rw [← hx, eval_mul, zsign_mul, hp, hq]

theorem leftSign_mul (p q : Polynomial ℝ) (a : ℝ) :
    leftSign (p * q) a = leftSign p a * leftSign q a := by
  have h := (eventually_eval_leftSign (p * q) a).and
    ((eventually_eval_leftSign p a).and (eventually_eval_leftSign q a))
  obtain ⟨x, hx, hp, hq⟩ := h.exists
  rw [← hx, eval_mul, zsign_mul, hp, hq]

theorem rightSign_neg (p : Polynomial ℝ) (a : ℝ) :
    rightSign (-p) a = -rightSign p a := by
  obtain ⟨x, hx, hp⟩ := ((eventually_eval_rightSign (-p) a).and
    (eventually_eval_rightSign p a)).exists
  rw [← hx, eval_neg, zsign_neg, hp]

theorem leftSign_neg (p : Polynomial ℝ) (a : ℝ) :
    leftSign (-p) a = -leftSign p a := by
  obtain ⟨x, hx, hp⟩ := ((eventually_eval_leftSign (-p) a).and
    (eventually_eval_leftSign p a)).exists
  rw [← hx, eval_neg, zsign_neg, hp]

/-- Polynomial signs at positive and negative infinity. -/
noncomputable def topSign (p : Polynomial ℝ) : ℤ := zsign p.leadingCoeff
noncomputable def botSign (p : Polynomial ℝ) : ℤ := topSign (p.comp (-X))

@[simp] theorem topSign_zero : topSign 0 = 0 := by simp [topSign]
@[simp] theorem botSign_zero : botSign 0 = 0 := by simp [botSign]

theorem eventually_eval_topSign (p : Polynomial ℝ) :
    ∀ᶠ x in atTop, zsign (p.eval x) = topSign p := by
  by_cases hp : p = 0
  · simp [hp]
  rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hp) with hn | hp
  · have h : ∀ᶠ x : ℝ in atTop, p.leadingCoeff * x ^ p.natDegree < 0 := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact mul_neg_of_neg_of_pos hn (pow_pos hx _)
    filter_upwards [p.isEquivalent_atTop_lead.eventually_neg h] with x hx
    simp [topSign, zsign_of_neg hx, zsign_of_neg hn]
  · have h : ∀ᶠ x : ℝ in atTop, 0 < p.leadingCoeff * x ^ p.natDegree := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact mul_pos hp (pow_pos hx _)
    filter_upwards [p.isEquivalent_atTop_lead.eventually_pos h] with x hx
    simp [topSign, zsign_of_pos hx, zsign_of_pos hp]

theorem eventually_eval_botSign (p : Polynomial ℝ) :
    ∀ᶠ x in atBot, zsign (p.eval x) = botSign p := by
  have h := tendsto_neg_atBot_atTop.eventually (eventually_eval_topSign (p.comp (-X)))
  simpa only [eval_comp, eval_neg, eval_X, neg_neg, botSign] using h

theorem botSign_eq (p : Polynomial ℝ) :
    botSign p = (-1) ^ p.natDegree * topSign p := by
  simp [botSign, topSign, comp_neg_X_leadingCoeff_eq, zsign_mul, zsign_pow,
    mul_comm]

end Submission.Obl.k4_sign_projection
