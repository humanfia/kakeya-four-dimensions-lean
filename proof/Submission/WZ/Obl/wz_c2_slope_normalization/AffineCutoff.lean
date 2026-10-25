-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_c2_slope_normalization.AffineCutoff.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_c2_slope_normalization

open Set Filter
open scoped Topology

noncomputable section

private theorem transition_deriv_zero {x : ℝ} (hx : x < 0 ∨ 1 < x) :
    deriv Real.smoothTransition x = 0 ∧ deriv (deriv Real.smoothTransition) x = 0 := by
  rcases hx with hx | hx
  · have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [gt_mem_nhds hx] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    exact ⟨by simpa using he.deriv_eq, by simpa using he.deriv.deriv_eq⟩
  · have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [lt_mem_nhds hx] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    exact ⟨by simpa using he.deriv_eq, by simpa using he.deriv.deriv_eq⟩

/-- A universal bound for the first two derivatives of the fixed smooth transition. -/
theorem exists_transition_deriv_bound : ∃ K : ℝ, 1 ≤ K ∧
    ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ K ∧
      |deriv (deriv Real.smoothTransition) x| ≤ K := by
  have hc : ContDiff ℝ (3 : ℕ) Real.smoothTransition := Real.smoothTransition.contDiff
  have hc' : ContDiff ℝ (2 : ℕ) (deriv Real.smoothTransition) := hc.deriv'
  obtain ⟨K₁, hK₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.continuous_deriv (by norm_num)).continuousOn (s := Icc (0 : ℝ) 1)
  obtain ⟨K₂, hK₂⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc'.continuous_deriv (by norm_num)).continuousOn (s := Icc (0 : ℝ) 1)
  refine ⟨max 1 (max K₁ K₂), le_max_left _ _, ?_⟩
  intro x
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · have h₁ : |deriv Real.smoothTransition x| ≤ K₁ := by
      simpa only [Real.norm_eq_abs] using hK₁ x hx
    have h₂ : |deriv (deriv Real.smoothTransition) x| ≤ K₂ := by
      simpa only [Real.norm_eq_abs] using hK₂ x hx
    exact ⟨h₁.trans ((le_max_left _ _).trans (le_max_right _ _)),
      h₂.trans ((le_max_right _ _).trans (le_max_right _ _))⟩
  · have hx' : x < 0 ∨ 1 < x := by simpa only [mem_Icc, not_and_or, not_le] using hx
    rw [(transition_deriv_zero hx').1, (transition_deriv_zero hx').2]
    constructor <;> simp only [abs_zero] <;> exact zero_le_one.trans (le_max_left _ _)

/-- A smooth cutoff equal to one on `[l,u]` and zero outside `[l-a,u+a]`. -/
def intervalCutoff (l u a x : ℝ) : ℝ :=
  Real.smoothTransition ((x - l + a) / a) * Real.smoothTransition ((u + a - x) / a)

def intervalCutoffD (l u a x : ℝ) : ℝ :=
  (deriv Real.smoothTransition ((x - l + a) / a) *
      Real.smoothTransition ((u + a - x) / a) -
    Real.smoothTransition ((x - l + a) / a) *
      deriv Real.smoothTransition ((u + a - x) / a)) / a

def intervalCutoffDD (l u a x : ℝ) : ℝ :=
  (deriv (deriv Real.smoothTransition) ((x - l + a) / a) *
      Real.smoothTransition ((u + a - x) / a) -
    2 * deriv Real.smoothTransition ((x - l + a) / a) *
      deriv Real.smoothTransition ((u + a - x) / a) +
    Real.smoothTransition ((x - l + a) / a) *
      deriv (deriv Real.smoothTransition) ((u + a - x) / a)) / a ^ 2

theorem intervalCutoff_contDiff (l u a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (intervalCutoff l u a) := by
  unfold intervalCutoff
  fun_prop

theorem intervalCutoff_mem_Icc (l u a x : ℝ) : intervalCutoff l u a x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · exact (mul_le_mul (Real.smoothTransition.le_one _)
      (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _) zero_le_one).trans_eq
        (one_mul _)

theorem intervalCutoff_eq_one {l u a x : ℝ} (ha : 0 < a) (hx : x ∈ Icc l u) :
    intervalCutoff l u a x = 1 := by
  have hleft : 1 ≤ (x - l + a) / a := (le_div_iff₀ ha).mpr (by linarith [hx.1])
  have hright : 1 ≤ (u + a - x) / a := (le_div_iff₀ ha).mpr (by linarith [hx.2])
  simp only [intervalCutoff, Real.smoothTransition.one_of_one_le hleft,
    Real.smoothTransition.one_of_one_le hright, mul_one]

theorem intervalCutoff_eq_zero {l u a x : ℝ} (ha : 0 < a)
    (hx : x ≤ l - a ∨ u + a ≤ x) : intervalCutoff l u a x = 0 := by
  rcases hx with hx | hx
  · have hleft : (x - l + a) / a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le
    simp only [intervalCutoff, Real.smoothTransition.zero_of_nonpos hleft, zero_mul]
  · have hright : (u + a - x) / a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le
    simp only [intervalCutoff, Real.smoothTransition.zero_of_nonpos hright, mul_zero]

private theorem transition_left_hasDerivAt (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (l a x : ℝ) :
    HasDerivAt (fun x => f ((x - l + a) / a)) (deriv f ((x - l + a) / a) / a) x := by
  simpa only [Function.comp_def, id_eq, div_eq_mul_inv, mul_one, one_mul] using
    (hf ((x - l + a) / a)).hasDerivAt.comp x
      (((hasDerivAt_id x).sub_const l).add_const a |>.div_const a)

private theorem transition_right_hasDerivAt (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (u a x : ℝ) :
    HasDerivAt (fun x => f ((u + a - x) / a)) (-deriv f ((u + a - x) / a) / a) x := by
  simpa only [Function.comp_def, Pi.sub_apply, id_eq, div_eq_mul_inv, zero_sub,
    mul_neg, mul_one, one_mul, neg_mul, mul_assoc] using
    (hf ((u + a - x) / a)).hasDerivAt.comp x
      (((hasDerivAt_const x (u + a)).sub (hasDerivAt_id x)).div_const a)

theorem intervalCutoff_hasDerivAt (l u a x : ℝ) :
    HasDerivAt (intervalCutoff l u a) (intervalCutoffD l u a x) x := by
  have hd : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
  unfold intervalCutoff intervalCutoffD
  convert (transition_left_hasDerivAt _ hd l a x).mul
    (transition_right_hasDerivAt _ hd u a x) using 1
  ring

theorem intervalCutoffD_hasDerivAt (l u a x : ℝ) :
    HasDerivAt (intervalCutoffD l u a) (intervalCutoffDD l u a x) x := by
  have hc : ContDiff ℝ (2 : ℕ) Real.smoothTransition := Real.smoothTransition.contDiff
  have hd : Differentiable ℝ Real.smoothTransition := hc.differentiable (by norm_num)
  have hd' : Differentiable ℝ (deriv Real.smoothTransition) := hc.differentiable_deriv_two
  unfold intervalCutoffD intervalCutoffDD
  convert (((transition_left_hasDerivAt _ hd' l a x).mul
    (transition_right_hasDerivAt _ hd u a x)).sub
      ((transition_left_hasDerivAt _ hd l a x).mul
        (transition_right_hasDerivAt _ hd' u a x))).div_const a using 1
  ring

theorem intervalCutoffD_bound {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x, |deriv Real.smoothTransition x| ≤ K)
    {a : ℝ} (ha : 0 < a) (l u x : ℝ) : |intervalCutoffD l u a x| ≤ 2 * K / a := by
  have hleft := Real.smoothTransition.nonneg ((x - l + a) / a)
  have hright := Real.smoothTransition.nonneg ((u + a - x) / a)
  unfold intervalCutoffD
  rw [abs_div, abs_of_pos ha]
  apply div_le_div_of_nonneg_right _ ha.le
  calc _ ≤ |deriv Real.smoothTransition ((x - l + a) / a) *
        Real.smoothTransition ((u + a - x) / a)| +
        |Real.smoothTransition ((x - l + a) / a) *
        deriv Real.smoothTransition ((u + a - x) / a)| := abs_sub _ _
    _ ≤ K * 1 + 1 * K := by
      simp only [abs_mul, abs_of_nonneg hleft, abs_of_nonneg hright]
      exact add_le_add
        (mul_le_mul (hbound _) (Real.smoothTransition.le_one _) hright hK)
        (mul_le_mul (Real.smoothTransition.le_one _) (hbound _) (abs_nonneg _) zero_le_one)
    _ = 2 * K := by ring

theorem intervalCutoffDD_bound {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x, |deriv Real.smoothTransition x| ≤ K ∧
      |deriv (deriv Real.smoothTransition) x| ≤ K)
    {a : ℝ} (_ha : 0 < a) (l u x : ℝ) :
    |intervalCutoffDD l u a x| ≤ (2 * K + 2 * K ^ 2) / a ^ 2 := by
  unfold intervalCutoffDD
  rw [abs_div, abs_of_nonneg (sq_nonneg a)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg a)
  calc _ ≤
      (|deriv (deriv Real.smoothTransition) ((x - l + a) / a) *
          Real.smoothTransition ((u + a - x) / a)| +
        |2 * deriv Real.smoothTransition ((x - l + a) / a) *
          deriv Real.smoothTransition ((u + a - x) / a)|) +
      |Real.smoothTransition ((x - l + a) / a) *
          deriv (deriv Real.smoothTransition) ((u + a - x) / a)| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ (K * 1 + 2 * K * K) + 1 * K := by
      simp only [abs_mul, abs_of_nonneg (Real.smoothTransition.nonneg _),
        abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul (hbound _).2 (Real.smoothTransition.le_one _)
            (Real.smoothTransition.nonneg _) hK
        · exact mul_le_mul (mul_le_mul_of_nonneg_left (hbound _).1 (by norm_num))
            (hbound _).1 (abs_nonneg _) (mul_nonneg (by norm_num) hK)
      · exact mul_le_mul (Real.smoothTransition.le_one _) (hbound _).2
          (abs_nonneg _) zero_le_one
    _ = 2 * K + 2 * K ^ 2 := by ring

/-- Extend an affine function smoothly with a padding interval of width `a`. -/
def affineExtension (l u a y s x : ℝ) : ℝ :=
  intervalCutoff l u a x * (y + s * (x - l))

def affineExtensionD (l u a y s x : ℝ) : ℝ :=
  intervalCutoffD l u a x * (y + s * (x - l)) + intervalCutoff l u a x * s

def affineExtensionDD (l u a y s x : ℝ) : ℝ :=
  intervalCutoffDD l u a x * (y + s * (x - l)) + 2 * intervalCutoffD l u a x * s

theorem affineExtension_contDiff (l u a y s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (affineExtension l u a y s) := by
  exact (intervalCutoff_contDiff l u a).mul (by fun_prop)

theorem affineExtension_eq_affine {l u a y s x : ℝ} (ha : 0 < a) (hx : x ∈ Icc l u) :
    affineExtension l u a y s x = y + s * (x - l) := by
  simp only [affineExtension, intervalCutoff_eq_one ha hx, one_mul]

theorem affineExtension_eq_zero {l u a y s x : ℝ} (ha : 0 < a)
    (hx : x ≤ l - a ∨ u + a ≤ x) : affineExtension l u a y s x = 0 := by
  simp only [affineExtension, intervalCutoff_eq_zero ha hx, zero_mul]

private theorem affine_hasDerivAt (l y s x : ℝ) :
    HasDerivAt (fun x => y + s * (x - l)) s x := by
  simpa only [id_eq, mul_one] using (((hasDerivAt_id x).sub_const l).const_mul s).const_add y

theorem affineExtension_hasDerivAt (l u a y s x : ℝ) :
    HasDerivAt (affineExtension l u a y s) (affineExtensionD l u a y s x) x := by
  exact (intervalCutoff_hasDerivAt l u a x).mul (affine_hasDerivAt l y s x)

theorem affineExtensionD_hasDerivAt (l u a y s x : ℝ) :
    HasDerivAt (affineExtensionD l u a y s) (affineExtensionDD l u a y s x) x := by
  unfold affineExtensionD affineExtensionDD
  convert ((intervalCutoffD_hasDerivAt l u a x).mul (affine_hasDerivAt l y s x)).add
    ((intervalCutoff_hasDerivAt l u a x).mul_const s) using 1
  ring

theorem deriv_affineExtension (l u a y s : ℝ) :
    deriv (affineExtension l u a y s) = affineExtensionD l u a y s := by
  funext x
  exact (affineExtension_hasDerivAt l u a y s x).deriv

theorem deriv_deriv_affineExtension (l u a y s : ℝ) :
    deriv (deriv (affineExtension l u a y s)) = affineExtensionDD l u a y s := by
  rw [deriv_affineExtension]
  funext x
  exact (affineExtensionD_hasDerivAt l u a y s x).deriv

private theorem affine_bound {l u a y s x : ℝ} (hx : x ∈ Icc (l - a) (u + a)) :
    |y + s * (x - l)| ≤ (|y| + |y + s * (u - l)|) + |s| * a := by
  have hy₀ := neg_abs_le y
  have hy₁ := le_abs_self y
  have hu₀ := neg_abs_le (y + s * (u - l))
  have hu₁ := le_abs_self (y + s * (u - l))
  have ha₀ := abs_nonneg y
  have ha₁ := abs_nonneg (y + s * (u - l))
  by_cases hs : 0 ≤ s
  · rw [abs_of_nonneg hs, abs_le]
    constructor <;> nlinarith [mul_nonneg hs (sub_nonneg.mpr hx.1),
      mul_nonneg hs (sub_nonneg.mpr hx.2)]
  · have hs' : 0 ≤ -s := by linarith
    rw [abs_of_nonpos (le_of_not_ge hs), abs_le]
    constructor <;> nlinarith [mul_nonneg hs' (sub_nonneg.mpr hx.1),
      mul_nonneg hs' (sub_nonneg.mpr hx.2)]

private theorem affineExtension_deriv_zero {l u a y s x : ℝ} (ha : 0 < a)
    (hx : x < l - a ∨ u + a < x) :
    deriv (affineExtension l u a y s) x = 0 ∧
      deriv (deriv (affineExtension l u a y s)) x = 0 := by
  have he : affineExtension l u a y s =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    rcases hx with hx | hx
    · filter_upwards [gt_mem_nhds hx] with z hz
      exact affineExtension_eq_zero ha (Or.inl hz.le)
    · filter_upwards [lt_mem_nhds hx] with z hz
      exact affineExtension_eq_zero ha (Or.inr hz.le)
  exact ⟨by simpa using he.deriv_eq, by simpa using he.deriv.deriv_eq⟩

theorem affineExtension_zero_of_not_mem {l u a y s x : ℝ} (ha : 0 < a)
    (hx : x ∉ Icc (l - a) (u + a)) : affineExtension l u a y s x = 0 := by
  have hx' : x < l - a ∨ u + a < x := by
    simpa only [mem_Icc, not_and_or, not_le] using hx
  exact affineExtension_eq_zero ha (hx'.imp le_of_lt le_of_lt)

theorem affineExtension_derivs_zero_of_not_mem {l u a y s x : ℝ} (ha : 0 < a)
    (hx : x ∉ Icc (l - a) (u + a)) :
    deriv (affineExtension l u a y s) x = 0 ∧
      deriv (deriv (affineExtension l u a y s)) x = 0 := by
  apply affineExtension_deriv_zero ha
  simpa only [mem_Icc, not_and_or, not_le] using hx

theorem affineExtension_deriv_bound {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x, |deriv Real.smoothTransition x| ≤ K)
    {a : ℝ} (ha : 0 < a) (l u y s x : ℝ) :
    |deriv (affineExtension l u a y s) x| ≤
      (2 * K + 1) * ((|y| + |y + s * (u - l)|) / a + |s|) := by
  by_cases hx : x ∈ Icc (l - a) (u + a)
  · rw [deriv_affineExtension]
    have hp := intervalCutoff_mem_Icc l u a x
    have he := affine_bound hx (y := y) (s := s)
    calc |affineExtensionD l u a y s x|
        ≤ |intervalCutoffD l u a x| * |y + s * (x - l)| +
          |intervalCutoff l u a x| * |s| := by
            simpa only [affineExtensionD, abs_mul] using abs_add_le
              (intervalCutoffD l u a x * (y + s * (x - l))) (intervalCutoff l u a x * s)
      _ ≤ (2 * K / a) * ((|y| + |y + s * (u - l)|) + |s| * a) + 1 * |s| := by
        apply add_le_add
        · exact mul_le_mul (intervalCutoffD_bound hK hbound ha l u x) he (abs_nonneg _)
            (by positivity)
        · exact mul_le_mul_of_nonneg_right (by simpa only [abs_of_nonneg hp.1] using hp.2)
            (abs_nonneg _)
      _ ≤ (2 * K + 1) * ((|y| + |y + s * (u - l)|) / a + |s|) := by
        field_simp
        nlinarith [abs_nonneg y, abs_nonneg (y + s * (u - l))]
  · have hx' : x < l - a ∨ u + a < x := by
      simpa only [mem_Icc, not_and_or, not_le] using hx
    rw [(affineExtension_deriv_zero ha hx').1, abs_zero]
    positivity

theorem affineExtension_deriv_deriv_bound {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x, |deriv Real.smoothTransition x| ≤ K ∧
      |deriv (deriv Real.smoothTransition) x| ≤ K)
    {a : ℝ} (ha : 0 < a) (l u y s x : ℝ) :
    |deriv (deriv (affineExtension l u a y s)) x| ≤
      (6 * K + 2 * K ^ 2) * ((|y| + |y + s * (u - l)|) / a ^ 2 + |s| / a) := by
  by_cases hx : x ∈ Icc (l - a) (u + a)
  · rw [deriv_deriv_affineExtension]
    have he := affine_bound hx (y := y) (s := s)
    calc |affineExtensionDD l u a y s x|
        ≤ |intervalCutoffDD l u a x| * |y + s * (x - l)| +
          2 * |intervalCutoffD l u a x| * |s| := by
            simpa only [affineExtensionDD, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
              using abs_add_le (intervalCutoffDD l u a x * (y + s * (x - l)))
                (2 * intervalCutoffD l u a x * s)
      _ ≤ ((2 * K + 2 * K ^ 2) / a ^ 2) *
          ((|y| + |y + s * (u - l)|) + |s| * a) + 2 * (2 * K / a) * |s| := by
        apply add_le_add
        · exact mul_le_mul (intervalCutoffDD_bound hK hbound ha l u x) he (abs_nonneg _)
            (by positivity)
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (intervalCutoffD_bound hK (fun x => (hbound x).1) ha l u x) (by norm_num))
            (abs_nonneg _)
      _ ≤ (6 * K + 2 * K ^ 2) *
          ((|y| + |y + s * (u - l)|) / a ^ 2 + |s| / a) := by
        have hnonneg : 0 ≤ K * (|y| + |y + s * (u - l)|) := by positivity
        field_simp
        nlinarith
  · have hx' : x < l - a ∨ u + a < x := by
      simpa only [mem_Icc, not_and_or, not_le] using hx
    rw [(affineExtension_deriv_zero ha hx').2, abs_zero]
    positivity

/-- The smooth affine extension used in the multiscale construction: the constants are
independent of the interval length, its location, the affine data, and the padding width. -/
theorem exists_smooth_affine_extension : ∃ C : ℝ, 0 < C ∧
    ∀ l u a y s : ℝ, l ≤ u → 0 < a → ∃ G : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) G ∧
      (∀ x ∈ Icc l u, G x = y + s * (x - l)) ∧
      (∀ x, x ≤ l - a ∨ u + a ≤ x → G x = 0) ∧
      (∀ x, |deriv G x| ≤ C * ((|y| + |y + s * (u - l)|) / a + |s|)) ∧
      (∀ x, |deriv (deriv G) x| ≤
        C * ((|y| + |y + s * (u - l)|) / a ^ 2 + |s| / a)) := by
  obtain ⟨K, hK, hbound⟩ := exists_transition_deriv_bound
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  refine ⟨8 * (K + 1) ^ 2, by positivity, ?_⟩
  intro l u a y s _ ha
  refine ⟨affineExtension l u a y s, affineExtension_contDiff l u a y s,
    (fun x hx => affineExtension_eq_affine ha hx),
    (fun x hx => affineExtension_eq_zero ha hx), ?_, ?_⟩
  · intro x
    exact (affineExtension_deriv_bound hK0 (fun x => (hbound x).1) ha l u y s x).trans
      (mul_le_mul_of_nonneg_right (by nlinarith) (by positivity))
  · intro x
    exact (affineExtension_deriv_deriv_bound hK0 hbound ha l u y s x).trans
      (mul_le_mul_of_nonneg_right (by nlinarith) (by positivity))

end

end WangZahlLot.Obl.wz_c2_slope_normalization
