import Mathlib

/-!
The profile minimizations used in the relative-profile and nested-system
arguments of the supplied paper, Proposition `prop:critical-path`.
-/

namespace Submission.Obl.k4_scalar_critical_path_terminal

open Set

/-- The increment hypotheses in the exact scalar problem give continuity on
its depth interval, with no assumption on the absolute value at depth zero. -/
theorem profile_lipschitzOn {f : ℝ → ℝ} {L : ℝ}
    (hf : ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ L →
      0 ≤ f s - f r ∧ f s - f r ≤ s - r) :
    LipschitzOnWith 1 f (Icc 0 L) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rcases le_total x y with hxy | hyx
  · obtain ⟨h₀, h₁⟩ := hf x y hx.1 hxy hy.2
    rw [abs_of_nonpos (by linarith : f x - f y ≤ 0),
      abs_of_nonpos (by linarith : x - y ≤ 0)]
    linarith
  · obtain ⟨h₀, h₁⟩ := hf y x hy.1 hyx hx.2
    rw [abs_of_nonneg h₀, abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact h₁

/-- Minimizing a tilted profile supplies an endpoint slope cap on all
preceding depths in the interval. -/
theorem exists_tilted_profile_minimum {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (d : ℝ) :
    ∃ r ∈ Icc a b, (∀ x ∈ Icc a b, f r - d * r ≤ f x - d * x) ∧
      ∀ x ∈ Icc a r, f r - f x ≤ d * (r - x) := by
  obtain ⟨r, hr, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hab) (hf.sub (continuous_const.mul continuous_id).continuousOn)
  refine ⟨r, hr, hmin, ?_⟩
  intro x hx
  have h := hmin ⟨hx.1, hx.2.trans hr.2⟩
  dsimp at h
  linarith

/-- A strict lower secant forces the tilted minimizer away from the left
endpoint. The displayed gap is useful before taking a sequence limit. -/
theorem tilted_profile_minimum_gap {f : ℝ → ℝ} {a b r d δ : ℝ}
    (hgap : δ ≤ d * (b - a) - (f b - f a))
    (hmono : f a ≤ f r)
    (hmin : f r - d * r ≤ f b - d * b) :
    δ ≤ d * (r - a) := by
  linarith

/-- A slope cap on a terminal subinterval combines with the ambient
one-Lipschitz bound to give a strict global terminal cap. -/
theorem global_terminal_cap_of_local {f : ℝ → ℝ} {a r d : ℝ}
    (ha : 0 ≤ a) (har : a < r) (hd₀ : 0 ≤ d) (hd₁ : d < 1)
    (hf : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ r →
      0 ≤ f y - f x ∧ f y - f x ≤ y - x)
    (hlocal : ∀ x ∈ Icc a r, f r - f x ≤ d * (r - x)) :
    ∃ D : ℝ, 0 ≤ D ∧ D < 1 ∧
      ∀ x ∈ Icc 0 r, f r - f x ≤ D * (r - x) := by
  have hr : 0 < r := lt_of_le_of_lt ha har
  let D := 1 - (1 - d) * (r - a) / r
  have hDr : (1 - D) * r = (1 - d) * (r - a) := by
    dsimp [D]
    field_simp
    ring
  have hD : d ≤ D := by nlinarith
  have hD₁ : D < 1 := by nlinarith
  refine ⟨D, hd₀.trans hD, hD₁, ?_⟩
  intro x hx
  by_cases hax : a ≤ x
  · exact (hlocal x ⟨hax, hx.2⟩).trans
      (mul_le_mul_of_nonneg_right hD (sub_nonneg.mpr hx.2))
  · have hxa : x ≤ a := le_of_not_ge hax
    have hfa := (hf x a hx.1 hxa har.le).2
    have hfr := hlocal a ⟨le_rfl, har.le⟩
    have hnonneg : 0 ≤ (1 - D) * x :=
      mul_nonneg (sub_nonneg.mpr hD₁.le) hx.1
    nlinarith

/-- A small uniform error from a line forces the minimum of the slightly
more steeply tilted profile to be close to the target right endpoint. -/
theorem tilted_profile_minimum_near_endpoint {f : ℝ → ℝ} {r t d ε δ : ℝ}
    (hε : 0 < ε)
    (hleft : -δ ≤ f t - f 0 - d * t)
    (hright : f r - f 0 - d * r ≤ δ)
    (hmin : f t - (d + ε) * t ≤ f r - (d + ε) * r) :
    r - t ≤ 2 * δ / ε := by
  apply (le_div_iff₀ hε).2
  nlinarith

end Submission.Obl.k4_scalar_critical_path_terminal
