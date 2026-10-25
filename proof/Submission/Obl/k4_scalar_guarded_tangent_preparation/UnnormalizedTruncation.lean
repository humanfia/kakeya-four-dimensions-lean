import Submission.Obl.k4_matching_palette_likelihood.Basic

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open Submission.Obl.k4_matching_palette_likelihood

noncomputable section

variable {α : Type*} [Fintype α]

/-- The original-law likelihood ratio has its original total mass in
the numerator; no reference law is renormalized after deletion. -/
def originalLikelihood (p : α → ℝ) (Y Z : α → ℕ) (x : α) : ℝ :=
  (colorMass p Y Z (Y x) (Z x) * ∑ i, p i) /
    (fiberMass p Y (Y x) * fiberMass p Z (Z x))

def originalRetained (p : α → ℝ) (Y Z : α → ℕ) (R : ℝ) (x : α) : ℝ := by
  classical
  exact if colorMass p Y Z (Y x) (Z x) * (∑ i, p i) ≤
    R * fiberMass p Y (Y x) * fiberMass p Z (Z x) then p x else 0

theorem originalRetained_nonneg (p : α → ℝ) (Y Z : α → ℕ) (R : ℝ)
    (hp : ∀ x, 0 ≤ p x) (x : α) : 0 ≤ originalRetained p Y Z R x := by
  classical
  unfold originalRetained
  split_ifs
  · exact hp x
  · exact le_rfl

theorem originalRetained_le (p : α → ℝ) (Y Z : α → ℕ) (R : ℝ)
    (hp : ∀ x, 0 ≤ p x) (x : α) : originalRetained p Y Z R x ≤ p x := by
  classical
  unfold originalRetained
  split_ifs <;> simp_all

/-- The joint bound retains all original state, palette and total masses. -/
theorem originalRetained_joint_le (p : α → ℝ) (Y Z : α → ℕ) {R : ℝ}
    (hp : ∀ x, 0 ≤ p x) (hR : 0 ≤ R) (e z : ℕ) :
    colorMass (originalRetained p Y Z R) Y Z e z * (∑ i, p i) ≤
      R * fiberMass p Y e * fiberMass p Z z := by
  classical
  have htotal : 0 ≤ ∑ i, p i := Finset.sum_nonneg (fun i _ => hp i)
  by_cases h : colorMass p Y Z e z * (∑ i, p i) ≤
      R * fiberMass p Y e * fiberMass p Z z
  · apply le_trans ?_ h
    apply mul_le_mul_of_nonneg_right _ htotal
    exact Finset.sum_le_sum (fun x _ => originalRetained_le p Y Z R hp x)
  · have hzero : colorMass (originalRetained p Y Z R) Y Z e z = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      obtain ⟨_, hYx, hZx⟩ := Finset.mem_filter.mp hx
      simp only [originalRetained, hYx, hZx, ite_eq_right h]
    rw [hzero, zero_mul]
    exact mul_nonneg (mul_nonneg hR (fiberMass_nonneg p Y hp e)) (fiberMass_nonneg p Z hp z)

theorem original_removed_log_gain (p : α → ℝ) (Y Z : α → ℕ) {R : ℝ}
    (hp : ∀ x, 0 ≤ p x) (hR : 0 < R) (x : α)
    (hx : originalRetained p Y Z R x < p x) :
    Real.log R < max 0 (Real.log (originalLikelihood p Y Z x)) := by
  classical
  have hpx : 0 < p x := lt_of_le_of_lt (originalRetained_nonneg p Y Z R hp x) hx
  have hY : 0 < fiberMass p Y (Y x) := hpx.trans_le
    ((self_le_colorMass p Y Z hp x).trans (colorMass_le_fiberMass p Y Z hp _ _))
  have hZ : 0 < fiberMass p Z (Z x) := hpx.trans_le
    ((self_le_colorMass p Z Y hp x).trans (colorMass_le_fiberMass p Z Y hp _ _))
  have hbad : R * fiberMass p Y (Y x) * fiberMass p Z (Z x) <
      colorMass p Y Z (Y x) (Z x) * (∑ i, p i) := by
    by_contra! hgood
    have hself : p x < p x := by simpa only [originalRetained, ite_eq_left hgood] using hx
    exact lt_irrefl _ hself
  have hratio : R < originalLikelihood p Y Z x := by
    apply (lt_div_iff₀ (mul_pos hY hZ)).2
    simpa only [mul_assoc] using hbad
  exact (Real.log_lt_log hR hratio).trans_le (le_max_right _ _)

/-- Positive likelihood controls deleted ORIGINAL mass for an arbitrary
finite subprobability vector. This is the weighted path-law budget used
before later current-floor deletions. -/
theorem original_removed_mass_le_score (p : α → ℝ) (Y Z : α → ℕ) {R : ℝ}
    (hp : ∀ x, 0 ≤ p x) (hR : 1 < R) :
    (∑ x, (p x - originalRetained p Y Z R x)) ≤
      (∑ x, p x * max 0 (Real.log (originalLikelihood p Y Z x))) / Real.log R := by
  classical
  have hlog : 0 < Real.log R := Real.log_pos hR
  have hpoint (x : α) : (p x - originalRetained p Y Z R x) * Real.log R ≤
      p x * max 0 (Real.log (originalLikelihood p Y Z x)) := by
    by_cases hx : originalRetained p Y Z R x = p x
    · rw [hx, sub_self, zero_mul]
      exact mul_nonneg (hp x) (le_max_left _ _)
    · have hlt := lt_of_le_of_ne (originalRetained_le p Y Z R hp x) hx
      have hzero : originalRetained p Y Z R x = 0 := by
        by_cases h : colorMass p Y Z (Y x) (Z x) * (∑ i, p i) ≤
            R * fiberMass p Y (Y x) * fiberMass p Z (Z x)
        · exact False.elim (hx (by simp only [originalRetained, ite_eq_left h]))
        · simp only [originalRetained, ite_eq_right h]
      rw [hzero, sub_zero]
      exact mul_le_mul_of_nonneg_left (original_removed_log_gain p Y Z hp (by linarith) x hlt).le (hp x)
  apply (le_div_iff₀ hlog).2
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun x _ => hpoint x)

end

end Submission.Obl.k4_scalar_guarded_tangent_preparation
