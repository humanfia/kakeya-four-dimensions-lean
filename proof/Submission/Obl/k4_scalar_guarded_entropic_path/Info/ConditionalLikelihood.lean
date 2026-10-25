/-
Adapted from this LOT tree, obligation o168, session x0567, branch x0567 (commit 6f572b8d),
Submission/Obl/k4_scalar_guarded_tangent_preparation/ConditionalLikelihood.lean,
renamed into namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.Info.AppendedScore
import Submission.Obl.k4_scalar_guarded_entropic_path.Info.UnnormalizedTruncation

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

open Submission.Obl.k4_matching_palette_likelihood

noncomputable section

variable {α : Type*} [Fintype α]

def parentSlice (p : α → ℝ) (F : α → ℕ) (e : ℕ) (x : α) : ℝ := by
  classical
  exact if F x = e then p x else 0

theorem sum_parentSlice (p : α → ℝ) (F : α → ℕ) (e : ℕ) :
    (∑ x, parentSlice p F e x) = fiberMass p F e := by
  classical
  unfold parentSlice fiberMass
  rw [Finset.sum_filter]

theorem fiberMass_parentSlice_fine (p : α → ℝ) (F E : α → ℕ)
    (hnest : ∀ x y, E x = E y → F x = F y) (x : α) :
    fiberMass (parentSlice p F (F x)) E (E x) = fiberMass p E (E x) := by
  classical
  unfold fiberMass
  apply Finset.sum_congr rfl
  intro y hy
  have hF := hnest y x (Finset.mem_filter.mp hy).2
  simp only [parentSlice, ite_eq_left hF]

theorem colorMass_parentSlice_fine (p : α → ℝ) (F E Z : α → ℕ)
    (hnest : ∀ x y, E x = E y → F x = F y) (x : α) :
    colorMass (parentSlice p F (F x)) E Z (E x) (Z x) = colorMass p E Z (E x) (Z x) := by
  classical
  unfold colorMass
  apply Finset.sum_congr rfl
  intro y hy
  have hF := hnest y x (Finset.mem_filter.mp hy).2.1
  simp only [parentSlice, ite_eq_left hF]

theorem fiberMass_parentSlice_velocity (p : α → ℝ) (F Z : α → ℕ) (x : α) :
    fiberMass (parentSlice p F (F x)) Z (Z x) = colorMass p F Z (F x) (Z x) := by
  classical
  unfold fiberMass colorMass parentSlice
  simp_rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hF : F y = F x <;> by_cases hZ : Z y = Z x <;> simp only [hF, hZ, ite_true, ite_false,
    true_and, false_and]

/-- Conditioning the original finite law on a parent fiber gives exactly
the original parent-relative likelihood ratio. No success-conditioned
palette or parent denominator appears. -/
theorem originalLikelihood_parentSlice (p : α → ℝ) (F E Z : α → ℕ)
    (hp : ∀ x, 0 ≤ p x) (hnest : ∀ x y, E x = E y → F x = F y)
    {x : α} (hpx : 0 < p x) :
    originalLikelihood (parentSlice p F (F x)) E Z x =
      posterior p E Z x / posterior p F Z x := by
  have hF : 0 < fiberMass p F (F x) := hpx.trans_le
    ((self_le_colorMass p F Z hp x).trans (colorMass_le_fiberMass p F Z hp _ _))
  have hE : 0 < fiberMass p E (E x) := hpx.trans_le
    ((self_le_colorMass p E Z hp x).trans (colorMass_le_fiberMass p E Z hp _ _))
  have hFZ : 0 < colorMass p F Z (F x) (Z x) := hpx.trans_le (self_le_colorMass p F Z hp x)
  unfold originalLikelihood
  rw [colorMass_parentSlice_fine p F E Z hnest, sum_parentSlice,
    fiberMass_parentSlice_fine p F E hnest, fiberMass_parentSlice_velocity]
  unfold posterior
  field_simp [hF.ne', hE.ne', hFZ.ne']

theorem fiberMass_const_mul (p : α → ℝ) (F : α → ℕ) (e : ℕ) (c : ℝ) :
    fiberMass (fun x => c * p x) F e = c * fiberMass p F e := by
  classical
  exact (Finset.mul_sum _ _ _).symm

theorem colorMass_const_mul (p : α → ℝ) (F Z : α → ℕ) (e z : ℕ) (c : ℝ) :
    colorMass (fun x => c * p x) F Z e z = c * colorMass p F Z e z := by
  classical
  exact (Finset.mul_sum _ _ _).symm

/-- An original world's constant mass normalization cancels out of its
unnormalized likelihood. -/
theorem originalLikelihood_const_mul (p : α → ℝ) (E Z : α → ℕ)
    (hp : ∀ x, 0 ≤ p x) {x : α} (hpx : 0 < p x) {c : ℝ} (hc : c ≠ 0) :
    originalLikelihood (fun y => c * p y) E Z x = originalLikelihood p E Z x := by
  have hE : 0 < fiberMass p E (E x) := hpx.trans_le
    ((self_le_colorMass p E Z hp x).trans (colorMass_le_fiberMass p E Z hp _ _))
  have hZ : 0 < fiberMass p Z (Z x) := hpx.trans_le
    ((self_le_colorMass p Z E hp x).trans (colorMass_le_fiberMass p Z E hp _ _))
  unfold originalLikelihood
  rw [colorMass_const_mul, fiberMass_const_mul, fiberMass_const_mul, ← Finset.mul_sum]
  field_simp [hE.ne', hZ.ne', hc]

/-- Summing the original unnormalized parent scores recovers exactly the
single global parent-relative score, with the original masses. -/
theorem parentSlice_score_decomposition (p : α → ℝ) (F E Z : α → ℕ)
    (hp : ∀ x, 0 ≤ p x) (hnest : ∀ x y, E x = E y → F x = F y) :
    (∑ e ∈ Finset.univ.image F, ∑ x, parentSlice p F e x * max 0
      (Real.log (originalLikelihood (parentSlice p F e) E Z x))) = positiveScore p F E Z := by
  classical
  unfold positiveScore
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : p x = 0
  · simp only [parentSlice, hx, ite_self, zero_mul, Finset.sum_const_zero]
  · rw [Finset.sum_eq_single (F x)]
    · rw [originalLikelihood_parentSlice p F E Z hp hnest (lt_of_le_of_ne (hp x) (Ne.symm hx))]
      simp [parentSlice]
    · intro e _ he
      simp only [parentSlice, ite_eq_right (Ne.symm he), zero_mul]
    · intro he
      exact False.elim (he (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩))

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
