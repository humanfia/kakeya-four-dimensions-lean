-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o107, session x0735, commit cc2492748f08.
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/ConditionalPalette.lean.
import Submission.Obl.k4_matching_abstract_switching_mixture.Finite

/-! External conditional palette bounds from original state floors and joint numerators. -/

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

open Finset Classical
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

variable {Ω Sf Pal : Type*} [Fintype Ω] [DecidableEq Sf] [DecidableEq Pal]

/-- The refreshed palette atom is its original joint numerator divided by
the original fine-state mass. This includes zero-mass states. -/
theorem conditional_palette_atom
    (P : Ω → ℝ) (key : Ω → Sf) (Z : Ω → Pal) (e : Ω) (z : Pal) :
    (∑ er ∈ univ.filter (fun er => Z er = z), condKey P key e er) =
      fiberMass P (fun er => (key er, Z er)) (key e, z) / atomMass P key e := by
  change (∑ er ∈ univ.filter (fun er => Z er = z), condKey P key e er) =
    (∑ er ∈ univ.filter (fun er => (key er, Z er) = (key e, z)), P er) / atomMass P key e
  rw [sum_div, sum_filter, sum_filter]
  apply sum_congr rfl
  intro er _
  by_cases hz : Z er = z <;> by_cases hk : key er = key e <;>
    simp [condKey, hz, hk]

/-- A joint numerator bounded in original mass units and an original state
floor give the pointwise external palette ceiling used by every traversal. -/
theorem conditional_palette_cap_of_original_floor
    (P : Ω → ℝ) (hP : ∀ e, 0 ≤ P e) (key : Ω → Sf) (Z : Ω → Pal)
    (base : Sf → ℝ) (π : Pal → ℝ) (K : ℝ) (hK : 0 ≤ K) (hπ : ∀ z, 0 ≤ π z)
    (hfloor : ∀ e, atomMass P key e ≠ 0 → base (key e) ≤ atomMass P key e)
    (hnum : ∀ s z, fiberMass P (fun er => (key er, Z er)) (s, z) ≤ K * base s * π z) :
    ∀ e z, (∑ er ∈ univ.filter (fun er => Z er = z), condKey P key e er) ≤ K * π z := by
  intro e z
  rw [conditional_palette_atom]
  by_cases hm : atomMass P key e = 0
  · rw [hm, div_zero]
    exact mul_nonneg hK (hπ z)
  have hm0 : 0 < atomMass P key e :=
    lt_of_le_of_ne (fiberMass_nonneg hP key (key e)) (Ne.symm hm)
  apply (div_le_iff₀ hm0).mpr
  calc
    _ ≤ K * base (key e) * π z := hnum (key e) z
    _ ≤ K * atomMass P key e * π z :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hfloor e hm) hK) (hπ z)
    _ = _ := by ring

end

end Submission.Obl.k4_finite_affine_parent_sources
