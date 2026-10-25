/-
Adapted from this LOT tree, o075, session x0249, commit c9860862e62947c5fb8b3bc42c0a4ebc874a7eee,
Submission/Obl/k4_joint_homogenization/Labels.lean. Earlier source attributions are retained below.
-/

import Mathlib

/-!
# Finite fibers of native hidden and angular label coarsening
-/
open Set MeasureTheory
open scoped ENNReal
namespace Submission.Obl.k4_native_grid_profile_extension

theorem count_prod_eq {B C : Type*} [MeasurableSpace B] [MeasurableSpace C]
    [Countable B] [Countable C] [MeasurableSingletonClass B] [MeasurableSingletonClass C] :
    (Measure.count : Measure B).prod (Measure.count : Measure C) = Measure.count := by
  apply Measure.ext_of_singleton
  intro p
  rcases p with ⟨b, c⟩
  rw [← singleton_prod_singleton, Measure.prod_prod]
  simp

def integerFiber (D : ℕ) (c : ℤ) : Finset ℤ :=
  Finset.Ico (c * D) (c * D + D)

theorem ediv_fiber_eq {D : ℕ} (hD : 0 < D) (c : ℤ) :
    {z : ℤ | z / (D : ℤ) = c} = (integerFiber D c : Set ℤ) := by
  ext z
  simp only [mem_ofPred_eq, integerFiber, Finset.mem_coe, Finset.mem_Ico]
  exact Int.ediv_eq_iff_of_pos (by exact_mod_cast hD)

theorem integerFiber_card (D : ℕ) (c : ℤ) : (integerFiber D c).card = D := by
  simp [integerFiber]

theorem count_ediv_fiber {D : ℕ} (hD : 0 < D) (c : ℤ) :
    Measure.count {z : ℤ | z / (D : ℤ) = c} = (D : ℝ≥0∞) := by
  rw [ediv_fiber_eq hD, Measure.count_apply_finset, integerFiber_card]

end Submission.Obl.k4_native_grid_profile_extension

namespace Submission.Obl.k4_native_grid_profile_extension
abbrev JointLabel := ℤ × (Fin 2 → ℤ)

def labelQuotient (Dw Du : ℕ) (z : JointLabel) : JointLabel :=
  (z.1 / (Dw : ℤ), fun j => z.2 j / (Du : ℤ))

def labelFiber (Dw Du : ℕ) (c : JointLabel) : Finset JointLabel :=
  (integerFiber Dw c.1) ×ˢ (Fintype.piFinset fun j => integerFiber Du (c.2 j))

theorem label_fiber_eq {Dw Du : ℕ} (hw : 0 < Dw) (hu : 0 < Du) (c : JointLabel) :
    {z : JointLabel | labelQuotient Dw Du z = c} = (labelFiber Dw Du c : Set JointLabel) := by
  ext z
  change labelQuotient Dw Du z = c ↔ z ∈ labelFiber Dw Du c
  rcases c with ⟨cw, cv⟩
  rcases z with ⟨zw, zv⟩
  simp only [labelQuotient, labelFiber, Prod.mk.injEq, funext_iff,
    Finset.mem_product, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hz, hv⟩
    exact ⟨(congrArg (fun s : Set ℤ => zw ∈ s) (ediv_fiber_eq hw cw)).mp hz,
      fun j => (congrArg (fun s : Set ℤ => zv j ∈ s) (ediv_fiber_eq hu (cv j))).mp (hv j)⟩
  · rintro ⟨hz, hv⟩
    exact ⟨(congrArg (fun s : Set ℤ => zw ∈ s) (ediv_fiber_eq hw cw)).mpr hz,
      fun j => (congrArg (fun s : Set ℤ => zv j ∈ s) (ediv_fiber_eq hu (cv j))).mpr (hv j)⟩

theorem labelFiber_card (Dw Du : ℕ) (c : JointLabel) :
    (labelFiber Dw Du c).card = Dw * Du ^ 2 := by
  simp [labelFiber, integerFiber_card, Fintype.card_piFinset]

theorem count_labelQuotient_fiber {Dw Du : ℕ} (hw : 0 < Dw) (hu : 0 < Du)
    (c : JointLabel) :
    Measure.count {z : JointLabel | labelQuotient Dw Du z = c} =
      ((Dw * Du ^ 2 : ℕ) : ℝ≥0∞) := by
  rw [label_fiber_eq hw hu, Measure.count_apply_finset, labelFiber_card]

end Submission.Obl.k4_native_grid_profile_extension
