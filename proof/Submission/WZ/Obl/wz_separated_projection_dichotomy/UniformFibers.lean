-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.UniformFibers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open scoped BigOperators

/-- A lower fiber bound transfers cardinal estimates to any family of cells. -/
theorem lower_fiber_count {X Y : Type*} [DecidableEq Y]
    (S : Finset X) (T : Finset Y) (f : X → Y) {M : ℝ}
    (hlower : ∀ y ∈ T, M ≤ ((S.filter (fun x => f x = y)).card : ℝ)) :
    M * (T.card : ℝ) ≤ ((S.filter (fun x => f x ∈ T)).card : ℝ) := by
  classical
  calc M * (T.card : ℝ) = ∑ y ∈ T, M := by simp; ring
    _ ≤ ∑ y ∈ T, ((S.filter (fun x => f x = y)).card : ℝ) :=
      Finset.sum_le_sum hlower
    _ = _ := by
      rw [← Nat.cast_sum]
      exact congrArg (Nat.cast : ℕ → ℝ) (Finset.sum_card_fiberwise_eq_card_filter S T f)

/-- An upper fiber bound controls the number of original points in a family
of cells. -/
theorem upper_fiber_count {X Y : Type*} [DecidableEq Y]
    (S : Finset X) (T : Finset Y) (f : X → Y) {M : ℝ}
    (hupper : ∀ y ∈ T, ((S.filter (fun x => f x = y)).card : ℝ) ≤ M) :
    ((S.filter (fun x => f x ∈ T)).card : ℝ) ≤ M * (T.card : ℝ) := by
  classical
  calc ((S.filter (fun x => f x ∈ T)).card : ℝ) =
        ∑ y ∈ T, ((S.filter (fun x => f x = y)).card : ℝ) := by
          rw [← Nat.cast_sum]
          exact congrArg (Nat.cast : ℕ → ℝ) (Finset.sum_card_fiberwise_eq_card_filter S T f).symm
    _ ≤ ∑ y ∈ T, M := Finset.sum_le_sum hupper
    _ = M * (T.card : ℝ) := by simp; ring

/-- A uniform upper bound on fibers bounds the size of any subset by the
size of its image, without an injectivity assumption. -/
theorem card_le_upper_fiber_mul_image {X Y : Type*} [DecidableEq Y]
    (S : Finset X) (f : X → Y) {M : ℝ}
    (hupper : ∀ y ∈ S.image f, ((S.filter (fun x => f x = y)).card : ℝ) ≤ M) :
    (S.card : ℝ) ≤ M * ((S.image f).card : ℝ) := by
  classical
  have h := upper_fiber_count S (S.image f) f hupper
  simpa only [Finset.filter_true_of_mem (fun x hx => Finset.mem_image_of_mem f hx)] using h

end WangZahlLot.Obl.wz_separated_projection_dichotomy
