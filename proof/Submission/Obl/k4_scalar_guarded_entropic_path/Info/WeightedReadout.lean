/-
Adapted from this LOT tree, obligation o168, session x0567, branch x0567 (commit 6f572b8d),
Submission/Obl/k4_scalar_guarded_tangent_preparation/WeightedReadout.lean,
renamed into namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.Info.WeightedInformation
import Submission.Obl.k4_scalar_guarded_entropic_path.Info.StateReadout

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

open Submission.Obl.k4_matching_palette_likelihood

noncomputable section

/-- An actual grid-state readout of a rich common path record inherits
the original weighted information budget with only one extra unit. -/
theorem weighted_state_readout_score_le {α : Type*} [Fintype α] {w : ℕ}
    (p : α → ℝ) (F : α → Fin w) (E Y V : α → ℕ)
    (r : Fin w → α → ℝ) (ω : Fin w → ℝ) (mass : ℝ)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hr : ∀ g x, 0 ≤ r g x) (hω : ∀ g, 0 ≤ ω g) (hmass : 0 < mass)
    (hworld : ∀ g x, ω g * r g x = if F x = g then mass * p x else 0)
    (hEF : ∀ x y, E x = E y → F x = F y)
    (hEY : ∀ x y, E x = E y → Y x = Y y) :
    (∑ g, ω g * ∑ x, r g x * max 0 (Real.log (originalLikelihood (r g)
      (pairedRecord (fun z => (F z).val) Y) V x))) ≤
      mass * (positiveScore p (fun z => (F z).val) E V + 1) := by
  let H := fun x => (F x).val
  have hnest : ∀ x y, pairedRecord H Y x = pairedRecord H Y y → F x = F y :=
    fun _ _ h => Fin.ext (Nat.pair_eq_pair.mp h).1
  rw [weighted_original_score_eq p F (pairedRecord H Y) V r ω mass hp hr hω hmass hnest hworld]
  apply mul_le_mul_of_nonneg_left _ hmass.le
  apply state_readout_score_le p H E (pairedRecord H Y) V hp hp1
  · intro x y h
    exact congrArg Fin.val (hEF x y h)
  · intro x y h
    exact (Nat.pair_eq_pair.mp h).1
  · intro x y h
    exact Nat.pair_eq_pair.mpr ⟨congrArg Fin.val (hEF x y h), hEY x y h⟩

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
