import Submission.Obl.k4_scalar_grid_cartesian_field.Interface
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Growth
import Submission.Obl.k4_tempered_grid_selection.SelectionMass
import Submission.Lib.K4ModelReduction.Diagonal
import Submission.Obl.k4_scalar_mesh_block_reduction.Uniformity

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Filter

abbrev SubpowerLoss := Submission.Obl.k4_scalar_marked_coefficient_smoothing.Subpower

/-- A vanishing exponent gives a loss in the frozen subpower convention. -/
theorem subpower_of_vanishing_exponent {N ε : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hε : ∀ k, 0 ≤ ε k)
    (hlim : Tendsto ε atTop (nhds 0)) :
    SubpowerLoss N (fun k => N k ^ ε k) := by
  exact Submission.Obl.k4_scalar_mesh_block_reduction.subpower_of_vanishing_exponent N ε hN hε hlim

/-- Choose a slowly vanishing accuracy after proving every fixed positive accuracy.
The resulting reciprocal spatial scale is still subpower. -/
theorem exists_subpower_accuracy {N : ℕ → ℝ} (hN : ∀ k, 1 ≤ N k)
    (P : ℝ → ℕ → Prop) (hP : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, P ε k) :
    ∃ ε : ℕ → ℝ, (∀ k, 0 < ε k) ∧ Tendsto ε atTop (nhds 0) ∧
      SubpowerLoss N (fun k => N k ^ ε k) ∧ ∀ᶠ k in atTop, P (ε k) k := by
  obtain ⟨j, ε, _, _, hε, _, hlim, hgood⟩ :=
    Submission.Lib.K4ModelReduction.exists_slow_tolerance (fun _ => P) (fun _ => hP)
  refine ⟨ε, hε, hlim, subpower_of_vanishing_exponent hN (fun k => (hε k).le) hlim, ?_⟩
  filter_upwards [hgood] with k hk
  exact hk 0 (Nat.zero_le _)

/-- Every fixed polynomial in an existing subpower loss is eventually below a positive power. -/
theorem eventually_polynomial_subpower_le {N H : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop) (hH : SubpowerLoss N H)
    {A ε : ℝ} (hA : 1 ≤ A) (p : ℕ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, A * H k ^ p ≤ N k ^ ε :=
  (Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_polynomial
    hN hNt hH hA p).2 ε hε

end Submission.Obl.k4_scalar_grid_cartesian_field
