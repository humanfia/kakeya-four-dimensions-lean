import Mathlib

/-!
Adapted from o079/x0261 Uniformity.lean, commit 2cdde81.

The passage from sequential subpower statements to uniform finite tolerances
in the last paragraph of the scalar mesh projection argument.
-/

open Filter
open scoped Topology

namespace Submission.Obl.k4_scalar_mesh_block_reduction

/-- A vanishing exponent produces a subpower loss, even when the base grows
arbitrarily fast. -/
theorem subpower_of_vanishing_exponent (N η : ℕ → ℝ)
    (hN : ∀ k, 1 ≤ N k) (hη : ∀ k, 0 ≤ η k)
    (hlim : Tendsto η atTop (𝓝 0)) :
    (∀ k, 1 ≤ N k ^ η k) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, N k ^ η k ≤ N k ^ ε := by
  constructor
  · intro k
    exact Real.one_le_rpow (hN k) (hη k)
  · intro ε hε
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with k hk
    exact Real.rpow_le_rpow_of_exponent_le (hN k) hk.le

/-- To prove a uniform finite statement, it suffices to obtain one successful
sample along every sequence with vanishing input loss and diverging bases.
The model type may vary with the parameters and may contain an arbitrary
measurable space. -/
theorem uniformity_of_sequence {Model : ℝ → ℝ → Type*}
    (admissible result : (η N : ℝ) → Model η N → Prop)
    (hseq : ∀ (η N : ℕ → ℝ),
      (∀ k, 0 < η k) → Tendsto η atTop (𝓝 0) →
      (∀ k, 2 ≤ N k) → Tendsto N atTop atTop →
      ∀ model : (k : ℕ) → Model (η k) (N k),
      (∀ k, admissible (η k) (N k) (model k)) →
      ∃ k, result (η k) (N k) (model k)) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ∀ model : Model η N,
        admissible η N model → result η N model := by
  classical
  by_contra h
  push Not at h
  have hcounter (k : ℕ) :
      ∃ N : ℝ, (k : ℝ) + 2 ≤ N ∧
        ∃ model : Model (1 / ((k : ℝ) + 1)) N,
          admissible (1 / ((k : ℝ) + 1)) N model ∧
            ¬ result (1 / ((k : ℝ) + 1)) N model := by
    exact h (1 / ((k : ℝ) + 1)) (by positivity) ((k : ℝ) + 2) (by linarith [Nat.cast_nonneg (α := ℝ) k])
  choose N hN model hmodel hbad using hcounter
  have hNtwo k : 2 ≤ N k :=
    le_trans (by linarith [Nat.cast_nonneg (α := ℝ) k]) (hN k)
  have hNlim : Tendsto N atTop atTop := by
    exact tendsto_atTop_mono
      (fun k => (le_add_of_nonneg_right (show (0 : ℝ) ≤ 2 by norm_num)).trans (hN k))
      tendsto_natCast_atTop_atTop
  obtain ⟨k, hk⟩ := hseq (fun k => 1 / ((k : ℝ) + 1)) N (fun k => by positivity)
    tendsto_one_div_add_atTop_nhds_zero_nat hNtwo hNlim model hmodel
  exact hbad k hk

end Submission.Obl.k4_scalar_mesh_block_reduction
