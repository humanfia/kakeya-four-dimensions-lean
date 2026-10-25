-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/SubpowerEnvelope.lean
import Submission.Lib.K4ModelReduction.Diagonal

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open Filter

/-- Eventual witnesses at every fixed positive exponent give a single
subpower envelope. The witnesses themselves need not be monotone in the bound. -/
theorem exists_subpower_envelope (N : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k)
    (P : ℕ → ℝ → Prop)
    (hP : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, P k (N k ^ ε)) :
    ∃ H : ℕ → ℝ, (∀ k, 1 ≤ H k) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε) ∧
      ∀ᶠ k in atTop, P k (H k) := by
  obtain ⟨j, δ, _, _, hδpos, _, hδlim, hgood⟩ :=
    Submission.Lib.K4ModelReduction.exists_slow_tolerance
      (fun _ ε k => P k (N k ^ ε)) (fun _ ε hε => hP ε hε)
  refine ⟨fun k => N k ^ δ k, ?_, ?_, ?_⟩
  · intro k
    exact Real.one_le_rpow (hN k) (hδpos k).le
  · intro ε hε
    filter_upwards [(tendsto_order.1 hδlim).2 ε hε] with k hk
    exact Real.rpow_le_rpow_of_exponent_le (hN k) hk.le
  · filter_upwards [hgood] with k hk
    exact hk 0 (Nat.zero_le _)

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover
