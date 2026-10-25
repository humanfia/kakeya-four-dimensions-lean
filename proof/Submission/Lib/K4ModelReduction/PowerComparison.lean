import Mathlib

/-! Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper. -/

/-! Passing quantified finite subpower bounds to profile exponent inequalities. -/

namespace Submission.Lib.K4ModelReduction

open Filter

/-- A subpower multiplier cannot reverse a fixed ordering of resolution
exponents. The statement applies unchanged on every subsequence. -/
theorem exponent_le_of_subpower_loss (N K : ℕ → ℝ) {a b : ℝ}
    (hN : Tendsto N atTop atTop)
    (hK : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, K j ≤ N j ^ ε)
    (hfit : ∀ᶠ j in atTop, N j ^ a ≤ K j * N j ^ b) : a ≤ b := by
  by_contra hn
  have hgap : 0 < a - b := sub_pos.mpr (lt_of_not_ge hn)
  let ε : ℝ := (a - b) / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨j, hNj, hKj, hfitj⟩ :=
    ((hN.eventually (eventually_gt_atTop 1)).and ((hK ε hε).and hfit)).exists
  have hpower : N j ^ a ≤ N j ^ (ε + b) := by
    calc
      _ ≤ K j * N j ^ b := hfitj
      _ ≤ N j ^ ε * N j ^ b :=
        mul_le_mul_of_nonneg_right hKj (Real.rpow_nonneg (by linarith) _)
      _ = N j ^ (ε + b) := (Real.rpow_add (by linarith) _ _).symm
  have hh := (Real.rpow_le_rpow_left_iff hNj).1 hpower
  dsimp [ε] at hh
  linarith

/-- The terminal observation-cover estimate forces the first density gain
`1-f ≥ σ` once the selected mass and density slack have subpower losses. -/
theorem terminal_profile_gain (N K : ℕ → ℝ) (σ f : ℝ)
    (hN : Tendsto N atTop atTop)
    (hK : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, K j ≤ N j ^ ε)
    (hmass : ∀ᶠ j in atTop, 1 ≤ K j * N j ^ (1 - σ - f)) :
    σ ≤ 1 - f := by
  have hh := exponent_le_of_subpower_loss N K hN hK
    (a := 0) (b := 1 - σ - f) (by simpa only [Real.rpow_zero] using hmass)
  linarith

end Submission.Lib.K4ModelReduction
