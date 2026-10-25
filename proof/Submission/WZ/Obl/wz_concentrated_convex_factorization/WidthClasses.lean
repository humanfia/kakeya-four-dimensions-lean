-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_concentrated_convex_factorization.WidthClasses.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_concentrated_convex_factorization

noncomputable section

/-- Round a width upwards in a fixed finite geometric grid. -/
theorem width_classes {δ r : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 2) (hr : 1 ≤ r)
    (q : ℕ) (hmax : 2 ≤ δ * r ^ q) :
    ∃ (grid : Fin (q + 1) → ℝ) (color : ℝ → Fin (q + 1)),
      (∀ j, δ ≤ grid j ∧ grid j ≤ 2) ∧
      ∀ t : ℝ, δ ≤ t → t ≤ 2 → t ≤ grid (color t) ∧ grid (color t) ≤ r * t := by
  classical
  let grid : Fin (q + 1) → ℝ := fun j => min 2 (δ * r ^ j.val)
  have hex (t : ℝ) (ht : t ≤ 2) : ∃ j : ℕ, t ≤ δ * r ^ j := ⟨q, ht.trans hmax⟩
  let color : ℝ → Fin (q + 1) := fun t =>
    if ht : t ≤ 2 then ⟨Nat.find (hex t ht), Nat.lt_succ_of_le (Nat.find_min' _ (ht.trans hmax))⟩
    else ⟨0, Nat.zero_lt_succ _⟩
  refine ⟨grid, color, ?_, ?_⟩
  · intro j
    exact ⟨le_min hδ2 (le_mul_of_one_le_right hδ.le (one_le_pow₀ hr)), min_le_left _ _⟩
  · intro t htδ ht2
    let j := Nat.find (hex t ht2)
    have hj : t ≤ δ * r ^ j := Nat.find_spec (hex t ht2)
    have hc : (color t).val = j := by simp [color, ht2, j]
    have hgrid : grid (color t) = min 2 (δ * r ^ j) := by dsimp only [grid]; rw [hc]
    rw [hgrid]
    refine ⟨le_min ht2 hj, ?_⟩
    cases hj0 : j with
    | zero =>
        simp only [hj0, pow_zero, mul_one]
        exact (min_le_right _ _).trans (htδ.trans (le_mul_of_one_le_left (hδ.le.trans htδ) hr))
    | succ k =>
        have hk : k < Nat.find (hex t ht2) := by change k < j; omega
        have hh : δ * r ^ k < t := lt_of_not_ge (Nat.find_min (hex t ht2) hk)
        apply (min_le_right _ _).trans
        rw [pow_succ]
        nlinarith [mul_le_mul_of_nonneg_right hh.le (by linarith : 0 ≤ r)]

end
end WangZahlLot.Obl.wz_concentrated_convex_factorization
