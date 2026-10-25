import Submission.Obl.k4_marked_scalar_grid_selection.Selection
import Submission.Obl.k4_marked_scalar_grid_selection.FrozenBands

namespace Submission.Obl.k4_marked_scalar_grid_selection

open MeasureTheory Set Filter Scalar
open scoped ENNReal

theorem select_tables
    (N K : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : Subpower N K) (s m V : ℝ) (hs : 0 < s) (hsm : s < m) (hV : 0 < V)
    (M : ℕ) (H J : ℕ → ℕ)
    (b : (k : ℕ) → Fin (H k) → Fin 5 → ℝ)
    (w : (k : ℕ) → Fin (H k) → ℝ)
    (mark : (k : ℕ) → Fin (H k) → Fin (J k) → Bool)
    (htables : ∀ k, tables (N k) (K k) m M (H k) (J k) (b k) (w k) (mark k)) :
    ∃ L : ℕ → ℝ, Subpower N L ∧ (∀ k, K k ≤ L k) ∧
      ∃ mark' : (k : ℕ) → Fin (H k) → Fin (J k) → Bool,
        (∀ k, tables (N k) (L k) m M (H k) (J k) (b k) (w k) (mark' k)) ∧
        (∀ k j z, mark' k j z = true → mark k j z = true) ∧
        gridData N s V (fun k => law (N k ^ (-m)) (H k) (J k) (b k) (w k) (mark' k)) := by
  have hn1 (k : ℕ) : 1 ≤ N k := by linarith [hN k]
  have hn0 (k : ℕ) : 0 < N k := by linarith [hN k]
  have hσ (k : ℕ) : 0 < N k ^ (-m) := Real.rpow_pos_of_pos (hn0 k) _
  have hσ₁ (k : ℕ) : N k ^ (-m) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (hn1 k) (by linarith)
  have hj (k : ℕ) : 0 < J k := by have := (htables k).1; omega
  apply selection_of_exact_densities N K hN hNt hK s m V hs hsm hV M H J b w mark htables
    (fun k T r => ((law (N k ^ (-m)) (H k) (J k) (b k) (w k) (markOf T)).map
      (obs (N k) r)).rnDeriv reference)
    (fun k T r u => ((law (N k ^ (-m)) (H k) (J k) (b k) (w k) (markOf T)).map
      (aug (N k) r u)).rnDeriv jointReference)
  · intro k T r hr hrs
    exact frozen_pure_rnDeriv (hj k) (hσ k) (hσ₁ k) (htables k).2.2.2.1
      (Real.rpow_le_rpow_of_exponent_le (hn1 k) (by linarith))
      (by linarith [hK.1 k]) (b k) (htables k).2.2.2.2.2.2.2.1 (w k) T
  · intro k T r u hr hrs hu huV
    exact frozen_joint_rnDeriv (hj k) (hσ k) (htables k).2.2.2.1 (hn0 k)
      (Real.rpow_le_rpow_of_exponent_le (hn1 k) (by linarith))
      (by linarith [hK.1 k]) (b k) (htables k).2.2.2.2.2.2.2.1 (w k) T

end Submission.Obl.k4_marked_scalar_grid_selection
