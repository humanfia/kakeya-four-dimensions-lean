-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_finite_load_selection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_nsp_finite_load_selection.Moment
import Submission.WZ.Obl.wz_nsp_finite_load_selection.Entropy
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_nsp_finite_load_selection`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_nsp_finite_load_selection`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_nsp_finite_load_selection/`
belong to this obligation.
-/

theorem WangZahlLot.wz_nsp_finite_load_selection : ∀ a d : ℝ, 1 ≤ a → 1 ≤ d → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ) (K H m N : ℕ) (X : Fin K → Fin H → Fin m → ℝ), 0 < r → r ≤ 1 → 0 < m → (H : ℝ) ≤ d * r ^ (-d) → (∀ (k : Fin K) (h : Fin H) (s : Fin m), 0 ≤ X k h s ∧ X k h s ≤ 1) → (∀ (k : Fin K) (h : Fin H), (N : ℝ) * Finset.sum Finset.univ (fun s : Fin m => X k h s) ≤ a * (m : ℝ)) → ∃ f : Fin N → Fin m, ∀ (k : Fin K) (h : Fin H), Finset.sum Finset.univ (fun j : Fin N => X k h (f j)) ≤ C * r ^ (-ε) * Real.log (2 + (K : ℝ)) := by
  intro a d ha hd ε hε
  obtain ⟨C, hC, hbound⟩ :=
    WangZahlLot.Obl.wz_nsp_finite_load_selection.entropy_absorption a d ha hd ε hε
  refine ⟨C, hC, ?_⟩
  intro r K H m N X hr hr1 hm hH hX havg
  obtain ⟨f, hf⟩ :=
    WangZahlLot.Obl.wz_nsp_finite_load_selection.finite_load_selection_log hm X hX havg
  exact ⟨f, fun k h => (hf k h).trans (hbound r K H hr hr1 hH)⟩
