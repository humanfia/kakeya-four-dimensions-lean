-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_iteration.Orientation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_iteration.Basic

namespace WangZahlLot.Obl.wz_normalized_projection_iteration

noncomputable def orientStart (x v : Space) : Space := if 0 ≤ v 2 then x else x + v
noncomputable def orientDir (v : Space) : Space := if 0 ≤ v 2 then v else -v

theorem tube_orient (δ : ℝ) (x v : Space) :
    Tube δ (orientStart x v) (orientDir v) = Tube δ x v := by
  unfold orientStart orientDir
  split_ifs with h
  · rfl
  · simp only [add_neg_cancel_right, Tube, segment_symm]

theorem norm_orientDir (v : Space) : ‖orientDir v‖ = ‖v‖ := by
  unfold orientDir
  split_ifs <;> simp

theorem orientDir_vertical {v : Space} (hv : (1 / 2 : ℝ) ≤ |v 2|) :
    (1 / 2 : ℝ) ≤ orientDir v 2 := by
  unfold orientDir
  split_ifs with h
  · simpa only [abs_of_nonneg h] using hv
  · simpa only [PiLp.neg_apply, abs_of_neg (lt_of_not_ge h)] using hv

theorem family_orient {η δ : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : Family η δ n x v Y) :
    Family η δ n (fun i => orientStart (x i) (v i)) (fun i => orientDir (v i)) Y := by
  simpa only [Family, norm_orientDir, tube_orient] using h

theorem frostman_orient {η δ : ℝ} {n : ℕ} {x v : Fin n → Space} (h : Frostman η δ n x v) :
    Frostman η δ n (fun i => orientStart (x i) (v i)) (fun i => orientDir (v i)) := by
  simpa only [Frostman, tube_orient] using h

end WangZahlLot.Obl.wz_normalized_projection_iteration
