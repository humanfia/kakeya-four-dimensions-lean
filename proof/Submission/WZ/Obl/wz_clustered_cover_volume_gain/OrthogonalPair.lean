-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.OrthogonalPair.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open LeanEval.Analysis.WangZahlKakeya

lemma basis_of_orthogonal_pair {n l : Space} (hn : ‖n‖ = 1) (hl : ‖l‖ = 1)
    (hnl : inner ℝ n l = 0) :
    ∃ u : OrthonormalBasis (Fin 3) ℝ Space, u 0 = n ∧ u 2 = l := by
  classical
  let S : Set (Fin 3) := {0, 2}
  let v : Fin 3 → Space := ![n, 0, l]
  have hln : inner ℝ l n = 0 := by rwa [real_inner_comm]
  have ho : Orthonormal ℝ (S.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : i = 0 ∨ i = 2 := by simpa [S] using hi
    have hj' : j = 0 ∨ j = 2 := by simpa [S] using hj
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;>
      simp [v, Set.domRestrict, hn, hl, hnl, hln, real_inner_self_eq_norm_sq]
  obtain ⟨u, hu⟩ := ho.exists_orthonormalBasis_extension_of_card_eq (by simp [Space])
  refine ⟨u, ?_, ?_⟩
  · simpa [v] using hu 0 (by simp [S])
  · simpa [v] using hu 2 (by simp [S])

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
