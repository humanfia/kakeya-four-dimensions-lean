-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.UpperBodies.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/UpperBodies.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.LocalCoefficient
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyTransport
import Submission.WZ.Obl.wz_separated_cover_refinement.Covers

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_concentrated_convex_factorization (Upper count)
open WangZahlLot.Obl.wz_flat_factored_improvement (BodyConvexCount)
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate enumerate_count)

noncomputable section

/-- Enumerating a selected block turns its convex upper bound into the
finite-body interface without changing any coefficient. -/
theorem upper_enumerate_body_count {L : ℕ} {U : Fin L → Set V} {w m : ℝ}
    {R : Finset (Fin L)} (h : Upper U w R m) :
    BodyConvexCount (fun i => U (enumerate R i)) w m := by
  classical
  intro W hW
  change O (({i | U (enumerate R i) ⊆ W}.ncard : ℝ) * w) ≤ O m * μ W
  rw [enumerate_count R (fun i => U i ⊆ W)]
  exact h W hW

/-- The convex bound on a selected block survives common affine normalization. -/
theorem upper_enumerate_affine_body_count {L : ℕ} {U : Fin L → Set V} {w m J : ℝ}
    {R : Finset (Fin L)} (hw : 0 ≤ w) (hJ : 0 < J) (f : V ≃ᵃ[ℝ] V)
    (hvol : ∀ W, μ (f '' W) = O J * μ W) (h : Upper U w R m) :
    BodyConvexCount (fun i => f '' U (enumerate R i)) (J * w) m :=
  (upper_enumerate_body_count h).affine_image hw hJ f hvol

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
