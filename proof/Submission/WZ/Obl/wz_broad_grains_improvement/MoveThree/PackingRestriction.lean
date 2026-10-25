-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PackingRestriction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PackingRestriction.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyCounts

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_flat_factored_improvement (BodyPacking)

/-- Independent quadratic packing is preserved under an injective choice
of bodies, without replacing it by the convex-count coefficient. -/
theorem packing_restrict {n k : ℕ} {U : Fin n → Set V} {w p : ℝ}
    (hw : 0 ≤ w) (hpack : BodyPacking U w p) (f : Fin k → Fin n)
    (hf : Function.Injective f) : BodyPacking (U ∘ f) w p := by
  intro Q hQ
  apply (ENNReal.ofReal_le_ofReal _).trans (hpack Q hQ)
  apply mul_le_mul_of_nonneg_right _ hw
  apply Real.sqrt_le_sqrt
  exact Nat.cast_le.mpr (Set.ncard_le_ncard_of_injOn f (fun _ hi => hi) hf.injOn)

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
