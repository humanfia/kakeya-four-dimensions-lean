-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.WeakGrainsGlue.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.PlaneGrainsTransfer
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.GGTheorem

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

/-- The plane-grains transfer in the form used by `gg_theorem`. -/
theorem planeGrainsTransferAt_of {σ : ℝ} (h : PlaneGrainsTransfer σ) :
    PlaneGrainsTransferAt σ := h

/-- **Weak global grains** from the extremal exponent: the plane-grains transfer (x0170) feeds the
global grains by fibre rescaling (x0158). -/
theorem weak_grains_of_examples {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hbelow : ∀ t, t < σ → Examples t) (habove : ∀ t, σ < t → ¬Examples t) :
    ∀ ε d0 : ℝ, 0 < ε → 0 < d0 → WeakGrainsAt σ ε d0 :=
  gg_theorem hσ0 hσ1 hbelow habove (planeGrainsTransferAt_of (plane_grains_transfer hσ0 hσ1 habove))

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
