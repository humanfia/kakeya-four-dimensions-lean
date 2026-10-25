-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.GGXBridge.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.WeakGrainsGlue
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormDefs

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

/-- The weak grains of `gg_theorem` give x0214's `GGX`. -/
theorem ggx_of_weakGrains {σ : ℝ} (h : ∀ ε d0 : ℝ, 0 < ε → 0 < d0 → WeakGrainsAt σ ε d0) :
    GGX σ := by
  intro η d0 hη hd0
  obtain ⟨δ, hδ, hδd0, hδ100, n, x, v, Y, hF, hS, -, f, V, hf, hslice, hVu, hVp, hVL, hloc⟩ :=
    h η d0 hη hd0
  exact ⟨δ, hδ, hδd0, hδ100, n, x, v, Y, hF, hS, f, V, hf, hslice, hVu, hVp,
    fun p hp q hq => hVL p q hp hq, hloc⟩

/-- `GGX` from the extremal exponent. -/
theorem ggx_of_examples {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hbelow : ∀ t, t < σ → Examples t) (habove : ∀ t, σ < t → ¬Examples t) : GGX σ :=
  ggx_of_weakGrains (weak_grains_of_examples hσ0 hσ1 hbelow habove)

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
