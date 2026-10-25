-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.TwoScaleBridge.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.LipschitzChain

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

/-- The frozen two-scale interface implies the pinned one. -/
theorem TwoScaleAt.toP {σ ε δ ρc : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : TwoScaleAt σ ε δ ρc n x v Y) : TwoScaleAtP σ ε δ ρc n x v Y := by
  obtain ⟨Y', k, z, w, Yt, a, s, M, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15, ⟨ρ0, k0, z0, w0, g, hδρ0, hρ0lo, hρ0hi, hg, -, hw0, -, -, -, -, -, hsep, hcov⟩,
    h17, h18, h19, h20⟩ := h
  refine ⟨Y', k, z, w, Yt, a, s, M, h1, h2, h3, h4, h5, h6, h7, h8, h9, h17, h18, h10, h11,
    h12, h13, h14, h15, ⟨ρ0, fun j => z0 (g j), fun j => w0 (g j), hδρ0, hρ0lo, hρ0hi,
      fun j => hw0 (g j), hcov, fun i j j' hj hj' => hg (hsep i (g j) (g j') hj hj')⟩, h19, h20⟩

theorem TwoScaleTheorem.toP {σ : ℝ} (h : TwoScaleTheorem σ) : TwoScaleTheoremP σ := by
  intro ε hε
  obtain ⟨η, d0, hη, hd0, H⟩ := h ε hε
  refine ⟨η, d0, hη, hd0, ?_⟩
  intro δ hδ hδd hδ100 n x v Y hF hS hV r hr1 hr2
  obtain ⟨ρc, h1, h2, h3⟩ := H δ hδ hδd hδ100 n x v Y hF hS hV r hr1 hr2
  exact ⟨ρc, h1, h2, h3.toP⟩

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
