-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.ThickThin.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/ThickThin.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Mono
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Statement
import Submission.WZ.Obl.wz_move_three_thick_grains_gain.ThickGrains

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

noncomputable section

/-- The accepted thick-grain estimate reduces every frozen stage to grains
whose short side is below the chosen power scale. -/
theorem gain_or_thin_state {σ ω b : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 < ω) (hE : E σ ω) (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃ κ θ d₀ : ℝ, 0 < κ ∧ 0 < θ ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ h : ℝ, 0 < δ → δ ≤ d₀ → 0 ≤ h → h ≤ θ →
      ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
      A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
      ∀ (ζ ρ c : ℝ) (j : ℕ), J ω ζ δ h ρ c n x v Y j →
      Gain σ ω κ (b * ω / 2) δ n Y ∨ Jt ω ζ δ h ρ c b n x v Y j := by
  obtain ⟨κ, θ, d₀, hκ, hθ, hd₀, hd₀small, HG⟩ :=
    WangZahlLot.Obl.wz_move_three_thick_grains_gain.thick_grains_gain hσ hσhalf hω hE hb hb1
  refine ⟨κ, θ, d₀, hκ, hθ, hd₀, hd₀small, ?_⟩
  intro δ h hδ hδsmall hh hhθ n x v Y hA ζ ρ c j hJ
  obtain ⟨S, Z, N, y, w, f, a, g, hC, hρ, hg, hB, hH, hstop⟩ := J_iff.mp hJ
  by_cases hthin : a < 2 * δ ^ (1 - b)
  · exact Or.inr (Jt_iff.mpr ⟨S, Z, N, y, w, f, a, g, hC, hρ, hg, hB, hH, hthin, hstop⟩)
  · exact Or.inl (HG δ h hδ hδsmall hh hhθ n x v Y hA
      S Z ρ N y w f True hC a c 0 g hH (le_of_not_gt hthin))

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
