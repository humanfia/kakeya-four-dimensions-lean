-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PrismConcentration.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PrismConcentration.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ClearedConcentration
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.WindowIncidenceAssembly
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.IncidenceRebase

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory

noncomputable section

/-- From the original frozen input, either obtain its gain or terminal
state, or construct growing, dense, broad per-incidence prisms at exactly
the old grain length. All carrier, mass, window and common-width data are
constructed from the input. -/
theorem gain_terminal_or_incidence_prisms {σ ω ζ ε : ℝ}
    (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hE : E σ ω) (hζ : 0 < ζ) (hζω : ζ ≤ ω / 1000)
    (hε : 0 < ε) (hεζ : ε ≤ ζ / 100) :
    ∃ α κ θ d₀ : ℝ, 0 < α ∧ 0 < κ ∧ 0 < θ ∧ θ ≤ ε ∧
      0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ h : ℝ, 0 < δ → δ ≤ d₀ → 0 ≤ h → h ≤ θ →
      ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
      A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
      ∀ ρ c, J ω ζ δ h ρ c n x v Y 2 →
      Gain σ ω κ α δ n Y ∨ J ω ζ δ ε ρ c n x v Y 3 ∨
        ∃ ρ', δ ^ (-ζ / 400) * ρ ≤ ρ' ∧
          WangZahlLot.Obl.wz_move_two_dense_broad_prisms.G ω ζ δ ε ρ' c n x v Y 0 := by
  classical
  obtain ⟨β, τ, ξ, b, t, ν, e, Cnet, loss, capLoss, α, κ, θ, dH, p, d,
    hβ, hβ1, hβζ, hτ, hξ, hξε, hξ1, hb, hbξ, ht, htν, hmass,
    hν, hνε, hνζ, he, heε, heζ, hCnet, hloss, hlosse, hνloss, htloss,
    hcapLoss, hcaploss, hα, hκ, hθ, hθε, hdH, hdH1, hp, hd, HH⟩ :=
    gain_terminal_or_cleared_bounded_concentration hσ hσhalf hω hω1 hE hζ hζω
      hε hεζ (1 / 2 ^ 35) 1 (by positivity) le_rfl
  have hβ₂ : 0 < ω * ζ / 100 := by positivity
  have hwidth : ω * ζ / 100 + 3 * (ζ / 400) < ζ / 4 := by
    have hh := mul_le_mul_of_nonneg_right hω1 hζ.le
    nlinarith only [hh, hζ]
  have hlossζ : loss ≤ ζ / 10000000 := by linarith only [hlosse, hεζ]
  obtain ⟨dW, hdW, hdW1, HW⟩ := window_high_net_block_uniform
    (ω := ω) (t := t) (loss := loss) (β₂ := ω * ζ / 100) (q₀ := ζ / 4)
    (jump := ζ / 100) (jump' := ζ / 200) (τ₂ := loss) (widthJump := ζ / 400)
    (s := loss) (h := 4 * loss) (rowExp := 5 * loss) (fillExp := 100 * loss)
    hβ₂ (by positivity) hwidth hloss (by linarith only [hlossζ, hζ])
    (by linarith) hloss.le (by linarith) (by linarith only [htloss, hloss])
    (by linarith only [hlossζ, hζω, hω]) (by linarith only [hζ])
  obtain ⟨dP, hdP, hdP1, HP⟩ := incidence_prisms_of_window_blocks_uniform
    (ω := ω) (ζ := ζ) (ξ := ξ) (e := e) (t := t) (τ₂ := loss)
    (widthJump := ζ / 400) (fillExp := 100 * loss) (h' := ε / 2)
    hβ₂.le hξ.le (by positivity)
    (by linarith only [hξε, heε, htloss, hlosse, hε])
    (by linarith only [hlosse, hε])
  refine ⟨α, κ, θ, min dH (min dW dP), hα, hκ, hθ, hθε, by positivity,
    (min_le_left _ _).trans (hdH1.trans (by norm_num)), ?_⟩
  intro δ h hδ hδ0 hh hhθ n x v Y hA ρ c hJ
  obtain ⟨hδH, hδW, hδP⟩ : δ ≤ dH ∧ δ ≤ dW ∧ δ ≤ dP := by
    simpa only [le_min_iff] using hδ0
  have hδ1 : δ ≤ 1 := hδP.trans hdP1
  rcases HH δ h hδ hδH hh hhθ n x v Y hA ρ c hJ with hgain | hterminal | hdata
  · exact Or.inl hgain
  · exact Or.inr (Or.inl hterminal)
  obtain ⟨Y', hsub, hclear, hretain, hA', hcap, D, F, HF⟩ := hdata
  have hwindows (R : F.blocks) : Nonempty (WindowHighNetBlock (F.angular R) hδ σ Cnet e t ν loss
      (ω * ζ / 100) (ζ / 4) (ζ / 100) loss (ζ / 400) (100 * loss) d) := by
    apply HW δ hδ hδW (Classical.choice (HF R))
    · exact fun i => (hA'.2.1 i).1
    · exact fun i => (D.cover.1 i).2.1.trans (hA'.2.1 i).2.2.2
    · intro i
      simpa only [one_mul] using (hclear i).mono (D.cover.1 i).2.1 Subset.rfl
  obtain ⟨ρ', hgrow, hG⟩ := HP δ hδ hδP D F (fun R => Classical.choice (hwindows R))
    hmass (fun i => (hA'.2.1 i).1) (fun i => (hA'.2.1 i).2.1)
  right; right
  refine ⟨ρ', ?_, incidence_prisms_rebase hδ hδ1 (by positivity : 0 ≤ ε / 8)
    (by linarith : ε / 2 + ε / 8 ≤ ε) hsub hretain hG⟩
  simpa only [neg_div] using hgrow

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
