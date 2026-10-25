-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.BlockNets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/BlockNets.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BlockNetData
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BlockNetParameters

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric

noncomputable section

/-- Apply the simultaneous net estimate to all actual filled labels of a
block, with no separate saturation assumption on its labels. -/
theorem block_filling_balanced_nets {σ ω : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 < ω) (hE : E σ ω) :
    ∀ e : ℝ, 0 < e → ∃ Cnet η d₀ : ℝ,
      0 < Cnet ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 4096 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ Kc : ℝ, 1 ≤ Kc →
      ∀ {ζ ε b ρ c β τ lam den k : ℝ} {p n : ℕ} {x v : Fin n → V}
        {Y : Fin n → Set V} (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
        (R : Finset (Fin D.L)), R.Nonempty → ∀ G : D.NormalizedBlock R,
      ∀ (A : BlockAngularData D R G β τ) {hk : 0 < k}
        (F : BlockFirstFilling A lam den k hk) (d : ℕ) (Λ : ℝ),
      ε ≤ 1 → WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.A δ (ε / 4) (δ ^ (-(ε / 4))) (δ ^ (-(ε / 4))) n x v Y →
      0 < lam → 0 < d → 1 < Λ → (R.card : ℝ) < Λ ^ d →
      4 * δ ≤ F.radius → 6144 * δ ^ η ≤ den * k / 16000 →
      Nonempty (BlockNetData (σ := σ) F Cnet e Λ Kc d) := by
  intro e he
  obtain ⟨Cnet, η, d₁, hC, hη, hd₁, _, H⟩ := filled_packet_balanced_nets hσ hσhalf hω hE e he
  refine ⟨Cnet, η, min d₁ (1 / 4096), hC, hη, by positivity, min_le_right _ _, ?_⟩
  intro δ hδ hδd Kc hKc ζ ε b ρ c β τ lam den k p n x v Y D R hR G A hk F d Λ
    hε hA hlam hd hΛ hnΛ hδB hden
  have hρ := (D.dimensions hδ).2.1
  have hM : 0 < grainCoefficient D.a ρ c D.z D.e D.Q :=
    (Real.rpow_pos_of_pos hδ (-ζ)).trans D.large
  obtain ⟨N, q, rep, Fib, hnet, hlow⟩ := H δ hδ (hδd.trans (min_le_left _ _)) Kc hKc
    F.good R.card d F.indices (D.normalizedBody R G.affine) A.start A.axis A.normalizedPiece
    F.map F.direction (2 * ρ) F.radius Λ (ρ ^ 2 / 64)
    (grainCoefficient D.a ρ c D.z D.e D.Q) (den * k / 16000) F.volumeFactor
    (D.block_cardinality_at_base hδ (hδd.trans (min_le_right _ _)) hε hA R)
    hd hΛ hnΛ hδB (F.radius_small hδ hR hlam) (by positivity) hM
    (F.volumeFactor_pos hδ hR) hden G.convex_count A.tubes
    (by
      intro l hl
      refine ⟨(F.filling l hl).1, A.normalizedPiece_measurable l, F.map_volume l, ?_⟩
      intro i hi
      exact ((F.filling l hl).2.2.2 i hi).2)
  exact ⟨{ N := N, size := q, representative := rep, fibre := Fib, net := hnet, low_sum := hlow }⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
