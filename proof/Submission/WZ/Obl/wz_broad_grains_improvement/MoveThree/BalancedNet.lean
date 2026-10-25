-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.BalancedNet.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/BalancedNet.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641 commit 7652d3d, BalancedNet.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_transverse_cell_weighted_cover.Net
import Submission.WZ.Obl.wz_weighted_affine_packet_balancing.Refinement

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open MeasureTheory Set Metric
open scoped ENNReal

/-- A separated carrier net with equal, disjoint fibres. The representatives remain
in the original family, so their individual density can also be retained. -/
theorem balanced_prism_net {n d : ℕ} (I : Finset (Fin n)) (hI : I.Nonempty)
    {a b R : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b)
    (hbsmall : b ≤ 1 / 1000000) (hd : 0 < d) (hR : 1 < R)
    (hn : (n : ℝ) < R ^ d) (c : Fin n → V) (u : Fin n → Fin 3 → V)
    (hu : ∀ i ∈ I, Orthonormal ℝ (u i)) (hc : ∀ i ∈ I, ‖c i‖ < 1 / 100) :
    ∃ (N q : ℕ) (k : Fin N → Fin n) (F : Fin N → Finset (Fin n)),
      0 < N ∧ 0 < q ∧ (∀ j, k j ∈ I) ∧ (∀ j, F j ⊆ I) ∧
      (∀ j, (F j).card = q) ∧ (∀ j j', j ≠ j' → Disjoint (F j) (F j')) ∧
      WangZahlLot.Obl.wz_transverse_cell_weighted_cover.netConst * (I.card : ℝ) ≤ (d : ℝ) * R * N * q ∧
      (∀ j, ∀ i ∈ F j,
        WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism a b (c i) (u i) ⊆ WangZahlLot.Obl.wz_transverse_cell_weighted_cover.cTube b (c (k j)) (u (k j))) ∧
      (∀ j j', j ≠ j' → μ (WangZahlLot.Obl.wz_transverse_cell_weighted_cover.cTube b (c (k j)) (u (k j)) ∩
          WangZahlLot.Obl.wz_transverse_cell_weighted_cover.cTube b (c (k j')) (u (k j'))) ≤
        (1 / 2 : ℝ≥0∞) * μ (WangZahlLot.Obl.wz_transverse_cell_weighted_cover.cTube b (c (k j)) (u (k j)))) := by
  obtain ⟨M, k₀, F₀, hM, hk₀, hF₀, hne, hdisj, hmass, hcover, hX⟩ :=
    WangZahlLot.Obl.wz_transverse_cell_weighted_cover.net_cover I hI ha hab hb hbsmall c u hu hc
  obtain ⟨N, q, v, F, hN, hq, hv, hF, hcard, hdisj', hmass'⟩ :=
    WangZahlLot.Obl.wz_weighted_affine_packet_balancing.balanced_fibers
      hM hd F₀ hne hdisj hR hn
  refine ⟨N, q, k₀ ∘ v, F, hN, hq, fun j => hk₀ (v j),
    fun j => (hF j).trans (hF₀ (v j)), hcard, hdisj', hmass.trans hmass', ?_, ?_⟩
  · exact fun j i hi => hcover (v j) i (hF j hi)
  · exact fun j j' hjj' => hX (v j) (v j') (fun h => hjj' (hv h))

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
