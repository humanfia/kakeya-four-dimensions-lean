-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.FramedFilling.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/FramedFilling.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641, commit 707550d, FramedFilling.lean
   (x0670 first-filling chain, building on x0551 geometry). -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FramedCordoba

noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open scoped ENNReal Classical
open WangZahlLot.Obl.wz_flat_cluster_slab_filling
  (slab_inner_dir frame_coord_le_angle inplane_large tube_ball_volume_lower)

/-- Slab filling in any specified adapted frame, retaining its alignment data. -/
theorem slab_filling_in_frame {n : ℕ} {δ R b L θ κ lam D r t : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) (hR : 0 < R) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hκ : 0 ≤ κ) (hD : 0 ≤ D) (hb : b = 32 * R * L)
    (hL3 : 3 * δ ≤ L) (hL : 1 / 2 + δ + L ≤ 1)
    (hrθ : 32 * r ≤ θ) (hrL : 3 * δ + 8 * r * (L + 2 * δ) ≤ 5 * δ)
    (hRL : 3 * δ + 8 * R * (L + 2 * δ) ≤ b / 2)
    (x v : Fin n → V) (Y Z : Fin n → Set V) (hv : ∀ i, ‖v i‖ = 1)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYT : ∀ i, Y i ⊆ T δ (x i) (v i))
    (hZm : ∀ i, MeasurableSet (Z i)) (hZY : ∀ i, Z i ⊆ Y i)
    (i : Fin n) (u : V) (g : V ≃ₗᵢ[ℝ] V)
    (hg₂ : ∀ p, g p 2 = inner ℝ (v i) p)
    (hg₀ : ∀ w, |g w 0| ≤ 2 * (|inner ℝ u w| + |inner ℝ u (v i)| * ‖w‖))
    (hstem : T δ (x i) (v i) ⊆ {p | |inner ℝ u p - t| ≤ r})
    (W : Set V) (hWm : MeasurableSet W) (hWT : W ⊆ T δ (x i) (v i))
    (hWmass : O (lam * δ ^ 2) ≤ volume W)
    (hcross : ∀ p ∈ W, ∃ j, p ∈ Z j ∧
      T δ (x j) (v j) ⊆ {q | |inner ℝ u q - t| ≤ r} ∧
      θ < min ‖v j - v i‖ ‖v j + v i‖ ∧ min ‖v j - v i‖ ‖v j + v i‖ ≤ 8 * R ∧
      O κ * volume (T δ (x j) (v j) ∩ ball p L) ≤ volume (Z j ∩ ball p L))
    (hnum : D * (10 ^ 13 * (R / θ) * (1 + Real.log (1 / δ))) ≤ κ ^ 2 * lam) :
    O D * volume (P (10 * δ) b 2 (x i + (1 / 2 : ℝ) • v i) g) ≤
      volume (P (10 * δ) b 2 (x i + (1 / 2 : ℝ) • v i) g ∩ ⋃ j, Y j) := by
  apply framed_cordoba_filling hδ hδ1 hR hθ hθ1 hκ hD hb hL3 hL hrL hRL
    (x i) (v i) (hv i) g hg₂ W (⋃ j, Y j) hWm hWT (MeasurableSet.iUnion hYm) hWmass ?_ hnum
  intro p hp
  obtain ⟨j, hpj, hslab, hanglo, hanghi, hregular⟩ := hcross p hp
  have hdir₀ : |g (v j) 0| ≤ 8 * r := by
    have h := hg₀ (v j)
    rw [hv j] at h
    linarith [slab_inner_dir hδ hstem, slab_inner_dir hδ hslab]
  have hdir₁ : |g (v j) 1| ≤ 8 * R :=
    (frame_coord_le_angle (hv i) hg₂ (v j) 1 (by decide)).trans hanghi
  have hdirlower : θ / 2 ≤ |g (v j) 1| :=
    inplane_large (hv i) (hv j) hg₂ hθ.le hanglo (by linarith)
  have hpT : p ∈ T δ (x j) (v j) := hYT j (hZY j hpj)
  refine ⟨x j, v j, Z j ∩ ball p L, hv j, hpT, hdirlower, hdir₀, hdir₁,
    (hZm j).inter measurableSet_ball, Set.inter_subset_inter_left _ ((hZY j).trans (hYT j)),
    (fun q hq => mem_iUnion.mpr ⟨j, hZY j hq.1⟩), ?_⟩
  calc
    O (κ * (L * δ ^ 2 / 8)) = O κ * O (L * δ ^ 2 / 8) := ENNReal.ofReal_mul hκ
    _ ≤ O κ * volume (T δ (x j) (v j) ∩ ball p L) :=
      mul_le_mul' le_rfl (tube_ball_volume_lower hδ (hv j) hL3 (by linarith) hpT)
    _ ≤ volume (Z j ∩ ball p L) := hregular

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
