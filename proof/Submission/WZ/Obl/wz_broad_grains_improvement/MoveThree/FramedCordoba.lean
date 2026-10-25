-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.FramedCordoba.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/FramedCordoba.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641, commit 707550d, FramedCordoba.lean
   (x0670 first-filling chain, building on x0551 geometry). -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.PerTube

noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open scoped ENNReal Classical
open WangZahlLot.Obl.wz_flat_cluster_slab_filling
  (cell pt_log_cells many_cells cordoba_box piece_subset_box pt_final_real box_volume box_measurable)

/-- A frame-preserving form of the slab filling argument. The local crossing
pieces may depend on the stem point; only their geometry and mass are used. -/
theorem framed_cordoba_filling {δ R θ L b κ lam D k₀ k₁ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) (hR : 0 < R) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hκ : 0 ≤ κ) (hD : 0 ≤ D) (hb : b = 32 * R * L)
    (hL3 : 3 * δ ≤ L) (hL : 1 / 2 + δ + L ≤ 1)
    (h₀ : 3 * δ + k₀ * (L + 2 * δ) ≤ 5 * δ)
    (h₁ : 3 * δ + k₁ * (L + 2 * δ) ≤ b / 2)
    (x v : V) (hv : ‖v‖ = 1) (g : V ≃ₗᵢ[ℝ] V)
    (hg : ∀ p, g p 2 = inner ℝ v p)
    (Z U : Set V) (hZm : MeasurableSet Z) (hZT : Z ⊆ T δ x v)
    (hUm : MeasurableSet U) (hmass : O (lam * δ ^ 2) ≤ volume Z)
    (hpieces : ∀ p ∈ Z, ∃ (y w : V) (A : Set V), ‖w‖ = 1 ∧
      p ∈ T δ y w ∧ θ / 2 ≤ |g w 1| ∧ |g w 0| ≤ k₀ ∧ |g w 1| ≤ k₁ ∧
      MeasurableSet A ∧ A ⊆ T δ y w ∩ ball p L ∧ A ⊆ U ∧
      O (κ * (L * δ ^ 2 / 8)) ≤ volume A)
    (hnum : D * (10 ^ 13 * (R / θ) * (1 + Real.log (1 / δ))) ≤ κ ^ 2 * lam) :
    O D * volume (P (10 * δ) b 2 (x + (1 / 2 : ℝ) • v) g) ≤
      volume (P (10 * δ) b 2 (x + (1 / 2 : ℝ) • v) g ∩ U) := by
  have hLpos : 0 < L := by linarith
  let step := 32 * δ / θ
  let m : ℕ := ⌈(1 + 2 * δ) / step⌉₊
  let active := Finset.univ.filter fun j : Fin m => (Z ∩ cell δ step x v j).Nonempty
  have hstep : 0 < step := by dsimp [step]; positivity
  obtain ⟨hcover, hlog⟩ := pt_log_cells hδ hδ1 hθ hθ1 (rfl : step = 32 * δ / θ)
  have hcount := many_cells hδ hv hstep Z hZm hZT hmass m hcover
  change lam * δ ^ 2 ≤ 128 * (2 * (step + 2 * δ) + δ) * δ ^ 2 * (active.card : ℝ) at hcount
  have hchoose : ∀ j ∈ active, ∃ p, p ∈ Z ∧ p ∈ cell δ step x v j := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  choose! points hpZ hpCell using hchoose
  choose! starts dirs pieces hdUnit hpTube hdCross hd₀ hd₁ hmPiece hPieceTube hPieceU hPieceMass using hpieces
  let box := P (10 * δ) b 2 (x + (1 / 2 : ℝ) • v) g
  let E := box ∩ U
  have hvol : volume box = O (10 * δ * b * 2) :=
    box_volume (by positivity) (by rw [hb]; positivity) (by norm_num) _ _
  have hEmeas : MeasurableSet E := (box_measurable _ _ _ _ _).inter hUm
  have hEfin : volume E ≠ ⊤ := ne_top_of_le_ne_top
    (hvol ▸ ENNReal.ofReal_ne_top) (measure_mono Set.inter_subset_left)
  have hpointStem (j) (hj : j ∈ active) : points j ∈ T δ x v := hZT (hpZ j hj)
  have hpieceE (j) (hj : j ∈ active) : pieces (points j) ⊆ E := by
    intro q hq
    refine ⟨?_, hPieceU _ (hpZ j hj) hq⟩
    apply piece_subset_box hδ hv (hdUnit _ (hpZ j hj)) hg (hpointStem j hj)
      (hpTube _ (hpZ j hj)) (hd₀ _ (hpZ j hj)) (hd₁ _ (hpZ j hj)) h₀ h₁ hL
    exact hPieceTube _ (hpZ j hj) hq
  let directions := fun j : Fin m => if j ∈ active then dirs (points j) else v
  have hcor := cordoba_box hδ (by linarith : δ ≤ 1) hθ hθ1 (by linarith : 2 * δ ≤ L)
    (rfl : step = 32 * δ / θ) (by positivity : 0 ≤ κ * (L * δ ^ 2 / 8)) hv hg active points
    (starts ∘ points) directions (pieces ∘ points)
    (by intro j; by_cases hj : j ∈ active
        · simpa [directions, hj] using hdUnit _ (hpZ j hj)
        · simpa [directions, hj] using hv)
    hpointStem hpCell
    (by intro j hj; simpa [directions, hj] using hpTube _ (hpZ j hj))
    (by intro j hj; simpa [directions, hj] using hdCross _ (hpZ j hj))
    (fun j hj => hmPiece _ (hpZ j hj))
    (by intro j hj; simpa [directions, hj] using hPieceTube _ (hpZ j hj))
    (fun j hj => hPieceMass _ (hpZ j hj))
    E hEmeas hEfin hpieceE
  have hlogpos : 1 ≤ 1 + Real.log (1 / δ) := by
    have hh : (1 : ℝ) ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by linarith)
    linarith [Real.log_nonneg hh]
  have hreal := pt_final_real hδ hR hθ hθ1 (by linarith : 0 < L) hD hlogpos
    (by linarith : 1 + Real.log m ≤ 1 + Real.log (1 / δ))
    (Nat.cast_nonneg active.card) ENNReal.toReal_nonneg (rfl : step = 32 * δ / θ)
    hb hcount hcor hnum
  rw [hvol, ← ENNReal.ofReal_mul hD]
  exact (ENNReal.ofReal_le_iff_le_toReal hEfin).mpr hreal

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
