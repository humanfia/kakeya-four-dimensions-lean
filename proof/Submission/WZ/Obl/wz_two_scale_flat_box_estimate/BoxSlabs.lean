-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.BoxSlabs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.SlabComposition
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.SlabTransport
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.ConvexComposition
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxNormalization
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.DoubledBodies
import Submission.WZ.Obl.wz_flat_factored_improvement.FlatBodies

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_flat_factored_improvement
  (BodySlabCount BodyConvexCount ConvexVolumeCount flatMap flatMap_volume flatMap_dist_lower)
open WangZahlLot.Obl.wz_regular_transverse_affine_cells
  (closedTube tube_subset_closedTube ball_subset_tube volume_closedTube)

set_option maxHeartbeats 800000 in
/-- Fine slab counting after flattening a box, obtained from the two different
counting assumptions in the frozen statement. -/
theorem box_slab_composition {δ ρ a b c L H F Q : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1 / 2)
    (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (ha2 : a ≤ 2) (hc : 1 ≤ c)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hF : 0 ≤ F) (hQ : 0 ≤ Q)
    {n N : ℕ} (x v : Fin n → Space) (y w : Fin N → Space) (f : Fin n → Fin N)
    (z : Space) (e : Space ≃ₗᵢ[ℝ] Space)
    (hw : ∀ k, ‖w k‖ = 1)
    (hcontain : ∀ i, Tube δ (x i) (v i) ⊆ Tube ρ (y (f i)) (w (f i)))
    (hbox : ∀ k, Tube ρ (y k) (w k) ⊆ Box a b c z e)
    (hmeet : ∀ k, (Tube ρ (y k) (w k) ∩ ball (0 : Space) 1).Nonempty)
    (hraw : ∀ W, Convex ℝ W →
      ENNReal.ofReal (Set.ncard {k | Tube ρ (y k) (w k) ⊆ W} : ℝ) ≤
        ENNReal.ofReal (H * N / (a * b * c)) * volume W)
    (hbelow : ∀ k (u : Space) (s r : ℝ), ‖u‖ = 1 → 0 < r →
      ENNReal.ofReal (Set.ncard {i | f i = k ∧ Tube δ (x i) (v i) ⊆
        {p | |inner ℝ u p - s| ≤ r}} : ℝ) *
        volume (Tube (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k)) ≤
      ENNReal.ofReal (L * F) * volume
        (Tube (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k) ∩
          {p | |inner ℝ u p - s| ≤ r}))
    (hbalance : F * N ≤ Q * n)
    (K : ℕ) (hK : (1 / 2 : ℝ) ^ K ≤ δ / 16) :
    BodySlabCount (fun i => flatMap (normalFrame b z e) a (min b 2) ha
      (lt_min hb (by norm_num)) '' closedTube δ (x i) (v i))
      (L * Q * (384 + 1280 * K * (49152 * H))) := by
  let A := flatMap (normalFrame b z e) a (min b 2) ha (lt_min hb (by norm_num))
  let J := 1 / (128 * a * min b 2)
  let D₀ := fun k => Tube (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k)
  let D := fun k => A '' closure (D₀ k)
  let U := fun i => A '' closedTube δ (x i) (v i)
  let W := J * (8 * ρ ^ 2)
  let R := H * N / (a * b * c)
  let m := 384 * (R * (8 * ρ ^ 2))
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  have hbmin : 0 < min b 2 := lt_min hb (by norm_num)
  have hJ : 0 < J := by dsimp [J]; positivity
  have hW : 0 < W := by dsimp [W]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hvol : ∀ S, volume (A '' S) = ENNReal.ofReal J * volume S :=
    flatMap_volume _ ha hbmin
  have hTD (k : Fin N) : Tube ρ (y k) (w k) ⊆ closure (D₀ k) :=
    (tube_subset_doubled hρ _ _).trans subset_closure
  have hDc : ∀ k, IsCompact (D k) := fun k =>
    (doubled_closed_compact _ _ _).image A.toContinuousAffineEquiv.continuous
  have hDconv : ∀ k, Convex ℝ (D k) := fun k =>
    (doubled_closed_convex _ _ _).affine_image A.toAffineMap
  have hDb : ∀ k, D k ⊆ closedBall (0 : Space) 1 := by
    intro k
    apply (image_mono (show closure (D₀ k) ⊆
      Box (3 * a) (3 * b) (3 * c) z e ∩ closedBall (0 : Space) 4 from
      fun p hp => ⟨doubled_closed_subset_triple_box hρ _ _ _ _ (hbox k) hp,
        doubled_closed_unit_bound hρhalf _ _ (hw k) (hmeet k) hp⟩)).trans
    exact flatMap_triple_box_bounded ha hb z e
  have hDV (k : Fin N) : ENNReal.ofReal W ≤ volume (D k) ∧
      volume (D k) ≤ ENNReal.ofReal (384 * W) := by
    obtain ⟨hl, hu⟩ := doubled_closed_volume_bounds hρ (hρhalf.trans (by norm_num)) (y k) (w k) (hw k)
    change ENNReal.ofReal W ≤ volume (A '' _) ∧ _
    rw [hvol]
    constructor
    · rw [show W = J * (8 * ρ ^ 2) from rfl, ENNReal.ofReal_mul hJ.le]
      exact mul_le_mul' le_rfl hl
    · calc
        _ ≤ ENNReal.ofReal J * ENNReal.ofReal (3072 * ρ ^ 2) := mul_le_mul' le_rfl hu
        _ = _ := by rw [← ENNReal.ofReal_mul hJ.le]; congr 1; dsimp [W]; ring
  have hconv : BodyConvexCount D W (R * (8 * ρ ^ 2)) :=
    (raw_convex_count_enlarge (fun k => Tube ρ (y k) (w k)) (fun k => closure (D₀ k))
      hR (by positivity) hTD hraw).affine_image (by positivity) hJ A hvol
  have hcount : ConvexVolumeCount D m :=
    hconv.volume_weighted (by norm_num : (0 : ℝ) ≤ 384) (by positivity) (fun k => (hDV k).2)
  have hcoef : m ≤ (49152 * H) * N * W := by
    have hbc : min b 2 ≤ b * c :=
      (min_le_left _ _).trans (by nlinarith)
    have hden : a * min b 2 ≤ a * b * c := by nlinarith
    calc
      m = (3072 * (H * N) * ρ ^ 2) / (a * b * c) := by dsimp [m, R]; ring
      _ ≤ (3072 * (H * N) * ρ ^ 2) / (a * min b 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = _ := by dsimp [W, J]; field_simp; ring
  have hinterior : ∀ i, ball (A (x i)) (δ / 8) ⊆ U i := by
    intro i p hp
    refine ⟨A.symm p, ?_, A.apply_symm_apply p⟩
    apply tube_subset_closedTube
    apply ball_subset_tube
    have hh := flatMap_dist_lower (normalFrame b z e) ha hbmin
      (le_min hab ha2) (min_le_right _ _) (A.symm p) (x i)
    change dist (A.symm p) (x i) / 8 ≤ dist (A (A.symm p)) (A (x i)) at hh
    rw [A.apply_symm_apply] at hh
    exact mem_ball.mpr (by have hp' := mem_ball.mp hp; linarith)
  have hlocal : ∀ (u : Space) (s r : ℝ), ‖u‖ = 1 → 0 < r → ∀ k,
      ENNReal.ofReal (Set.ncard {i | f i = k ∧ U i ⊆
        WangZahlLot.Obl.wz_regular_transverse_affine_cells.slab (innerSL ℝ u) s r} : ℝ) * volume (D k) ≤
      ENNReal.ofReal (L * F) * volume (D k ∩
        WangZahlLot.Obl.wz_regular_transverse_affine_cells.slab (innerSL ℝ u) s r) := by
    intro u s r hu hr k
    have hh := fixed_slab_affine_enlargement (hbelow k) (fun i : Fin n => i) Function.injective_id
      (fun _ hi => hi) (fun i => tube_subset_closedTube δ (x i) (v i))
      subset_closure (volume_closedTube _ _ _) A hvol u s r hu hr
    exact hh
  exact bodySlabCount_of_two_scale U (fun i => A (x i)) D f
    (by positivity : 0 < δ / 8) hW hL hF (by norm_num) hm (by positivity) hQ hinterior
    hDc hDconv hDb (fun k => (hDV k).1) (fun k => (hDV k).2) hcount hcoef hbalance hlocal K
    (by convert hK using 1 <;> ring)

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
