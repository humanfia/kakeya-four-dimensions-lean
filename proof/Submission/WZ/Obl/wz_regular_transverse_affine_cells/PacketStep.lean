-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.PacketStep.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.RefineSlab
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.CountedSlabs
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.FiniteRefinement

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open Module MeasureTheory Set Metric
open scoped ENNReal

lemma PreparedPacket.jacobian_bounds {n K : ℕ} {C : PhysicalPacket n} {δ S : ℝ}
    {x v : Fin n → E} (A : PreparedPacket (K := K) C δ S x v) (hS : 2 ≤ S)
    (hCbound : C.region ⊆ closedBall (0 : E) 1) :
    δ ^ 3 ≤ A.cell.jacobian ∧ A.cell.jacobian ≤ 512 * S ^ 3 := by
  have hSpos : 0 < S := by linarith
  constructor
  · apply A.jacobian_lower.trans
    apply mul_le_of_le_one_right A.jacobian_pos.le
    apply pow_le_one₀ (by positivity)
    rw [div_le_one hSpos]
    exact hS
  · have hU : volume C.region ≤ 8 := (measure_mono hCbound).trans volume_unit_closedBall_upper
    have h := A.jacobian_volume.trans (mul_le_mul_right hU _)
    rw [← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_mul (by positivity)] at h
    have h' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
    nlinarith

set_option maxHeartbeats 800000 in
/-- One complete physical refinement step, with all losses expressed by the two
parameters `d` and `lambda`. -/
lemma physical_packet_step {n K : ℕ} {C : PhysicalPacket n} {δ d S h t θ κ τ : ℝ}
    {x v : Fin n → E} {Y : Fin n → Set E} (hC : C.Valid δ d x v Y)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hSlarge : 1000000000 ≤ S)
    (hv : ∀ i, ‖v i‖ = 1) (htube : ∀ i, tube δ (x i) (v i) ⊆ ball (0 : E) 1)
    (hK : (1 / 2 : ℝ) ^ K < δ / (6 * S))
    (hbottom : (1 / 2 : ℝ) ^ K * (384 * (n : ℝ)) ≤ 1)
    (hd : 0 < d) (hd1 : d ≤ 1) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hτsmall : 3072 * τ ≤ 1)
    (hτbudget : 8 * (1000000 * (K + 1 : ℕ)) * (400000 * S) * 384 * τ ≤ 1)
    (hτshape : τ * (K + 1 : ℕ) ^ 2 ≤ 1)
    (hτslab : 768 * (1 + 320 * K : ℝ) * τ ≤ 1)
    (hh : 0 < h) (ht : 0 < t) (hθ : 0 < θ)
    (htq : t * (d * τ) ≤ 1) (hhq : h ≤ d * τ) (hhθ : h ≤ θ)
    (hslack : h * 6144 ≤ t * (d * τ))
    (hshrink : 2048 * S * t ≤ κ) (hθt : 9 * θ ≤ t)
    (hshape : δ ^ (100 : ℕ) ≤ δ / (12 * S)) (hhsmall : h ≤ 1 / (12 * S))
    (hDlower : δ ^ (100 : ℕ) ≤ δ ^ 3) (hDupper : 512 * S ^ 3 ≤ δ ^ (-100 : ℝ)) :
    ∃ L : List (PacketOutcome n K),
      (∀ z ∈ L, z.Valid δ (d * τ) h κ C x v Y ∧ z.support ⊆ C.support) ∧
      L.Pairwise (fun z z' => Disjoint z.support z'.support) ∧
      (d ^ 2 * τ ^ 3) * (C.indices.card : ℝ) ≤ (L.map PacketOutcome.weight).sum := by
  classical
  have hS : 0 < S := by linarith
  obtain ⟨A⟩ := prepare_packet hC hδ hSlarge hK hv htube
  let U := fun i => A.cell.affine ⁻¹' closedTube δ (x i) (v i)
  let w : ℝ := δ ^ 2 / A.cell.jacobian
  have hw : 0 < w := div_pos (sq_pos_of_pos hδ) A.jacobian_pos
  have hUc : ∀ i, IsCompact (U i) := fun i =>
    A.cell.affine.toContinuousAffineEquiv.toHomeomorph.isCompact_preimage.mpr (closedTube_compact (htube i))
  have hUconv : ∀ i, Convex ℝ (U i) := fun i =>
    (closedTube_convex _ _ _).affine_preimage A.cell.affine.toAffineMap
  have hweights : ∀ i, w ≤ (volume (U i)).toReal ∧ (volume (U i)).toReal ≤ 384 * w := fun i =>
    affine_preimage_weights A.cell.affine A.jacobian_pos A.volume_identity (closedTube_compact (htube i))
      (sq_nonneg _) (by norm_num) (closedTube_volume_bounds hδ hδ1 (x i) (v i) (hv i))
  have hUiA : ∀ i ∈ A.cell.indices, U i ⊆ closedBall (0 : E) 1 := by
    intro i hi
    apply ((preimage_mono (hC.2.2.2.2.1 i (A.indices_subset hi))).trans A.small).trans
    apply closedBall_subset_closedBall
    rw [div_le_one hS]
    linarith
  have hballs : ∀ i, ∃ p, ball p (δ / (6 * S)) ⊆ U i := by
    intro i
    refine ⟨A.cell.affine.symm (x i), ?_⟩
    exact (ball_subset_affine_preimage A.cell.affine (by positivity : 0 < 6 * S)
      A.lipschitz (x i)).trans (preimage_mono ((ball_subset_tube (x i) (v i)).trans (tube_subset_closedTube _ _ _)))
  have hAm : ∀ i ∈ A.cell.indices, MeasurableSet (A.cell.shading i) := by
    intro i hi
    rw [A.shading_eq]
    exact (hC.2.2.2.2.2.1 i (A.indices_subset hi)).preimage
      A.cell.affine.toContinuousAffineEquiv.continuous.measurable
  have hAU : ∀ i ∈ A.cell.indices, A.cell.shading i ⊆ U i := by
    intro i hi
    rw [A.shading_eq]
    exact preimage_mono (hC.2.2.2.2.2.2.2.1 i (A.indices_subset hi))
  have hAd : ∀ i ∈ A.cell.indices, ENNReal.ofReal d * volume (U i) ≤ volume (A.cell.shading i) := by
    intro i hi
    rw [A.shading_eq]
    exact affine_preimage_density A.cell.affine A.jacobian_pos A.volume_identity _
      (hC.2.2.2.2.2.2.2.2 i (A.indices_subset hi))
  have hAbottom : (1 / 2 : ℝ) ^ K * (384 * (A.cell.indices.card : ℝ)) ≤ 1 := by
    apply le_trans _ hbottom
    have hc : (A.cell.indices.card : ℝ) ≤ n := by
      exact_mod_cast (show A.cell.indices.card ≤ n by simpa using Finset.card_le_univ A.cell.indices)
    gcongr
  obtain ⟨m, B, hB, hBdisj, hBcount⟩ := counted_slab_extraction A.cell.indices U A.cell.shading
    (fun i _ => hUc i) (fun i _ => hUconv i) (by positivity : 0 < δ / (6 * S)) hw
    (by norm_num : (0 : ℝ) < 384) hd.le (fun i _ => hballs i) hUiA
    (fun i _ => hweights i) K hAbottom hAm hAU hAd
  let L₀ := List.ofFn B
  let support := fun Z : ShadedCell (Fin n) => A.cell.affine '' Z.support
  have hLdisj : L₀.Pairwise (fun Z Z' => Disjoint (support Z) (support Z')) := by
    apply List.pairwise_ofFn.mpr
    intro j k hjk
    exact (disjoint_image_iff A.cell.affine.injective).mpr (hBdisj (ne_of_lt hjk))
  have hq1 : d * τ ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left hτ1 hd.le]
  have hqsmall : 3072 * (d * τ) ≤ d := by nlinarith [mul_le_mul_of_nonneg_left hτsmall hd.le]
  have hbudget : 8 * (1000000 * (K + 1 : ℕ) * (d * τ)) * (400000 * S) * 384 ≤ d := by
    nlinarith [mul_le_mul_of_nonneg_left hτbudget hd.le]
  have hK' : (1 / 2 : ℝ) ^ K < 2 * A.cell.a := by
    calc (1 / 2 : ℝ) ^ K < δ / (6 * S) := hK
      _ = 2 * (δ / (12 * S)) := by ring
      _ ≤ _ := by gcongr; exact A.short_lower
  have hD := A.jacobian_bounds (by linarith : 2 ≤ S) hC.2.2.2.1
  have hb : δ * h ≤ A.cell.b := by
    calc δ * h ≤ δ * (1 / (12 * S)) := by gcongr
      _ = δ / (12 * S) := by ring
      _ ≤ A.cell.a := A.short_lower
      _ ≤ A.cell.b := A.ordered
  have hrefine : ∀ Z ∈ L₀, ∃ L : List (PacketOutcome n K),
      (∀ z ∈ L, z.Valid δ (d * τ) h κ C x v Y ∧ z.support ⊆ support Z) ∧
      L.Pairwise (fun z z' => Disjoint z.support z'.support) ∧
      (d * τ) * (Z.indices.card : ℝ) ≤ (L.map PacketOutcome.weight).sum := by
    intro Z hZ
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hZ
    obtain ⟨hBI, hBA, ⟨S₀, hS₀, hS₀w, hmax⟩, hwhole, hZm, hZA, hZd⟩ := hB j
    apply refine_selected_slab hC A hS (B j).indices hBI hBA (B j).shading hZm hZA hZd S₀
      (fun i hi => by simpa only [hS₀] using hwhole i hi) hmax
      (fun i _ => hweights i) (fun i _ => (hUc i).measure_ne_top)
      hd hh ht (mul_pos hd hτ) hw hθ hq1 hqsmall hbudget hK' htq hhq hhθ hslack hshrink hθt
      (hshape.trans A.short_lower) hb ⟨hDlower.trans hD.1, hD.2.trans hDupper⟩
  obtain ⟨L, hL, hLpair, hLmass⟩ := refine_finite_list L₀ support PacketOutcome.support
    (fun Z => (Z.indices.card : ℝ)) PacketOutcome.weight
    (fun z => z.Valid δ (d * τ) h κ C x v Y) (d * τ) hLdisj hrefine
  have hsupport : ∀ Z ∈ L₀, support Z ⊆ C.support := by
    intro Z hZ
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hZ
    rintro p ⟨z, hz, rfl⟩
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz
    have hAi := (hB j).2.1 hi
    have hpi := (hB j).2.2.2.2.2.1 i hi hzi
    rw [A.shading_eq i] at hpi
    exact mem_iUnion₂.mpr ⟨i, A.indices_subset hAi, hpi⟩
  refine ⟨L, ?_, hLpair, ?_⟩
  · intro z hz
    obtain ⟨hvalid, Z, hZ, hsub⟩ := hL z hz
    exact ⟨hvalid, hsub.trans (hsupport Z hZ)⟩
  have hshapeRet : τ * (C.indices.card : ℝ) ≤ A.cell.indices.card := by
    calc τ * (C.indices.card : ℝ) ≤ τ * ((K + 1 : ℕ) ^ 2 * (A.cell.indices.card : ℝ)) :=
        mul_le_mul_of_nonneg_left A.retained hτ.le
      _ = (τ * (K + 1 : ℕ) ^ 2) * (A.cell.indices.card : ℝ) := by ring
      _ ≤ 1 * (A.cell.indices.card : ℝ) := mul_le_mul_of_nonneg_right hτshape (Nat.cast_nonneg _)
      _ = _ := one_mul _
  have hslabRet : (d * τ) * (A.cell.indices.card : ℝ) ≤ ∑ j, ((B j).indices.card : ℝ) := by
    have hsum : (0 : ℝ) ≤ ∑ j, ((B j).indices.card : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    calc (d * τ) * (A.cell.indices.card : ℝ) = τ * (d * (A.cell.indices.card : ℝ)) := by ring
      _ ≤ τ * (2 * (1 + 320 * K : ℝ) * 384 * ∑ j, ((B j).indices.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hBcount hτ.le
      _ = (768 * (1 + 320 * K : ℝ) * τ) * ∑ j, ((B j).indices.card : ℝ) := by ring
      _ ≤ 1 * ∑ j, ((B j).indices.card : ℝ) := mul_le_mul_of_nonneg_right hτslab hsum
      _ = _ := one_mul _
  simp only [L₀, List.map_ofFn, List.sum_ofFn, Function.comp_apply] at hLmass
  calc (d ^ 2 * τ ^ 3) * (C.indices.card : ℝ) =
        (d * τ) * ((d * τ) * (τ * (C.indices.card : ℝ))) := by ring
    _ ≤ (d * τ) * ((d * τ) * (A.cell.indices.card : ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hshapeRet (by positivity)) (by positivity)
    _ ≤ (d * τ) * ∑ j, ((B j).indices.card : ℝ) :=
      mul_le_mul_of_nonneg_left hslabRet (by positivity)
    _ ≤ _ := hLmass

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
