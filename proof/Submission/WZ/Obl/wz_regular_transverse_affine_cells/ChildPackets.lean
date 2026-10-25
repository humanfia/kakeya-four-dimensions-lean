-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.ChildPackets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.PreparePacket
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.SlabSelection

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open Module MeasureTheory Set Metric
open scoped ENNReal

lemma PreparedPacket.preimage_body {n K : ℕ} {C : PhysicalPacket n} {δ S : ℝ}
    {x v : Fin n → E} (A : PreparedPacket (K := K) C δ S x v) (i : Fin n)
    (hi : i ∈ A.cell.indices) :
    A.cell.affine ⁻¹' closedTube δ (x i) (v i) ⊆ A.cell.body i := by
  intro p hp
  obtain ⟨q, hq, heq⟩ := A.whole_body i hi hp
  exact A.cell.affine.injective heq ▸ hq

lemma image_shading_support {ι : Type*} (I : Finset ι) (f : E → E) (Z : ι → Set E) :
    (⋃ i ∈ I, f '' Z i) = f '' (⋃ i ∈ I, Z i) := by
  simp only [image_iUnion]

/-- Transport a normalized slab piece to a new compact convex physical packet. -/
lemma child_packet_from_slab {n K : ℕ} {C : PhysicalPacket n} {δ d S q : ℝ}
    {x v : Fin n → E} {Y : Fin n → Set E} (hC : C.Valid δ d x v Y)
    (A : PreparedPacket (K := K) C δ S x v) (hS : 0 < S)
    (I : Finset (Fin n)) (hI : I.Nonempty) (hIA : I ⊆ A.cell.indices)
    (Z : Fin n → Set E) (hZm : ∀ i ∈ I, MeasurableSet (Z i))
    (hZA : ∀ i ∈ I, Z i ⊆ A.cell.shading i)
    (hZd : ∀ i ∈ I, ENNReal.ofReal q * volume (A.cell.affine ⁻¹' closedTube δ (x i) (v i)) ≤ volume (Z i))
    (T : SlabSpec) (hwhole : ∀ i ∈ I, A.cell.affine ⁻¹' closedTube δ (x i) (v i) ⊆ T.carrier) :
    let C' : PhysicalPacket n := {
      indices := I, region := C.region ∩ A.cell.affine '' T.carrier,
      shading := fun i => A.cell.affine '' Z i }
    C'.Valid δ q x v Y ∧ C'.support = A.cell.affine '' (⋃ i ∈ I, Z i) ∧
      C'.support ⊆ C.support ∧
      volume C'.region ≤ ENNReal.ofReal (2048 * S * T.width) * volume C.region := by
  let C' : PhysicalPacket n := {
    indices := I, region := C.region ∩ A.cell.affine '' T.carrier,
    shading := fun i => A.cell.affine '' Z i }
  change C'.Valid δ q x v Y ∧ C'.support = A.cell.affine '' (⋃ i ∈ I, Z i) ∧
    C'.support ⊆ C.support ∧ _
  obtain ⟨hCne, hCc, hCconv, hCbound, hCwhole, hCm, hCsub, hCbody, hCd⟩ := hC
  have hIC : I ⊆ C.indices := hIA.trans A.indices_subset
  have hZC : ∀ i ∈ I, A.cell.affine '' Z i ⊆ C.shading i := by
    intro i hi p hp
    obtain ⟨z, hz, rfl⟩ := hp
    have h := hZA i hi hz
    rwa [A.shading_eq i] at h
  have hcompact := compact_convex_slab_cut hCc hCconv A.cell.affine T.normal T.offset T.width
  refine ⟨⟨hI, hcompact.1, hcompact.2, inter_subset_left.trans hCbound, ?_, ?_, ?_, ?_, ?_⟩,
    image_shading_support I A.cell.affine Z, ?_, ?_⟩
  · intro i hi p hp
    refine ⟨hCwhole i (hIC hi) hp, A.cell.affine.symm p, ?_, A.cell.affine.apply_symm_apply p⟩
    apply hwhole i hi
    simpa only [mem_preimage, A.cell.affine.apply_symm_apply] using hp
  · intro i hi
    exact A.cell.affine.toContinuousAffineEquiv.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr (hZm i hi)
  · intro i hi
    exact (hZC i hi).trans (hCsub i (hIC hi))
  · intro i hi
    exact (hZC i hi).trans (hCbody i (hIC hi))
  · intro i hi
    have he := A.volume_identity (A.cell.affine ⁻¹' closedTube δ (x i) (v i))
    rw [image_preimage_eq _ A.cell.affine.surjective] at he
    change ENNReal.ofReal q * volume (closedTube δ (x i) (v i)) ≤ volume (A.cell.affine '' Z i)
    rw [he, A.volume_identity, mul_left_comm]
    exact mul_le_mul_right (hZd i hi) _
  · intro p hp
    obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp hp
    exact mem_iUnion₂.mpr ⟨i, hIC hi, hZC i hi hpi⟩
  · exact normalized_slab_volume_shrink hS A.cell.affine A.jacobian_pos.le A.small
      A.volume_identity A.jacobian_volume T.unit_normal T.offset T.width_pos.le

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
