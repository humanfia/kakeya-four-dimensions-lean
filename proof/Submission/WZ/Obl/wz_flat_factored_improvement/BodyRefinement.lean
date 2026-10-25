-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.BodyRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyPackets
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.ChildPackets
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.PrismRefinement
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.SlabCounting

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_regular_transverse_affine_cells
  (PhysicalPacket AffineCell SlabSpec PrismRefinement slab image_shading_support
    compact_convex_slab_cut normalized_slab_volume_shrink slab_counting_of_good
    center_mem_prism)

def bodyChild {n : ℕ} (C : PhysicalPacket n) (f : Space ≃ᵃ[ℝ] Space)
    (I : Finset (Fin n)) (Z : Fin n → Set Space) (T : SlabSpec) : PhysicalPacket n := {
  indices := I, region := C.region ∩ f '' T.carrier, shading := fun i => f '' Z i }

theorem body_child_valid {n K : ℕ} {U Y : Fin n → Set Space} {C : PhysicalPacket n}
    {δ B d q S : ℝ} (P : BodyPacketValid U Y d C)
    (A : BodyPrepared (K := K) U C δ B S) (hS : 0 < S)
    (I : Finset (Fin n)) (hI : I.Nonempty) (hIA : I ⊆ A.cell.indices)
    (Z : Fin n → Set Space) (hZm : ∀ i ∈ I, MeasurableSet (Z i))
    (hZA : ∀ i ∈ I, Z i ⊆ A.cell.shading i)
    (hd : ∀ i ∈ I, ENNReal.ofReal q * volume (A.cell.affine ⁻¹' U i) ≤ volume (Z i))
    (T : SlabSpec) (hwhole : ∀ i ∈ I, A.cell.affine ⁻¹' U i ⊆ T.carrier) :
    BodyPacketValid U Y q (bodyChild C A.cell.affine I Z T) ∧
    (bodyChild C A.cell.affine I Z T).support = A.cell.affine '' (⋃ i ∈ I, Z i) ∧
    (bodyChild C A.cell.affine I Z T).support ⊆ C.support ∧
    volume (bodyChild C A.cell.affine I Z T).region ≤
      ENNReal.ofReal (2048 * S * T.width) * volume C.region := by
  have hIC := hIA.trans A.indices
  have himage (i : Fin n) (hi : i ∈ I) : A.cell.affine '' Z i ⊆ C.shading i := by
    rintro p ⟨z, hz, rfl⟩
    have h := hZA i hi hz
    rwa [A.shading_eq] at h
  have hcut := compact_convex_slab_cut P.compact P.convex A.cell.affine
    T.normal T.offset T.width
  refine ⟨{
    nonempty := hI, compact := hcut.1, convex := hcut.2,
    bounded := inter_subset_left.trans P.bounded,
    whole := ?_, measurable := ?_, original := ?_, source := ?_, density := ?_ },
    image_shading_support I A.cell.affine Z, ?_, ?_⟩
  · intro i hi p hp
    refine ⟨P.whole i (hIC hi) hp, A.cell.affine.symm p, ?_,
      A.cell.affine.apply_symm_apply p⟩
    exact hwhole i hi (by simpa only [mem_preimage, A.cell.affine.apply_symm_apply])
  · intro i hi
    exact A.cell.affine.toContinuousAffineEquiv.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr
      (hZm i hi)
  · exact fun i hi => (himage i hi).trans (P.original i (hIC hi))
  · exact fun i hi => (himage i hi).trans (P.source i (hIC hi))
  · intro i hi
    have hvol := A.volume_identity (A.cell.affine ⁻¹' U i)
    rw [image_preimage_eq _ A.cell.affine.surjective] at hvol
    change ENNReal.ofReal q * volume (U i) ≤ volume (A.cell.affine '' Z i)
    rw [hvol, A.volume_identity, mul_left_comm]
    exact mul_le_mul' le_rfl (hd i hi)
  · intro p hp
    obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp hp
    exact mem_iUnion₂.mpr ⟨i, hIC hi, himage i hi hpi⟩
  · exact normalized_slab_volume_shrink hS A.cell.affine A.jacobian_pos.le A.small
      A.volume_identity A.jacobian_volume T.unit_normal T.offset T.width_pos.le

open Classical in
theorem body_regular_core {n K : ℕ} {U Y : Fin n → Set Space} {C : PhysicalPacket n}
    {δ B d S h t q θ w : ℝ} (P : BodyPacketValid U Y d C)
    (A : BodyPrepared (K := K) U C δ B S)
    (I : Finset (Fin n)) (hI : I.Nonempty) (hIA : I ⊆ A.cell.indices)
    (Z : Fin n → Set Space) (hZA : ∀ i ∈ I, Z i ⊆ A.cell.shading i)
    (R : PrismRefinement I A.cell.a A.cell.b θ q K A.cell.center A.cell.axes Z)
    (hret : q * (I.card : ℝ) ≤ ((I.filter fun i => (R.core i).Nonempty).card : ℝ))
    (hh : 0 < h) (ht : 0 < t) (hq : 0 < q) (hw : 0 < w)
    (htq : t * q ≤ 1) (hhq : h ≤ q) (hhθ : h ≤ θ) (hslack : h * 6144 ≤ t * q)
    (hwidth : B * h / 2 ≤ A.cell.b)
    (S₀ : SlabSpec) (hSt : t ≤ S₀.width)
    (hmax : ∀ T : SlabSpec,
      T.weight I (fun i => A.cell.affine ⁻¹' U i)
        (fun i => (volume (A.cell.affine ⁻¹' U i)).toReal) / T.width ≤
        2 * (∑ i ∈ I, (volume (A.cell.affine ⁻¹' U i)).toReal) / S₀.width)
    (hweights : ∀ i ∈ I, w ≤ (volume (A.cell.affine ⁻¹' U i)).toReal ∧
      (volume (A.cell.affine ⁻¹' U i)).toReal ≤ 384 * w) :
    let J := I.filter fun i => (R.core i).Nonempty
    let G : AffineCell n K := { A.cell with indices := J, shading := R.core }
    BodyCellValid U Y B h G ∧ G.support ⊆ A.cell.affine '' (⋃ i ∈ I, Z i) := by
  classical
  let J := I.filter fun i => (R.core i).Nonempty
  let G : AffineCell n K := { A.cell with indices := J, shading := R.core }
  change BodyCellValid U Y B h G ∧ G.support ⊆ A.cell.affine '' (⋃ i ∈ I, Z i)
  have hJI : J ⊆ I := Finset.filter_subset _ _
  have hJA := hJI.trans hIA
  have hJ : J.Nonempty := by
    apply Finset.card_pos.mp
    have hIc : (0 : ℝ) < I.card := by exact_mod_cast hI.card_pos
    exact_mod_cast (mul_pos hq hIc).trans_le hret
  have hbody : ∀ i, G.body i = A.cell.body i := fun _ => rfl
  constructor
  · refine {
      nonempty := hJ, ordered := A.ordered, small := A.short_small, width := hwidth,
      jacobian_pos := A.jacobian_pos, volume_identity := A.volume_identity,
      body_small := fun i hi => A.body_small i (hJA hi),
      whole := fun i hi => A.whole i (hJA hi),
      measurable := fun i hi => R.core_measurable i (hJI hi),
      shading := ?_, density := ?_, regular := ?_, transverse := ?_, slabs := ?_ }
    · intro i hi p hp
      have h := hZA i (hJI hi) (R.core_subset i (hJI hi) hp)
      rw [A.shading_eq] at h
      exact ⟨A.preimage_body (hJA hi) (P.source i (A.indices (hJA hi)) h),
        P.original i (A.indices (hJA hi)) h⟩
    · intro i hi
      exact (mul_le_mul' (ENNReal.ofReal_le_ofReal hhq) le_rfl).trans
        (R.core_density i (hJI hi) (Finset.mem_filter.mp hi).2)
    · intro i hi p hp r har hr
      exact (mul_le_mul' (ENNReal.ofReal_le_ofReal hhq) le_rfl).trans
        (R.core_regular i (hJI hi) p hp r har hr)
    · intro p hp
      obtain ⟨i, hi, hpi⟩ := hp
      obtain ⟨i', hi', j', hj', hpi', hpj', hang⟩ := R.transverse p ⟨i, hJI hi, hpi⟩
      exact ⟨i', Finset.mem_filter.mpr ⟨hi', p, hpi'⟩,
        j', Finset.mem_filter.mpr ⟨hj', p, hpj'⟩, hpi', hpj', hhθ.trans hang⟩
    · intro ν s r hν hr
      have hcount := slab_counting_of_good I J (fun i => A.cell.affine ⁻¹' U i)
        A.cell.body S₀ hmax hJI ht hq hw (by norm_num : (1 : ℝ) ≤ 384)
        htq hSt hweights hret (fun i hi => A.preimage_body (hJA hi))
        (fun i _ => ⟨A.cell.center i, center_mem_prism
          (by dsimp [AffineCell.a]; positivity) (by dsimp [AffineCell.b]; positivity) _ _⟩)
        (fun i hi => A.body_small i (hJA hi)) ν s r hν hr
      have hset : {i : Fin n | i ∈ G.indices ∧
          G.body i ⊆ ball (0 : Space) 1 ∩ slab (innerSL ℝ ν) s r} =
          ↑(J.filter fun i => A.cell.body i ⊆ ball (0 : Space) 1 ∩ slab (innerSL ℝ ν) s r) := by
        ext i
        simp only [mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, G, hbody]
      change ENNReal.ofReal (Set.ncard {i : Fin n | i ∈ G.indices ∧
        G.body i ⊆ ball (0 : Space) 1 ∩ slab (innerSL ℝ ν) s r} : ℝ) ≤ _
      rw [hset, ncard_coe_finset]
      apply hcount.trans
      apply mul_le_mul'
      · apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        rw [inv_eq_one_div, div_le_div_iff₀ (mul_pos ht hq) hh]
        nlinarith
      · exact le_rfl
  · rintro p ⟨z, hz, rfl⟩
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz
    exact ⟨z, mem_iUnion₂.mpr ⟨i, hJI hi, R.core_subset i (hJI hi) hzi⟩, rfl⟩

end WangZahlLot.Obl.wz_flat_factored_improvement
