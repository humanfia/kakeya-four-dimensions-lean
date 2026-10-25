-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.BodyStep.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.BodySlabs
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.CountedSlabs
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.IteratePackets

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_regular_transverse_affine_cells

theorem body_packet_step {n K N : ℕ} {U Y : Fin n → Set Space} {x : Fin n → Space}
    {δ B w d h S τ κ t θ : ℝ} (F : BodyGeometry U x δ B w)
    (hw : 0 < w) (hB : 0 ≤ B)
    (p : IterationParameters δ h S τ κ t θ N K)
    {C : PhysicalPacket n} (P : BodyPacketValid U Y d C)
    (hbottom : (1 / 2 : ℝ) ^ K * (384 * (n : ℝ)) ≤ 1)
    (hd : 0 < d) (hd1 : d ≤ 1) (hhq : h ≤ d * τ)
    (hslack : h * 6144 ≤ t * (d * τ)) :
    ∃ L : List (BodyOutcome n K),
      (∀ z ∈ L, BodyOutcome.Valid U Y B (d * τ) h κ C z ∧ z.support ⊆ C.support) ∧
      L.Pairwise (fun z z' => Disjoint z.support z'.support) ∧
      (d ^ 2 * τ ^ 3) * (C.indices.card : ℝ) ≤ (L.map BodyOutcome.weight).sum := by
  classical
  have hS : 0 < S := by linarith [p.scale_large]
  have hδ : 0 < δ := p.delta_pos
  obtain ⟨A⟩ := prepare_bodies F P p.delta_pos p.scale_large p.depth_scale
  let V := fun i => A.cell.affine ⁻¹' U i
  let w' := w / A.cell.jacobian
  have hw' : 0 < w' := div_pos hw A.jacobian_pos
  have hVc (i : Fin n) : IsCompact (V i) :=
    A.cell.affine.toContinuousAffineEquiv.toHomeomorph.isCompact_preimage.mpr (F.compact i)
  have hVconv (i : Fin n) : Convex ℝ (V i) :=
    (F.convex i).affine_preimage A.cell.affine.toAffineMap
  have hweights (i : Fin n) : w' ≤ (volume (V i)).toReal ∧ (volume (V i)).toReal ≤ 384 * w' :=
    affine_preimage_weights A.cell.affine A.jacobian_pos A.volume_identity
      (F.compact i) hw.le (by norm_num) (F.volume_bounds i)
  have hballs (i : Fin n) : ∃ z, ball z (δ / (6 * S)) ⊆ V i := by
    refine ⟨A.cell.affine.symm (x i), ?_⟩
    exact (ball_subset_affine_preimage A.cell.affine (by positivity : 0 < 6 * S)
      A.lipschitz (x i)).trans (preimage_mono (F.interior i))
  have hbounded : ∀ i ∈ A.cell.indices, V i ⊆ closedBall (0 : Space) 1 := by
    intro i hi
    apply ((preimage_mono (P.whole i (A.indices hi))).trans A.small).trans
    apply closedBall_subset_closedBall
    rw [div_le_one hS]
    linarith [p.scale_large]
  have hZm : ∀ i ∈ A.cell.indices, MeasurableSet (A.cell.shading i) := by
    intro i hi
    rw [A.shading_eq]
    exact (P.measurable i (A.indices hi)).preimage
      A.cell.affine.toContinuousAffineEquiv.continuous.measurable
  have hZV : ∀ i ∈ A.cell.indices, A.cell.shading i ⊆ V i := by
    intro i hi
    rw [A.shading_eq]
    exact preimage_mono (P.source i (A.indices hi))
  have hZd : ∀ i ∈ A.cell.indices,
      ENNReal.ofReal d * volume (V i) ≤ volume (A.cell.shading i) := by
    intro i hi
    rw [A.shading_eq]
    exact affine_preimage_density A.cell.affine A.jacobian_pos A.volume_identity _
      (P.density i (A.indices hi))
  have hbottom' : (1 / 2 : ℝ) ^ K * (384 * (A.cell.indices.card : ℝ)) ≤ 1 := by
    apply le_trans _ hbottom
    have hc : (A.cell.indices.card : ℝ) ≤ n := by
      exact_mod_cast (show A.cell.indices.card ≤ n by simpa using Finset.card_le_univ A.cell.indices)
    gcongr
  obtain ⟨m, Q, hQ, hQdisj, hQmass⟩ := counted_slab_extraction A.cell.indices V A.cell.shading
    (fun i _ => hVc i) (fun i _ => hVconv i) (by positivity : 0 < δ / (6 * S)) hw'
    (by norm_num : (0 : ℝ) < 384) hd.le (fun i _ => hballs i) hbounded
    (fun i _ => hweights i) K hbottom' hZm hZV hZd
  let support : ShadedCell (Fin n) → Set Space := fun Z => A.cell.affine '' Z.support
  have hdisj : (List.ofFn Q).Pairwise (fun Z Z' => Disjoint (support Z) (support Z')) := by
    apply List.pairwise_ofFn.mpr
    intro j k hjk
    exact (disjoint_image_iff A.cell.affine.injective).mpr (hQdisj (ne_of_lt hjk))
  have hq : 0 < d * τ := mul_pos hd p.tau_pos
  have hq1 : d * τ ≤ 1 := (mul_le_mul_of_nonneg_left p.tau_small hd.le).trans (by simpa)
  have hqsmall : 3072 * (d * τ) ≤ d := by
    nlinarith only [mul_le_mul_of_nonneg_left p.tau_density hd.le]
  have hbudget : 8 * (1000000 * (K + 1 : ℕ) * (d * τ)) * (400000 * S) * 384 ≤ d := by
    nlinarith only [mul_le_mul_of_nonneg_left p.tau_budget hd.le]
  have hK : (1 / 2 : ℝ) ^ K < 2 * A.cell.a := by
    calc
      _ < δ / (6 * S) := p.depth_scale
      _ = 2 * (δ / (12 * S)) := by ring
      _ ≤ _ := by gcongr; exact A.short_lower
  have hwidth : B * h / 2 ≤ A.cell.b := by
    calc
      _ ≤ B * (1 / (12 * S)) / 2 := by gcongr; exact p.quality_small
      _ = B / (24 * S) := by ring
      _ ≤ _ := A.middle_lower
  have hrefine : ∀ Z ∈ List.ofFn Q, ∃ L : List (BodyOutcome n K),
      (∀ z ∈ L, BodyOutcome.Valid U Y B (d * τ) h κ C z ∧ z.support ⊆ support Z) ∧
      L.Pairwise (fun z z' => Disjoint z.support z'.support) ∧
      (d * τ) * (Z.indices.card : ℝ) ≤ (L.map BodyOutcome.weight).sum := by
    intro Z hZ
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hZ
    obtain ⟨hJ, hJA, ⟨T, hT, _, hmax⟩, hwhole, hmeas, hsub, hdense⟩ := hQ j
    exact resolve_body_slab P A hS (Q j).indices hJ hJA (Q j).shading hmeas hsub hdense T
      (fun i hi => by simpa only [hT] using hwhole i hi) hmax
      (fun i _ => hweights i) (fun i _ => (hVc i).measure_ne_top)
      hd p.quality_pos p.width_pos hq hw' p.angle_pos hq1 hqsmall hbudget hK
      ((mul_le_mul_of_nonneg_left hq1 p.width_pos.le).trans (by simpa using p.width_small))
      hhq p.quality_angle hslack p.width_shrink p.angle_width hwidth
  obtain ⟨L, hL, hLdisj, hLmass⟩ := refine_finite_list (List.ofFn Q) support BodyOutcome.support
    (fun Z => (Z.indices.card : ℝ)) BodyOutcome.weight
    (BodyOutcome.Valid U Y B (d * τ) h κ C) (d * τ) hdisj hrefine
  have hsupport : ∀ Z ∈ List.ofFn Q, support Z ⊆ C.support := by
    intro Z hZ
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hZ
    rintro z ⟨p', hp', rfl⟩
    obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp hp'
    have hAi := (hQ j).2.1 hi
    have hpA := (hQ j).2.2.2.2.2.1 i hi hpi
    rw [A.shading_eq] at hpA
    exact mem_iUnion₂.mpr ⟨i, A.indices hAi, hpA⟩
  refine ⟨L, ?_, hLdisj, ?_⟩
  · intro z hz
    obtain ⟨hgood, Z, hZ, hsub⟩ := hL z hz
    exact ⟨hgood, hsub.trans (hsupport Z hZ)⟩
  have hshape : τ * (C.indices.card : ℝ) ≤ A.cell.indices.card := by
    have hc := mul_le_mul_of_nonneg_left A.retained p.tau_pos.le
    have hb := mul_le_mul_of_nonneg_right p.tau_shape (Nat.cast_nonneg A.cell.indices.card)
    nlinarith only [hc, hb]
  have hslab : (d * τ) * (A.cell.indices.card : ℝ) ≤ ∑ j, ((Q j).indices.card : ℝ) := by
    have hc := mul_le_mul_of_nonneg_left hQmass p.tau_pos.le
    have hb := mul_le_mul_of_nonneg_right p.tau_slab
      (Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => Nat.cast_nonneg (Q j).indices.card))
    nlinarith only [hc, hb]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] at hLmass
  calc
    (d ^ 2 * τ ^ 3) * (C.indices.card : ℝ) =
        (d * τ) * ((d * τ) * (τ * (C.indices.card : ℝ))) := by ring
    _ ≤ (d * τ) * ((d * τ) * (A.cell.indices.card : ℝ)) := by gcongr
    _ ≤ (d * τ) * ∑ j, ((Q j).indices.card : ℝ) := by gcongr
    _ ≤ _ := hLmass

end WangZahlLot.Obl.wz_flat_factored_improvement
