-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.SlabTransport.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.Basic

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set

/-- The preimage of a slab under an invertible affine map is a slab with unit normal. -/
theorem affine_preimage_slab (F : Space ≃ᴬ[ℝ] Space) {u : Space} (hu : ‖u‖ = 1)
    (t : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ (u' : Space) (t' r' : ℝ), ‖u'‖ = 1 ∧ 0 < r' ∧
      F ⁻¹' {p | |inner ℝ u p - t| ≤ r} = {p | |inner ℝ u' p - t'| ≤ r'} := by
  let L : Space ≃ₗ[ℝ] Space := F.toAffineEquiv.linear
  let v : Space := L.toLinearMap.adjoint u
  have hv : v ≠ 0 := by
    intro hz
    have hinner := L.toLinearMap.adjoint_inner_left (L.symm u) u
    change inner ℝ v (L.symm u) = inner ℝ u (L (L.symm u)) at hinner
    rw [hz, inner_zero_left, L.apply_symm_apply, real_inner_self_eq_norm_sq, hu] at hinner
    norm_num at hinner
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hmap (p : Space) : F p = L p + F 0 := by
    have hh := F.toAffineEquiv.map_vadd (0 : Space) p
    simpa only [vadd_eq_add, add_zero, L, ContinuousAffineEquiv.coe_coe] using hh
  refine ⟨‖v‖⁻¹ • v, (t - inner ℝ u (F 0)) / ‖v‖, r / ‖v‖, ?_, div_pos hr hnorm, ?_⟩
  · simp [norm_smul, hnorm.ne']
  · ext p
    simp only [mem_preimage, mem_ofPred_eq]
    have he : inner ℝ (‖v‖⁻¹ • v) p - (t - inner ℝ u (F 0)) / ‖v‖ =
        (inner ℝ u (F p) - t) / ‖v‖ := by
      rw [real_inner_smul_left, hmap p, inner_add_right]
      have hadj : inner ℝ v p = inner ℝ u (L p) :=
        L.toLinearMap.adjoint_inner_left p u
      rw [hadj]
      ring
    rw [he, abs_div, abs_of_pos hnorm, div_le_div_iff_of_pos_right hnorm]

/-- The normalized slab count in a reference body, without any round-body convention. -/
def ReferenceSlabCount (D : Set Space) (l : ℝ) {n : ℕ} (T : Fin n → Set Space) : Prop :=
  ∀ (u : Space) (t r : ℝ), ‖u‖ = 1 → 0 < r →
    ENNReal.ofReal ({i | T i ⊆ D ∩ {p | |inner ℝ u p - t| ≤ r}}.ncard : ℝ) * volume D ≤
      ENNReal.ofReal (l * n) * volume (D ∩ {p | |inner ℝ u p - t| ≤ r})

/-- Enlarging affine image tubes preserves a reference-body slab count. -/
theorem reference_slab_count_transport (F : Space ≃ᴬ[ℝ] Space)
    {D D' : Set Space} {J l : ℝ} (_hJ : 0 < J)
    (hvol : ∀ W : Set Space, volume (F '' W) = ENNReal.ofReal J * volume W)
    (hD : D' = F '' D) {n : ℕ} {T T' : Fin n → Set Space}
    (hT : ∀ i, T i ⊆ D) (hcontain : ∀ i, F '' T i ⊆ T' i)
    (hcount : ReferenceSlabCount D l T) :
    ∀ (u : Space) (t r : ℝ), ‖u‖ = 1 → 0 < r →
      ENNReal.ofReal ({i | T' i ⊆ {p | |inner ℝ u p - t| ≤ r}}.ncard : ℝ) * volume D' ≤
        ENNReal.ofReal (l * n) * volume (D' ∩ {p | |inner ℝ u p - t| ≤ r}) := by
  intro u t r hu hr
  obtain ⟨u', t', r', hu', hr', hpre⟩ := affine_preimage_slab F hu t hr
  let Q := {p : Space | |inner ℝ u p - t| ≤ r}
  let Q' := {p : Space | |inner ℝ u' p - t'| ≤ r'}
  change F ⁻¹' Q = Q' at hpre
  have hsub : {i : Fin n | T' i ⊆ Q} ⊆ {i : Fin n | T i ⊆ D ∩ Q'} := by
    intro i hi p hp
    refine ⟨hT i hp, ?_⟩
    have hFp : F p ∈ Q := hi (hcontain i ⟨p, hp, rfl⟩)
    change p ∈ Q'
    rw [← hpre]
    exact hFp
  have hmeasure : volume (D' ∩ Q) = ENNReal.ofReal J * volume (D ∩ Q') := by
    rw [hD, ← hvol]
    have heq : F '' (D ∩ Q') = (F '' D) ∩ Q := by
      rw [← hpre]
      exact Set.image_inter_preimage F D Q
    exact congrArg volume heq.symm
  have hbase := hcount u' t' r' hu' hr'
  change ENNReal.ofReal ({i : Fin n | T i ⊆ D ∩ Q'}.ncard : ℝ) * volume D ≤
    ENNReal.ofReal (l * n) * volume (D ∩ Q') at hbase
  calc
    ENNReal.ofReal ({i : Fin n | T' i ⊆ Q}.ncard : ℝ) * volume D' ≤
        ENNReal.ofReal ({i : Fin n | T i ⊆ D ∩ Q'}.ncard : ℝ) * volume D' := by
      apply mul_le_mul_left
      exact ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr (Set.ncard_mono hsub))
    _ = ENNReal.ofReal J *
        (ENNReal.ofReal ({i : Fin n | T i ⊆ D ∩ Q'}.ncard : ℝ) * volume D) := by
      rw [hD, hvol]
      ring
    _ ≤ ENNReal.ofReal J * (ENNReal.ofReal (l * n) * volume (D ∩ Q')) :=
      mul_le_mul_right hbase _
    _ = ENNReal.ofReal (l * n) * volume (D' ∩ Q) := by rw [hmeasure]; ring

/-- A lower bound for the transformed reference volume converts its normalized
slab estimate into the unit-ball Frostman convention. Extended tubes themselves
need not be contained in the transformed reference body. -/
theorem frostman_of_transported_reference {D : Set Space} {b l δ : ℝ}
    (hb : 0 < b) (hD : D ⊆ Metric.ball (0 : Space) 1)
    (hvol : ENNReal.ofReal b ≤ volume D) {n : ℕ} {x v : Fin n → Space}
    (hcount : ∀ (u : Space) (t r : ℝ), ‖u‖ = 1 → 0 < r →
      ENNReal.ofReal ({i | Tube δ (x i) (v i) ⊆ {p | |inner ℝ u p - t| ≤ r}}.ncard : ℝ) *
          volume D ≤ ENNReal.ofReal (l * n) * volume (D ∩ {p | |inner ℝ u p - t| ≤ r})) :
    Frostman δ (l / b) x v := by
  intro u t r hu hr
  let Q := {p : Space | |inner ℝ u p - t| ≤ r}
  have hsub : {i : Fin n | Tube δ (x i) (v i) ⊆ Metric.ball 0 1 ∩ Q} ⊆
      {i : Fin n | Tube δ (x i) (v i) ⊆ Q} := fun _ hi => hi.trans Set.inter_subset_right
  have hbound := hcount u t r hu hr
  apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hb).ne'
    ENNReal.ofReal_ne_top).mp
  calc
    ENNReal.ofReal b * ENNReal.ofReal
        ({i : Fin n | Tube δ (x i) (v i) ⊆ Metric.ball 0 1 ∩ Q}.ncard : ℝ) ≤
        ENNReal.ofReal ({i : Fin n | Tube δ (x i) (v i) ⊆ Q}.ncard : ℝ) * volume D := by
      rw [mul_comm]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr (Set.ncard_mono hsub))) hvol
    _ ≤ ENNReal.ofReal (l * n) * volume (D ∩ Q) := hbound
    _ ≤ ENNReal.ofReal (l * n) * volume (Metric.ball 0 1 ∩ Q) :=
      mul_le_mul_right (measure_mono (Set.inter_subset_inter_left Q hD)) _
    _ = ENNReal.ofReal b * (ENNReal.ofReal ((l / b) * n) *
        volume (Metric.ball 0 1 ∩ Q)) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hb.le]
      congr 2
      field_simp

/-- Enlarge a reference body, paying only the ratio of its volumes. -/
theorem reference_slab_count_enlarge {D D' : Set Space} {C l : ℝ} (hC : 0 ≤ C)
    (hDD : D ⊆ D') (hvol : volume D' ≤ ENNReal.ofReal C * volume D)
    {n : ℕ} {T : Fin n → Set Space} (hT : ∀ i, T i ⊆ D)
    (hcount : ReferenceSlabCount D l T) : ReferenceSlabCount D' (C * l) T := by
  intro u t r hu hr
  let Q := {p : Space | |inner ℝ u p - t| ≤ r}
  have heq : {i : Fin n | T i ⊆ D' ∩ Q} = {i : Fin n | T i ⊆ D ∩ Q} := by
    ext i
    constructor
    · exact fun h p hp => ⟨hT i hp, (h hp).2⟩
    · exact fun h p hp => ⟨hDD (h hp).1, (h hp).2⟩
  change ENNReal.ofReal ({i : Fin n | T i ⊆ D' ∩ Q}.ncard : ℝ) * volume D' ≤ _
  rw [heq]
  calc
    ENNReal.ofReal ({i : Fin n | T i ⊆ D ∩ Q}.ncard : ℝ) * volume D' ≤
        ENNReal.ofReal ({i : Fin n | T i ⊆ D ∩ Q}.ncard : ℝ) *
          (ENNReal.ofReal C * volume D) := mul_le_mul_right hvol _
    _ = ENNReal.ofReal C *
        (ENNReal.ofReal ({i : Fin n | T i ⊆ D ∩ Q}.ncard : ℝ) * volume D) := by ring
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (l * n) * volume (D ∩ Q)) :=
        mul_le_mul_right (hcount u t r hu hr) _
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (l * n) * volume (D' ∩ Q)) := by
        gcongr
    _ = ENNReal.ofReal ((C * l) * n) * volume (D' ∩ Q) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hC]
        congr 2
        ring

/-- Enlarge the reference body of the unit-ball Frostman condition. The loss
is an upper bound for the new body's volume. -/
theorem reference_count_of_frostman {δ l C : ℝ} (hC : 0 ≤ C) {D : Set Space}
    (hD : Metric.ball (0 : Space) 1 ⊆ D) (hvol : volume D ≤ ENNReal.ofReal C)
    {n : ℕ} {x v : Fin n → Space}
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1)
    (hF : Frostman δ l x v) :
    ReferenceSlabCount D (C * l) (fun i => Tube δ (x i) (v i)) := by
  intro u t r hu hr
  let Q := {p : Space | |inner ℝ u p - t| ≤ r}
  have heq : {i : Fin n | Tube δ (x i) (v i) ⊆ D ∩ Q} =
      {i : Fin n | Tube δ (x i) (v i) ⊆ Metric.ball 0 1 ∩ Q} := by
    ext i
    constructor
    · exact fun h p hp => ⟨hball i hp, (h hp).2⟩
    · exact fun h p hp => ⟨hD (h hp).1, (h hp).2⟩
  change ENNReal.ofReal ({i : Fin n | Tube δ (x i) (v i) ⊆ D ∩ Q}.ncard : ℝ) * volume D ≤ _
  rw [heq]
  have hbase := hF u t r hu hr
  calc
    ENNReal.ofReal ({i : Fin n | Tube δ (x i) (v i) ⊆ Metric.ball 0 1 ∩ Q}.ncard : ℝ) *
        volume D ≤
        (ENNReal.ofReal (l * n) * volume (Metric.ball 0 1 ∩ Q)) * ENNReal.ofReal C :=
      mul_le_mul' hbase hvol
    _ ≤ (ENNReal.ofReal (l * n) * volume (D ∩ Q)) * ENNReal.ofReal C :=
      mul_le_mul_left (mul_le_mul_right (measure_mono (Set.inter_subset_inter_left Q hD)) _) _
    _ = ENNReal.ofReal ((C * l) * n) * volume (D ∩ Q) := by
      rw [mul_right_comm, mul_comm (ENNReal.ofReal (l * n)), ← ENNReal.ofReal_mul hC]
      congr 2
      ring

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
