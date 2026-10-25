-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.RefineSlab.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.CertifyCore
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.ChildPackets
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.RefinementCounting
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.UniformMass

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open Module MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_balanced_cluster_cover

abbrev PacketOutcome (n K : ℕ) := AffineCell n K ⊕ PhysicalPacket n

def PacketOutcome.support {n K : ℕ} (z : PacketOutcome n K) : Set E :=
  Sum.elim AffineCell.support ShadedCell.support z

noncomputable def PacketOutcome.weight {n K : ℕ} (z : PacketOutcome n K) : ℝ :=
  Sum.elim (fun C => (C.indices.card : ℝ)) (fun C => (C.indices.card : ℝ)) z

def PacketOutcome.Valid {n K : ℕ} (z : PacketOutcome n K) (δ d h κ : ℝ)
    (parent : PhysicalPacket n) (x v : Fin n → E) (Y : Fin n → Set E) : Prop :=
  Sum.elim (fun G => G.Valid δ h x v Y)
    (fun C => C.Valid δ d x v Y ∧ volume C.region ≤ ENNReal.ofReal κ * volume parent.region) z

/-- Resolve a selected slab. Wide slabs yield a terminal core or angular children;
thin slabs immediately yield a smaller physical packet. -/
lemma refine_selected_slab {n K : ℕ} {C : PhysicalPacket n} {δ d S h t q θ w κ : ℝ}
    {x v : Fin n → E} {Y : Fin n → Set E} (hC : C.Valid δ d x v Y)
    (A : PreparedPacket (K := K) C δ S x v) (hS : 0 < S)
    (I : Finset (Fin n)) (hI : I.Nonempty) (hIA : I ⊆ A.cell.indices)
    (Z : Fin n → Set E) (hZm : ∀ i ∈ I, MeasurableSet (Z i))
    (hZA : ∀ i ∈ I, Z i ⊆ A.cell.shading i)
    (hZd : ∀ i ∈ I, ENNReal.ofReal (d / 2) *
      volume (A.cell.affine ⁻¹' closedTube δ (x i) (v i)) ≤ volume (Z i))
    (S₀ : SlabSpec)
    (hwhole : ∀ i ∈ I, A.cell.affine ⁻¹' closedTube δ (x i) (v i) ⊆ S₀.carrier)
    (hmax : ∀ T : SlabSpec,
      T.weight I (fun i => A.cell.affine ⁻¹' closedTube δ (x i) (v i))
          (fun i => (volume (A.cell.affine ⁻¹' closedTube δ (x i) (v i))).toReal) / T.width ≤
        2 * (∑ i ∈ I, (volume (A.cell.affine ⁻¹' closedTube δ (x i) (v i))).toReal) / S₀.width)
    (hweights : ∀ i ∈ I,
      w ≤ (volume (A.cell.affine ⁻¹' closedTube δ (x i) (v i))).toReal ∧
      (volume (A.cell.affine ⁻¹' closedTube δ (x i) (v i))).toReal ≤ 384 * w)
    (hUfin : ∀ i ∈ I, volume (A.cell.affine ⁻¹' closedTube δ (x i) (v i)) ≠ ∞)
    (hd : 0 < d) (hh : 0 < h) (ht : 0 < t) (hq : 0 < q) (hw : 0 < w) (hθ : 0 < θ)
    (hq1 : q ≤ 1) (hqsmall : 3072 * q ≤ d)
    (hbudget : 8 * (1000000 * (K + 1 : ℕ) * q) * (400000 * S) * 384 ≤ d)
    (hK : (1 / 2 : ℝ) ^ K < 2 * A.cell.a)
    (htq : t * q ≤ 1) (hhq : h ≤ q) (hhθ : h ≤ θ) (hslack : h * 6144 ≤ t * q)
    (hshrink : 2048 * S * t ≤ κ) (hθt : 9 * θ ≤ t)
    (ha : δ ^ (100 : ℕ) ≤ A.cell.a) (hb : δ * h ≤ A.cell.b)
    (hD : δ ^ (100 : ℕ) ≤ A.cell.jacobian ∧ A.cell.jacobian ≤ δ ^ (-100 : ℝ)) :
    ∃ L : List (PacketOutcome n K),
      (∀ z ∈ L, z.Valid δ q h κ C x v Y ∧ z.support ⊆ A.cell.affine '' (⋃ i ∈ I, Z i)) ∧
      L.Pairwise (fun z z' => Disjoint z.support z'.support) ∧
      q * (I.card : ℝ) ≤ (L.map PacketOutcome.weight).sum := by
  classical
  have hqhalf : q ≤ d / 2 := by linarith
  have hshrink_width {r : ℝ} (hr : r ≤ t) : 2048 * S * r ≤ κ :=
    (mul_le_mul_of_nonneg_left hr (by positivity)).trans hshrink
  by_cases hthin : S₀.width ≤ t
  · let C' : PhysicalPacket n := {
      indices := I, region := C.region ∩ A.cell.affine '' S₀.carrier,
      shading := fun i => A.cell.affine '' Z i }
    have hZd' : ∀ i ∈ I, ENNReal.ofReal q *
        volume (A.cell.affine ⁻¹' closedTube δ (x i) (v i)) ≤ volume (Z i) :=
      fun i hi => (mul_le_mul_left (ENNReal.ofReal_le_ofReal hqhalf) _).trans (hZd i hi)
    obtain ⟨hvalid, hsupport, _, hvol⟩ :=
      child_packet_from_slab hC A hS I hI hIA Z hZm hZA hZd' S₀ hwhole
    refine ⟨[Sum.inr C'], ?_, by simp, ?_⟩
    · intro z hz
      have hz' : z = Sum.inr C' := by simpa using hz
      subst z
      refine ⟨⟨hvalid, hvol.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal (hshrink_width hthin)) _)⟩, ?_⟩
      exact hsupport.le
    · simpa only [List.map_singleton, List.sum_singleton, PacketOutcome.weight, Sum.elim_inr, C'] using
        mul_le_of_le_one_left (Nat.cast_nonneg I.card) hq1
  have htS : t ≤ S₀.width := (lt_of_not_ge hthin).le
  have hZP : ∀ i ∈ I, Z i ⊆ A.cell.body i := by
    intro i hi p hp
    have hp' := hZA i hi hp
    rw [A.shading_eq] at hp'
    exact A.preimage_body i (hIA hi) (hC.2.2.2.2.2.2.2.1 i (A.indices_subset (hIA hi)) hp')
  obtain ⟨R⟩ := exists_prism_refinement I hI A.cell.center A.cell.axes Z
    (by dsimp [AffineCell.a]; positivity) A.ordered (A.short_small.trans (by norm_num)) hθ hq.le
    (fun i hi => (A.body_small i (hIA hi)).trans (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by norm_num : (1 / 100 : ℝ) ≤ 1)))) hZm hZP hK
  have hUV : ∀ i ∈ I, ENNReal.ofReal w ≤ volume (A.cell.affine ⁻¹' closedTube δ (x i) (v i)) ∧
      volume (A.cell.affine ⁻¹' closedTube δ (x i) (v i)) ≤ ENNReal.ofReal (384 * w) :=
    fun i hi => volume_bounds_of_toReal (hUfin i hi) (hweights i hi).1 (hweights i hi).2
  have hZV : ∀ i ∈ I, volume (Z i) ≤ ENNReal.ofReal (384 * w) := by
    intro i hi
    apply le_trans _ (hUV i hi).2
    apply measure_mono
    intro p hp
    have hp' := hZA i hi hp
    rw [A.shading_eq] at hp'
    exact hC.2.2.2.2.2.2.2.1 i (A.indices_subset (hIA hi)) hp'
  have hinput : ENNReal.ofReal ((d / 768) * (384 * w) * (I.card : ℝ)) ≤ ∑ i ∈ I, volume (Z i) := by
    have he : (d / 768) * (384 * w) = (d / 2) * w := by ring
    rw [he]
    apply uniform_mass_le_sum I _ (by positivity)
    intro i hi
    rw [ENNReal.ofReal_mul (by positivity)]
    exact (mul_le_mul_right (hUV i hi).1 _).trans (hZd i hi)
  have hPsum : (∑ i ∈ I, volume (A.cell.body i)) ≤
      ENNReal.ofReal ((400000 * S) * (384 * w) * (I.card : ℝ)) := by
    apply sum_le_uniform_mass I _ (by positivity)
    intro i hi
    rw [ENNReal.ofReal_mul (by positivity)]
    exact (A.body_volume i (hIA hi)).trans (mul_le_mul_right (hUV i hi).2 _)
  have hcost : ENNReal.ofReal (1000000 * (K + 1 : ℕ) * q) *
      (∑ i ∈ I, volume (A.cell.body i)) ≤ ENNReal.ofReal ((d / 768) * (384 * w) * (I.card : ℝ) / 4) := by
    apply le_trans (mul_le_mul_right hPsum _)
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_right hbudget (mul_nonneg hw.le (Nat.cast_nonneg I.card))
    nlinarith [h]
  rcases R.count_dichotomy (by positivity : 0 < d / 768) (by positivity : 0 < 384 * w)
      hq.le (by linarith : 4 * q ≤ d / 768) hZV hinput hcost with hcore | hnarrow
  · let J := I.filter fun i => (R.core i).Nonempty
    let G : AffineCell n K := { A.cell with indices := J, shading := R.core }
    obtain ⟨hvalid, hsupport⟩ := certify_regular_core hC A I hIA Z hZA R hcore hI hh ht hq hw
      htq hhq hhθ hslack S₀ htS hmax hweights ha hb hD
    refine ⟨[Sum.inl G], ?_, by simp, ?_⟩
    · intro z hz
      have hz' : z = Sum.inl G := by simpa using hz
      subst z
      exact ⟨hvalid, hsupport⟩
    · simpa only [List.map_singleton, List.sum_singleton, PacketOutcome.weight, Sum.elim_inl, G, J] using hcore
  · let J : Angular.Label → Finset (Fin n) := fun ℓ => I.filter fun i => (R.narrow i ∩ R.region ℓ).Nonempty
    let F := R.labels.filter fun ℓ => (J ℓ).Nonempty
    let label := enumerate F
    have hF (j : Fin F.card) : label j ∈ R.labels ∧ (J (label j)).Nonempty :=
      Finset.mem_filter.mp (enumerate_mem F j)
    have hJI (ℓ : Angular.Label) : J ℓ ⊆ I := Finset.filter_subset _ _
    have hnormal (j : Fin F.card) : ‖W θ (label j).1‖ = 1 := by
      obtain ⟨i, hi⟩ := (hF j).2
      exact (R.narrow_whole i (hJI _ hi) _ (Finset.mem_filter.mp hi).2).1
    let T (j : Fin F.card) : SlabSpec := ⟨W θ (label j).1, θ * (label j).2, 9 * θ, hnormal j, by positivity⟩
    let Z' (j : Fin F.card) (i : Fin n) := R.narrow i ∩ R.region (label j)
    let C' (j : Fin F.card) : PhysicalPacket n := {
      indices := J (label j), region := C.region ∩ A.cell.affine '' (T j).carrier,
      shading := fun i => A.cell.affine '' Z' j i }
    have hchild (j : Fin F.card) : (C' j).Valid δ q x v Y ∧
        (C' j).support = A.cell.affine '' (⋃ i ∈ J (label j), Z' j i) ∧
        (C' j).support ⊆ C.support ∧
        volume (C' j).region ≤ ENNReal.ofReal (2048 * S * (T j).width) * volume C.region := by
      apply child_packet_from_slab hC A hS (J (label j)) (hF j).2 ((hJI _).trans hIA) (Z' j)
      · intro i hi
        exact (R.narrow_measurable i (hJI _ hi)).inter (R.region_measurable _)
      · intro i hi
        exact inter_subset_left.trans ((R.narrow_subset i (hJI _ hi)).trans (hZA i (hJI _ hi)))
      · intro i hi
        exact (mul_le_mul_right (measure_mono (A.preimage_body i (hIA (hJI _ hi)))) _).trans
          (R.narrow_density i (hJI _ hi) _ (hF j).1 (Finset.mem_filter.mp hi).2)
      · intro i hi
        exact (A.preimage_body i (hIA (hJI _ hi))).trans
          (R.narrow_whole i (hJI _ hi) _ (Finset.mem_filter.mp hi).2).2
    have hsupport (j : Fin F.card) : (C' j).support ⊆ A.cell.affine '' (⋃ i ∈ I, Z i) := by
      rw [(hchild j).2.1]
      apply image_mono
      intro p hp
      obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp hp
      exact mem_iUnion₂.mpr ⟨i, hJI _ hi, R.narrow_subset i (hJI _ hi) hpi.1⟩
    have hregion (j : Fin F.card) : (C' j).support ⊆ A.cell.affine '' R.region (label j) := by
      rw [(hchild j).2.1]
      apply image_mono
      intro p hp
      obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp hp
      exact hpi.2
    refine ⟨List.ofFn (fun j => Sum.inr (C' j)), ?_, ?_, ?_⟩
    · intro z hz
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
      refine ⟨⟨(hchild j).1, (hchild j).2.2.2.trans ?_⟩, hsupport j⟩
      apply mul_le_mul_left
      exact ENNReal.ofReal_le_ofReal (hshrink_width hθt)
    · apply List.pairwise_ofFn.mpr
      intro j k hjk
      have hlabel : label j ≠ label k := fun he => (ne_of_lt hjk) (label.injective he)
      have hdj := (disjoint_image_iff A.cell.affine.injective).mpr (R.region_disjoint hlabel)
      exact hdj.mono (hregion j) (hregion k)
    · have hsumF : (∑ ℓ ∈ F, ((J ℓ).card : ℝ)) = ∑ ℓ ∈ R.labels, ((J ℓ).card : ℝ) := by
        apply Finset.sum_filter_of_ne
        intro ℓ hℓ hne
        apply Finset.nonempty_iff_ne_empty.mpr
        intro he
        simp [he] at hne
      simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, PacketOutcome.weight,
        Sum.elim_inr, C', ← sum_enumerate F (fun ℓ => ((J ℓ).card : ℝ)), label] using
        (show q * (I.card : ℝ) ≤ ∑ ℓ ∈ F, ((J ℓ).card : ℝ) from by rw [hsumF]; exact hnarrow)

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
