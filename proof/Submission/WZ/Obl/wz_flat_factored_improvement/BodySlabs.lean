-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.BodySlabs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyRefinement
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.RefinementCounting
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.UniformMass

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_regular_transverse_affine_cells
open WangZahlLot.Obl.wz_balanced_cluster_cover (W)

abbrev BodyOutcome (n K : ℕ) := AffineCell n K ⊕ PhysicalPacket n

def BodyOutcome.support {n K : ℕ} : BodyOutcome n K → Set Space :=
  Sum.elim AffineCell.support ShadedCell.support

noncomputable def BodyOutcome.weight {n K : ℕ} : BodyOutcome n K → ℝ :=
  Sum.elim (fun G => (G.indices.card : ℝ)) (fun C => (C.indices.card : ℝ))

def BodyOutcome.Valid {n K : ℕ} (U Y : Fin n → Set Space) (B q h κ : ℝ)
    (C : PhysicalPacket n) : BodyOutcome n K → Prop :=
  Sum.elim (BodyCellValid U Y B h)
    (fun C' => BodyPacketValid U Y q C' ∧ volume C'.region ≤ ENNReal.ofReal κ * volume C.region)

theorem resolve_body_slab {n K : ℕ} {U Y : Fin n → Set Space} {C : PhysicalPacket n}
    {δ B d S h t q θ w κ : ℝ} (P : BodyPacketValid U Y d C)
    (A : BodyPrepared (K := K) U C δ B S) (hS : 0 < S)
    (I : Finset (Fin n)) (hI : I.Nonempty) (hIA : I ⊆ A.cell.indices)
    (Z : Fin n → Set Space) (hZm : ∀ i ∈ I, MeasurableSet (Z i))
    (hZA : ∀ i ∈ I, Z i ⊆ A.cell.shading i)
    (hZd : ∀ i ∈ I, ENNReal.ofReal (d / 2) * volume (A.cell.affine ⁻¹' U i) ≤ volume (Z i))
    (S₀ : SlabSpec) (hwhole : ∀ i ∈ I, A.cell.affine ⁻¹' U i ⊆ S₀.carrier)
    (hmax : ∀ T : SlabSpec,
      T.weight I (fun i => A.cell.affine ⁻¹' U i)
        (fun i => (volume (A.cell.affine ⁻¹' U i)).toReal) / T.width ≤
      2 * (∑ i ∈ I, (volume (A.cell.affine ⁻¹' U i)).toReal) / S₀.width)
    (hweights : ∀ i ∈ I, w ≤ (volume (A.cell.affine ⁻¹' U i)).toReal ∧
      (volume (A.cell.affine ⁻¹' U i)).toReal ≤ 384 * w)
    (hfinite : ∀ i ∈ I, volume (A.cell.affine ⁻¹' U i) ≠ ∞)
    (hd : 0 < d) (hh : 0 < h) (ht : 0 < t) (hq : 0 < q) (hw : 0 < w) (hθ : 0 < θ)
    (hq1 : q ≤ 1) (hqsmall : 3072 * q ≤ d)
    (hbudget : 8 * (1000000 * (K + 1 : ℕ) * q) * (400000 * S) * 384 ≤ d)
    (hK : (1 / 2 : ℝ) ^ K < 2 * A.cell.a)
    (htq : t * q ≤ 1) (hhq : h ≤ q) (hhθ : h ≤ θ) (hslack : h * 6144 ≤ t * q)
    (hshrink : 2048 * S * t ≤ κ) (hθt : 9 * θ ≤ t)
    (hwidth : B * h / 2 ≤ A.cell.b) :
    ∃ L : List (BodyOutcome n K),
      (∀ z ∈ L, BodyOutcome.Valid U Y B q h κ C z ∧
        z.support ⊆ A.cell.affine '' (⋃ i ∈ I, Z i)) ∧
      L.Pairwise (fun z z' => Disjoint z.support z'.support) ∧
      q * (I.card : ℝ) ≤ (L.map BodyOutcome.weight).sum := by
  classical
  have hcut {T : SlabSpec} (hT : T.width ≤ t) :
      ENNReal.ofReal (2048 * S * T.width) ≤ ENNReal.ofReal κ := by
    apply ENNReal.ofReal_le_ofReal
    exact (mul_le_mul_of_nonneg_left hT (by positivity)).trans hshrink
  by_cases hthin : S₀.width ≤ t
  · obtain ⟨hvalid, hsupport, _, hvol⟩ := body_child_valid P A hS I hI hIA Z hZm hZA
      (fun i hi => (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith : q ≤ d / 2))
        le_rfl).trans (hZd i hi)) S₀ hwhole
    refine ⟨[Sum.inr (bodyChild C A.cell.affine I Z S₀)], ?_, by simp, ?_⟩
    · intro z hz
      obtain rfl : z = Sum.inr (bodyChild C A.cell.affine I Z S₀) := by simpa using hz
      exact ⟨⟨hvalid, hvol.trans (mul_le_mul' (hcut hthin) le_rfl)⟩, hsupport.le⟩
    · simpa only [List.map_singleton, List.sum_singleton, BodyOutcome.weight,
        Sum.elim_inr, bodyChild] using mul_le_of_le_one_left (Nat.cast_nonneg I.card) hq1
  have hZU (i : Fin n) (hi : i ∈ I) : Z i ⊆ A.cell.affine ⁻¹' U i := by
    intro p hp
    have hz := hZA i hi hp
    rw [A.shading_eq] at hz
    exact P.source i (A.indices (hIA hi)) hz
  obtain ⟨R⟩ := exists_prism_refinement I hI A.cell.center A.cell.axes Z
    (by dsimp [AffineCell.a]; positivity) A.ordered (A.short_small.trans (by norm_num))
    hθ hq.le
    (fun i hi => (A.body_small i (hIA hi)).trans (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by norm_num : (1 / 100 : ℝ) ≤ 1))))
    hZm (fun i hi => (hZU i hi).trans (A.preimage_body (hIA hi))) hK
  have hUv (i : Fin n) (hi : i ∈ I) :=
    volume_bounds_of_toReal (hfinite i hi) (hweights i hi).1 (hweights i hi).2
  have hZupper : ∀ i ∈ I, volume (Z i) ≤ ENNReal.ofReal (384 * w) :=
    fun i hi => (measure_mono (hZU i hi)).trans (hUv i hi).2
  have hZlower : ENNReal.ofReal ((d / 768) * (384 * w) * (I.card : ℝ)) ≤
      ∑ i ∈ I, volume (Z i) := by
    have he : d / 768 * (384 * w) = d / 2 * w := by ring
    rw [he]
    apply uniform_mass_le_sum I _ (by positivity)
    intro i hi
    rw [ENNReal.ofReal_mul (by positivity)]
    exact (mul_le_mul' le_rfl (hUv i hi).1).trans (hZd i hi)
  have hPupper : (∑ i ∈ I, volume (A.cell.body i)) ≤
      ENNReal.ofReal ((400000 * S) * (384 * w) * (I.card : ℝ)) := by
    apply sum_le_uniform_mass I _ (by positivity)
    intro i hi
    rw [ENNReal.ofReal_mul (by positivity)]
    exact (A.body_volume i (hIA hi)).trans (mul_le_mul' le_rfl (hUv i hi).2)
  have hcost : ENNReal.ofReal (1000000 * (K + 1 : ℕ) * q) *
      (∑ i ∈ I, volume (A.cell.body i)) ≤
      ENNReal.ofReal ((d / 768) * (384 * w) * (I.card : ℝ) / 4) := by
    apply (mul_le_mul' le_rfl hPupper).trans
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hh := mul_le_mul_of_nonneg_right hbudget
      (mul_nonneg hw.le (Nat.cast_nonneg I.card))
    nlinarith only [hh]
  rcases R.count_dichotomy (by positivity : 0 < d / 768) (by positivity : 0 < 384 * w)
      hq.le (by linarith : 4 * q ≤ d / 768) hZupper hZlower hcost with hcore | hnarrow
  · let J := I.filter fun i => (R.core i).Nonempty
    let G : AffineCell n K := { A.cell with indices := J, shading := R.core }
    have hG := body_regular_core P A I hI hIA Z hZA R hcore hh ht hq hw htq hhq hhθ
      hslack hwidth S₀ (le_of_not_ge hthin) hmax hweights
    refine ⟨[Sum.inl G], ?_, by simp, ?_⟩
    · intro z hz
      obtain rfl : z = Sum.inl G := by simpa using hz
      exact hG
    · simpa only [List.map_singleton, List.sum_singleton, BodyOutcome.weight,
        Sum.elim_inl, G, J] using hcore
  · let J : Angular.Label → Finset (Fin n) :=
      fun ℓ => I.filter fun i => (R.narrow i ∩ R.region ℓ).Nonempty
    let F := R.labels.filter fun ℓ => (J ℓ).Nonempty
    let label := enumerate F
    have hF (j : Fin F.card) : label j ∈ R.labels ∧ (J (label j)).Nonempty :=
      Finset.mem_filter.mp (enumerate_mem F j)
    have hJI (ℓ : Angular.Label) : J ℓ ⊆ I := Finset.filter_subset _ _
    have hn (j : Fin F.card) : ‖W θ (label j).1‖ = 1 := by
      obtain ⟨i, hi⟩ := (hF j).2
      exact (R.narrow_whole i (hJI _ hi) _ (Finset.mem_filter.mp hi).2).1
    let T (j : Fin F.card) : SlabSpec :=
      ⟨W θ (label j).1, θ * (label j).2, 9 * θ, hn j, by positivity⟩
    let Z' (j : Fin F.card) (i : Fin n) := R.narrow i ∩ R.region (label j)
    let C' (j : Fin F.card) := bodyChild C A.cell.affine (J (label j)) (Z' j) (T j)
    have hchildren (j : Fin F.card) : BodyPacketValid U Y q (C' j) ∧
        (C' j).support = A.cell.affine '' (⋃ i ∈ J (label j), Z' j i) ∧
        (C' j).support ⊆ C.support ∧
        volume (C' j).region ≤ ENNReal.ofReal (2048 * S * (T j).width) * volume C.region := by
      apply body_child_valid P A hS (J (label j)) (hF j).2 ((hJI _).trans hIA) (Z' j)
      · intro i hi
        exact (R.narrow_measurable i (hJI _ hi)).inter (R.region_measurable _)
      · intro i hi
        exact inter_subset_left.trans ((R.narrow_subset i (hJI _ hi)).trans (hZA i (hJI _ hi)))
      · intro i hi
        exact (mul_le_mul' le_rfl (measure_mono (A.preimage_body (hIA (hJI _ hi))))).trans
          (R.narrow_density i (hJI _ hi) _ (hF j).1 (Finset.mem_filter.mp hi).2)
      · intro i hi
        exact (A.preimage_body (hIA (hJI _ hi))).trans
          (R.narrow_whole i (hJI _ hi) _ (Finset.mem_filter.mp hi).2).2
    have hsupport (j : Fin F.card) : (C' j).support ⊆ A.cell.affine '' (⋃ i ∈ I, Z i) := by
      rw [(hchildren j).2.1]
      apply image_mono
      intro p hp
      obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp hp
      exact mem_iUnion₂.mpr ⟨i, hJI _ hi, R.narrow_subset i (hJI _ hi) hpi.1⟩
    have hregion (j : Fin F.card) : (C' j).support ⊆ A.cell.affine '' R.region (label j) := by
      rw [(hchildren j).2.1]
      apply image_mono
      intro p hp
      obtain ⟨i, _, hpi⟩ := mem_iUnion₂.mp hp
      exact hpi.2
    refine ⟨List.ofFn (fun j => Sum.inr (C' j)), ?_, ?_, ?_⟩
    · intro z hz
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
      exact ⟨⟨(hchildren j).1, (hchildren j).2.2.2.trans
        (mul_le_mul' (hcut hθt) le_rfl)⟩, hsupport j⟩
    · apply List.pairwise_ofFn.mpr
      intro j k hjk
      have hne : label j ≠ label k := fun he => (ne_of_lt hjk) (label.injective he)
      exact ((disjoint_image_iff A.cell.affine.injective).mpr (R.region_disjoint hne)).mono
        (hregion j) (hregion k)
    · have hsum : (∑ ℓ ∈ F, ((J ℓ).card : ℝ)) =
          ∑ ℓ ∈ R.labels, ((J ℓ).card : ℝ) := by
        apply Finset.sum_filter_of_ne
        intro ℓ hℓ hne
        apply Finset.nonempty_iff_ne_empty.mpr
        intro hempty
        simp [hempty] at hne
      have hh : q * (I.card : ℝ) ≤ ∑ ℓ ∈ F, ((J ℓ).card : ℝ) := by
        rw [hsum]
        exact hnarrow
      simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, BodyOutcome.weight,
        Sum.elim_inr, C', bodyChild, ← sum_enumerate F (fun ℓ => ((J ℓ).card : ℝ)), label] using hh

end WangZahlLot.Obl.wz_flat_factored_improvement
