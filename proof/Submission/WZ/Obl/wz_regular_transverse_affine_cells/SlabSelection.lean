-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.SlabSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Slab
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Greedy

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open MeasureTheory Set
open scoped ENNReal

/-- A finite dyadic layer estimate, with an explicit remainder at the bottom scale. -/
lemma dyadic_layer_bound {w x : ℝ} (hw : 0 ≤ w) (hx : x ≤ w) (K : ℕ) :
    x ≤ (1 / 2 : ℝ) ^ K * w + ∑ k ∈ Finset.range K,
      if (1 / 2 : ℝ) ^ (k + 1) * w ≤ x then (1 / 2 : ℝ) ^ k * w else 0 := by
  induction K with
  | zero => simpa using hx
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hsum : 0 ≤ ∑ k ∈ Finset.range K,
        if (1 / 2 : ℝ) ^ (k + 1) * w ≤ x then (1 / 2 : ℝ) ^ k * w else 0 := by
      apply Finset.sum_nonneg
      intro k _
      split_ifs <;> positivity
    split_ifs with h
    · have : 0 ≤ (1 / 2 : ℝ) ^ (K + 1) * w := by positivity
      linarith
    · exact (le_of_not_ge h).trans (le_add_of_nonneg_right (by simpa using hsum))

/-- Bounds for the mass of dyadic superlevel sets control the total intersection mass. -/
lemma finite_dyadic_mass_bound {ι : Type*} (F : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ F, 0 ≤ w i) (hx : ∀ i ∈ F, x i ≤ w i)
    (K : ℕ) (A : ℝ)
    (hlevel : ∀ k < K, (1 / 2 : ℝ) ^ (k + 1) *
      (∑ i ∈ F, if (1 / 2 : ℝ) ^ (k + 1) * w i ≤ x i then w i else 0) ≤ A) :
    ∑ i ∈ F, x i ≤ (1 / 2 : ℝ) ^ K * (∑ i ∈ F, w i) + 2 * K * A := by
  classical
  calc
    ∑ i ∈ F, x i ≤ ∑ i ∈ F, ((1 / 2 : ℝ) ^ K * w i +
        ∑ k ∈ Finset.range K,
          if (1 / 2 : ℝ) ^ (k + 1) * w i ≤ x i then (1 / 2 : ℝ) ^ k * w i else 0) :=
      Finset.sum_le_sum fun i hi => dyadic_layer_bound (hw i hi) (hx i hi) K
    _ = (1 / 2 : ℝ) ^ K * (∑ i ∈ F, w i) +
        ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k *
          (∑ i ∈ F, if (1 / 2 : ℝ) ^ (k + 1) * w i ≤ x i then w i else 0) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    _ ≤ (1 / 2 : ℝ) ^ K * (∑ i ∈ F, w i) + ∑ _k ∈ Finset.range K, 2 * A := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro k hk
      have h := hlevel k (Finset.mem_range.mp hk)
      have he : (1 / 2 : ℝ) ^ k = 2 * (1 / 2 : ℝ) ^ (k + 1) := by
        rw [pow_succ]; ring
      rw [he]
      nlinarith
    _ = _ := by simp; ring

/-- A slab containing an open ball has width at least half its radius. -/
lemma half_radius_le_slab_width {ν x : E} {s r δ : ℝ}
    (hν : ‖ν‖ = 1) (hδ : 0 < δ)
    (hball : Metric.ball x δ ⊆ slab (innerSL ℝ ν) s r) : δ / 2 ≤ r := by
  have hplus : x + (δ / 2) • ν ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hν,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  have hminus : x - (δ / 2) • ν ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, dist_eq_norm]
    have he : x - (δ / 2) • ν - x = -((δ / 2) • ν) := by abel
    rw [he, norm_neg, norm_smul, hν, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  have hp := hball hplus
  have hm := hball hminus
  have hii : inner ℝ ν ν = 1 := by rw [real_inner_self_eq_norm_sq, hν]; norm_num
  change |inner ℝ ν (x + (δ / 2) • ν) - s| ≤ r at hp
  change |inner ℝ ν (x - (δ / 2) • ν) - s| ≤ r at hm
  simp only [inner_add_right, inner_sub_right, real_inner_smul_right, hii, mul_one] at hp hm
  have hp' := (abs_le.mp hp).2
  have hm' := (abs_le.mp hm).1
  linarith

/-- The parameters of a nondegenerate Euclidean slab. -/
structure SlabSpec where
  normal : E
  offset : ℝ
  width : ℝ
  unit_normal : ‖normal‖ = 1
  width_pos : 0 < width

def SlabSpec.carrier (S : SlabSpec) : Set E :=
  slab (innerSL ℝ S.normal) S.offset S.width

open Classical in
noncomputable def SlabSpec.weight {ι : Type*} (S : SlabSpec)
    (F : Finset ι) (U : ι → Set E) (w : ι → ℝ) : ℝ :=
  ∑ i ∈ F, if U i ⊆ S.carrier then w i else 0

lemma SlabSpec.weight_nonneg {ι : Type*} (S : SlabSpec)
    (F : Finset ι) (U : ι → Set E) (w : ι → ℝ) (hw : ∀ i ∈ F, 0 ≤ w i) :
    0 ≤ S.weight F U w := by
  classical
  apply Finset.sum_nonneg
  intro i hi
  split_ifs <;> first | exact hw i hi | exact le_rfl

lemma SlabSpec.weight_le_total {ι : Type*} (S : SlabSpec)
    (F : Finset ι) (U : ι → Set E) (w : ι → ℝ) (hw : ∀ i ∈ F, 0 ≤ w i) :
    S.weight F U w ≤ ∑ i ∈ F, w i := by
  classical
  apply Finset.sum_le_sum
  intro i hi
  split_ifs <;> first | exact le_rfl | exact hw i hi

/-- A slab can be chosen within a factor two of the best weighted density.
No compactness assertion for the full parameter space of slabs is needed. -/
lemma exists_near_maximal_slab {ι : Type*} (F : Finset ι) (hF : F.Nonempty)
    (U : ι → Set E) (w : ι → ℝ) (hw : ∀ i ∈ F, 0 < w i)
    {δ : ℝ} (hδ : 0 < δ)
    (hballs : ∀ i ∈ F, ∃ x, Metric.ball x δ ⊆ U i)
    (hbounded : ∀ i ∈ F, U i ⊆ Metric.closedBall (0 : E) 1) :
    ∃ S : SlabSpec, S.width ≤ 2 ∧ 0 < S.weight F U w ∧
      ∀ S' : SlabSpec, S'.weight F U w / S'.width ≤
        2 * (S.weight F U w / S.width) := by
  classical
  let W : ℝ := ∑ i ∈ F, w i
  have hW : 0 < W := Finset.sum_pos (fun i hi => hw i hi) hF
  have hw0 : ∀ i ∈ F, 0 ≤ w i := fun i hi => (hw i hi).le
  let e : E := EuclideanSpace.basisFun (Fin 3) ℝ 0
  have he : ‖e‖ = 1 := (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.1 0
  let S₀ : SlabSpec := ⟨e, 0, 1, he, by norm_num⟩
  have hS₀ : S₀.weight F U w = W := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [ite_eq_left]
    intro p hp
    have hp' : ‖p‖ ≤ 1 := by simpa using hbounded i hi hp
    change |inner ℝ e p - 0| ≤ 1
    simpa only [sub_zero, he, one_mul] using
      (abs_real_inner_le_norm e p).trans (mul_le_mul_of_nonneg_left hp' (norm_nonneg e))
  let score : SlabSpec → ℝ := fun S => S.weight F U w / S.width
  have hbound : ∀ S, score S ≤ 2 * W / δ := by
    intro S
    by_cases hex : ∃ i ∈ F, U i ⊆ S.carrier
    · obtain ⟨i, hi, hUi⟩ := hex
      obtain ⟨x, hx⟩ := hballs i hi
      have hwidth := half_radius_le_slab_width S.unit_normal hδ (hx.trans hUi)
      calc score S ≤ W / S.width :=
            div_le_div_of_nonneg_right (S.weight_le_total F U w hw0) S.width_pos.le
        _ ≤ W / (δ / 2) := div_le_div_of_nonneg_left hW.le (by positivity) hwidth
        _ = 2 * W / δ := by ring
    · have hz : S.weight F U w = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact ite_eq_right (fun h => hex ⟨i, hi, h⟩)
      simp only [score, hz, zero_div]
      positivity
  have hbb : BddAbove (Set.range score) := ⟨2 * W / δ, by
    rintro _ ⟨S, rfl⟩
    exact hbound S⟩
  have hS₀score : score S₀ = W := by simp [score, hS₀, S₀]
  have hsup : 0 < sSup (Set.range score) := by
    apply lt_of_lt_of_le hW
    rw [← hS₀score]
    exact le_csSup hbb (mem_range_self S₀)
  obtain ⟨v, ⟨S, rfl⟩, hS⟩ := exists_lt_of_lt_csSup
    (show (Set.range score).Nonempty from ⟨score S₀, mem_range_self S₀⟩)
    (show sSup (Set.range score) / 2 < sSup (Set.range score) by linarith)
  have hSpos : 0 < score S := by linarith
  have hwS : 0 < S.weight F U w := (div_pos_iff_of_pos_right S.width_pos).mp hSpos
  have hmax : ∀ S', score S' ≤ 2 * score S := by
    intro S'
    have h := le_csSup hbb (mem_range_self S')
    linarith
  refine ⟨S, ?_, hwS, hmax⟩
  have hwidth := hmax S₀
  rw [hS₀score] at hwidth
  have hweight := S.weight_le_total F U w hw0
  dsimp [score] at hwidth
  have hmul : W * S.width ≤ 2 * S.weight F U w := by
    apply (le_div_iff₀ S.width_pos).mp
    simpa only [mul_div_assoc] using hwidth
  change S.weight F U w ≤ W at hweight
  nlinarith

/-- Near-maximality bounds the weight of every substantial slab-intersection level. -/
lemma slab_intersection_level_bound {ι : Type*} (F : Finset ι) (U : ι → Set E)
    (hUc : ∀ i ∈ F, IsCompact (U i)) (hUconv : ∀ i ∈ F, Convex ℝ (U i))
    (hUpos : ∀ i ∈ F, volume (U i) ≠ 0)
    (S : SlabSpec)
    (hmax : ∀ T : SlabSpec,
      T.weight F U (fun i => (volume (U i)).toReal) / T.width ≤
        2 * (S.weight F U (fun i => (volume (U i)).toReal) / S.width))
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    t * (∑ i ∈ F, if t * (volume (U i)).toReal ≤ (volume (U i ∩ S.carrier)).toReal
      then (volume (U i)).toReal else 0) ≤
      160 * S.weight F U (fun i => (volume (U i)).toReal) := by
  classical
  let T : SlabSpec := ⟨S.normal, S.offset, 80 * S.width / t,
    S.unit_normal, div_pos (mul_pos (by norm_num) S.width_pos) ht⟩
  have hsub : ∀ i ∈ F, t * (volume (U i)).toReal ≤ (volume (U i ∩ S.carrier)).toReal →
      U i ⊆ T.carrier := by
    intro i hi hmass
    apply subset_enlarged_slab_of_mass (hUc i hi) (hUconv i hi) (hUpos i hi)
      (innerSL ℝ S.normal) S.offset S.width t S.width_pos.le ht ht1
    calc ENNReal.ofReal t * volume (U i)
        = ENNReal.ofReal (t * (volume (U i)).toReal) := by
          rw [ENNReal.ofReal_mul ht.le, ENNReal.ofReal_toReal (hUc i hi).measure_ne_top]
      _ ≤ ENNReal.ofReal (volume (U i ∩ S.carrier)).toReal := ENNReal.ofReal_le_ofReal hmass
      _ = volume (U i ∩ S.carrier) := ENNReal.ofReal_toReal
        (measure_ne_top_of_subset inter_subset_left (hUc i hi).measure_ne_top)
  have hweight : (∑ i ∈ F,
        if t * (volume (U i)).toReal ≤ (volume (U i ∩ S.carrier)).toReal
        then (volume (U i)).toReal else 0) ≤ T.weight F U (fun i => (volume (U i)).toReal) := by
    apply Finset.sum_le_sum
    intro i hi
    dsimp only
    split_ifs with h h' h'
    · exact le_rfl
    · exact False.elim (h' (hsub i hi h))
    · exact ENNReal.toReal_nonneg
    · exact le_rfl
  have h := (div_le_iff₀ T.width_pos).mp (hmax T)
  change T.weight F U (fun i => (volume (U i)).toReal) ≤
    2 * (S.weight F U (fun i => (volume (U i)).toReal) / S.width) * (80 * S.width / t) at h
  have he : 2 * (S.weight F U (fun i => (volume (U i)).toReal) / S.width) *
      (80 * S.width / t) = 160 * S.weight F U (fun i => (volume (U i)).toReal) / t := by
    field_simp [S.width_pos.ne', ht.ne']
    ring
  rw [he, le_div_iff₀ ht] at h
  exact (mul_le_mul_of_nonneg_left hweight ht.le).trans (by nlinarith [h])

/-- A nearly maximal slab loses only a logarithmic factor when partial intersections
are charged to the weight of the wholly contained convex sets. -/
lemma near_maximal_slab_overlap_bound {ι : Type*} (F : Finset ι) (U : ι → Set E)
    (hUc : ∀ i ∈ F, IsCompact (U i)) (hUconv : ∀ i ∈ F, Convex ℝ (U i))
    (hUpos : ∀ i ∈ F, volume (U i) ≠ 0)
    (S : SlabSpec)
    (hmax : ∀ T : SlabSpec,
      T.weight F U (fun i => (volume (U i)).toReal) / T.width ≤
        2 * (S.weight F U (fun i => (volume (U i)).toReal) / S.width))
    (K : ℕ)
    (hbottom : (1 / 2 : ℝ) ^ K * (∑ i ∈ F, (volume (U i)).toReal) ≤
      S.weight F U (fun i => (volume (U i)).toReal)) :
    ∑ i ∈ F, (volume (U i ∩ S.carrier)).toReal ≤
      (1 + 320 * K) * S.weight F U (fun i => (volume (U i)).toReal) := by
  have h := finite_dyadic_mass_bound F (fun i => (volume (U i)).toReal)
    (fun i => (volume (U i ∩ S.carrier)).toReal)
    (fun _ _ => ENNReal.toReal_nonneg)
    (fun i hi => ENNReal.toReal_mono (hUc i hi).measure_ne_top (measure_mono inter_subset_left))
    K (160 * S.weight F U (fun i => (volume (U i)).toReal))
    (fun k _ => slab_intersection_level_bound F U hUc hUconv hUpos S hmax
      (by positivity) (pow_le_one₀ (by norm_num) (by norm_num)))
  nlinarith

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
