-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.FlatMap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.PairWidth
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.TubeBodies

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (norm_sq_coords)
open WangZahlLot.Obl.wz_regular_transverse_affine_cells
  (closedTube tube_subset_closedTube closedTube_endpoints)

noncomputable section

def flatScales (a b : ℝ) : Fin 3 → ℝ := ![1 / (4 * a), 1 / (4 * b), 1 / 8]

theorem flatScales_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ i, 0 < flatScales a b i := by
  intro i; fin_cases i <;> dsimp [flatScales] <;> positivity

def flatMap (e : AffineIsometryEquiv ℝ Space Space) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) : Space ≃ᵃ[ℝ] Space :=
  coordinateAffine e (flatScales a b) (fun i => (flatScales_pos ha hb i).ne')

theorem flatMap_apply (e : AffineIsometryEquiv ℝ Space Space) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (p : Space) (i : Fin 3) :
    flatMap e a b ha hb p i = flatScales a b i * e.symm p i := rfl

theorem flatMap_linear (e : AffineIsometryEquiv ℝ Space Space) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (v : Space) (i : Fin 3) :
    (flatMap e a b ha hb).linear v i = flatScales a b i * e.symm.linearIsometryEquiv v i := rfl

theorem flatMap_volume (e : AffineIsometryEquiv ℝ Space Space) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (U : Set Space) :
    volume (flatMap e a b ha hb '' U) = ENNReal.ofReal (1 / (128 * a * b)) * volume U := by
  rw [flatMap, coordinateAffine_volume e _ (flatScales_pos ha hb)]
  congr 2
  rw [Fin.prod_univ_three]
  dsimp [flatScales]
  ring

theorem flatMap_dist_lower (e : AffineIsometryEquiv ℝ Space Space) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (hb2 : b ≤ 2) (p q : Space) :
    dist p q / 8 ≤ dist (flatMap e a b ha hb p) (flatMap e a b ha hb q) := by
  have hh := coordinateAffine_dist_lower e (fun i => (flatScales_pos ha hb i).ne')
    (by norm_num : (0 : ℝ) ≤ 1 / 8) (fun i => ?_) p q
  · simpa only [flatMap, one_div_mul_eq_div] using hh
  · rw [abs_of_pos (flatScales_pos ha hb i)]
    fin_cases i <;> dsimp [flatScales]
    · rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      linarith
    · rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      linarith
    · rfl

theorem flatMap_prism_norm (e : AffineIsometryEquiv ℝ Space Space) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) {p : Space} (hp : p ∈ e '' StandardPrism a b) :
    ‖flatMap e a b ha hb p‖ ≤ 1 / 2 := by
  obtain ⟨q, hq, rfl⟩ := hp
  have hi (i : Fin 3) : |flatMap e a b ha hb (e q) i| ≤ 1 / 4 := by
    rw [flatMap_apply, e.symm_apply_apply, abs_mul, abs_of_pos (flatScales_pos ha hb i)]
    fin_cases i <;> dsimp [flatScales]
    · apply (mul_le_mul_of_nonneg_left hq.1 (by positivity)).trans_eq
      field_simp
    · apply (mul_le_mul_of_nonneg_left hq.2.1 (by positivity)).trans_eq
      field_simp
    · linarith [hq.2.2]
  convert WangZahlLot.Obl.wz_balanced_cluster_cover.norm_le_of_forall_abs_le (by norm_num) hi using 1 <;> norm_num

theorem standardPrism_closed (a b : ℝ) : IsClosed (StandardPrism a b) := by
  exact (isClosed_le (show Continuous (fun p : Space => |p 0|) by fun_prop) continuous_const).inter
    ((isClosed_le (show Continuous (fun p : Space => |p 1|) by fun_prop) continuous_const).inter
      (isClosed_le (show Continuous (fun p : Space => |p 2|) by fun_prop) continuous_const))

theorem closedTube_subset_prism {δ a b : ℝ} (e : AffineIsometryEquiv ℝ Space Space)
    {x v : Space} (hT : Tube δ x v ⊆ e '' StandardPrism a b) :
    closedTube δ x v ⊆ e '' StandardPrism a b :=
  closure_minimal hT (e.toHomeomorph.isClosedMap _ (standardPrism_closed a b))

theorem flat_direction_data {δ a b : ℝ} (hδ : 0 < δ) (ha : 0 < a) (hb : 0 < b)
    (haSmall : a ≤ 1 / 100) (hb2 : b ≤ 2) (e : AffineIsometryEquiv ℝ Space Space)
    (x v : Space) (hv : ‖v‖ = 1) (hT : Tube δ x v ⊆ e '' StandardPrism a b) :
    |(flatMap e a b ha hb).linear v 0| ≤ 1 / 2 ∧
    ∃ j : Fin 3, j ≠ 0 ∧ 1 / 32 ≤ |(flatMap e a b ha hb).linear v j| := by
  let w := e.symm.linearIsometryEquiv v
  have hw : ‖w‖ = 1 := by simpa [w] using hv
  have he : e.symm (x + v) - e.symm x = w := by
    have hh := e.symm.map_vadd x v
    simpa only [vadd_eq_add, add_comm, sub_eq_iff_eq_add] using hh
  have hleft := hT (self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v)))
  have hright := hT (self_subset_thickening hδ _ (right_mem_segment ℝ x (x + v)))
  have hl : e.symm x ∈ StandardPrism a b := by
    obtain ⟨p, hp, rfl⟩ := hleft
    simpa using hp
  have hr : e.symm (x + v) ∈ StandardPrism a b := by
    obtain ⟨p, hp, heq⟩ := hright
    rw [← heq, e.symm_apply_apply]
    exact hp
  have hw0 : |w 0| ≤ 2 * a := by
    rw [← he]
    change |e.symm (x + v) 0 - e.symm x 0| ≤ 2 * a
    have hh := add_le_add hr.1 hl.1
    exact (abs_sub _ _).trans (by convert hh using 1 <;> ring)
  have h0 : |(flatMap e a b ha hb).linear v 0| ≤ 1 / 2 := by
    rw [flatMap_linear, abs_mul, abs_of_pos (flatScales_pos ha hb 0)]
    change 1 / (4 * a) * |w 0| ≤ 1 / 2
    apply (mul_le_mul_of_nonneg_left hw0 (by positivity)).trans_eq
    field_simp
    norm_num
  refine ⟨h0, ?_⟩
  have hw12 : 1 / 4 ≤ |w 1| ∨ 1 / 4 ≤ |w 2| := by
    by_contra hh
    push_neg at hh
    have hsq := norm_sq_coords w
    rw [hw] at hsq
    have hsq0 := sq_le_sq' (abs_le.mp hw0).1 (abs_le.mp hw0).2
    have hsq1 := sq_le_sq' (abs_le.mp hh.1.le).1 (abs_le.mp hh.1.le).2
    have hsq2 := sq_le_sq' (abs_le.mp hh.2.le).1 (abs_le.mp hh.2.le).2
    nlinarith
  rcases hw12 with hw1 | hw2
  · refine ⟨1, by decide, ?_⟩
    rw [flatMap_linear, abs_mul, abs_of_pos (flatScales_pos ha hb 1)]
    change 1 / 32 ≤ 1 / (4 * b) * |w 1|
    have hh : 1 / 8 ≤ 1 / (4 * b) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
    nlinarith [mul_le_mul_of_nonneg_right hh (abs_nonneg (w 1))]
  · refine ⟨2, by decide, ?_⟩
    rw [flatMap_linear, abs_mul, abs_of_pos (flatScales_pos ha hb 2)]
    change 1 / 32 ≤ 1 / 8 * |w 2|
    linarith

theorem flatMap_tube_width {δ a b : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a)
    (hab : a ≤ b) (haSmall : a ≤ 1 / 100) (hb2 : b ≤ 2)
    (e : AffineIsometryEquiv ℝ Space Space) (x v : Space) (hv : ‖v‖ = 1)
    (hT : Tube δ x v ⊆ e '' StandardPrism a b) :
    WideSection (flatMap e a b (hδ.trans_le hδa) (hδ.trans_le (hδa.trans hab)) ''
      closedTube δ x v) (δ / (1024 * a)) := by
  let ha := hδ.trans_le hδa
  let hb := hδ.trans_le (hδa.trans hab)
  let f := flatMap e a b ha hb
  let e₀ := EuclideanSpace.basisFun (Fin 3) ℝ 0
  let ξ := e.linearIsometryEquiv e₀
  have hξ : ‖ξ‖ = 1 := by simp [ξ, e₀, OrthonormalBasis.norm_eq_one]
  have hfξ : f.linear ξ = (1 / (4 * a)) • e₀ := by
    ext i
    rw [flatMap_linear]
    change flatScales a b i * e.linearIsometryEquiv.symm (e.linearIsometryEquiv e₀) i = _
    rw [LinearIsometryEquiv.symm_apply_apply]
    fin_cases i <;> simp [flatScales, e₀, EuclideanSpace.basisFun_apply]
  obtain ⟨h0, j, hj, hjv⟩ := flat_direction_data hδ ha hb haSmall hb2 e x v hv hT
  have hdiamond : ∀ s t : ℝ, |s| + |t| ≤ δ / (16 * a) →
      f (x + (1 / 2 : ℝ) • v) + s • e₀ + t • f.linear v ∈ f '' closedTube δ x v := by
    intro s t hst
    have hs : |s| ≤ δ / (16 * a) := by linarith [abs_nonneg t]
    have ht : |t| ≤ 1 / 16 := by
      have hr : δ / (16 * a) ≤ 1 / 16 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith [abs_nonneg s]
    let p := x + (1 / 2 + t) • v + (4 * a * s) • ξ
    have hseg : x + (1 / 2 + t) • v ∈ segment ℝ x (x + v) := by
      rw [segment_eq_image']
      refine ⟨1 / 2 + t, ⟨?_, ?_⟩, by simp⟩ <;> linarith [(abs_le.mp ht).1, (abs_le.mp ht).2]
    have hp : p ∈ closedTube δ x v := by
      apply tube_subset_closedTube
      apply mem_thickening_iff.mpr
      refine ⟨_, hseg, ?_⟩
      change dist (x + (1 / 2 + t) • v + (4 * a * s) • ξ) (x + (1 / 2 + t) • v) < δ
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hξ, mul_one, Real.norm_eq_abs,
        abs_mul, abs_of_pos (by positivity : 0 < 4 * a)]
      have hh := (le_div_iff₀ (by positivity : 0 < 16 * a)).mp hs
      nlinarith
    refine ⟨p, hp, ?_⟩
    have hmap (q z : Space) : f (q + z) = f q + f.linear z := by
      simpa only [vadd_eq_add, add_comm] using f.map_vadd q z
    have hm : p = (x + (1 / 2 : ℝ) • v) + (t • v + (4 * a * s) • ξ) := by
      dsimp [p]; module
    rw [hm, hmap, f.linear.map_add, f.linear.map_smul, f.linear.map_smul, hfξ, smul_smul]
    have he : (4 * a * s) * (1 / (4 * a)) = s := by field_simp
    rw [he]
    abel
  have hwidth := wideSection_of_coordinate_pair (by positivity : 0 ≤ δ / (16 * a))
    (f (x + (1 / 2 : ℝ) • v)) (f.linear v) h0 hj hjv hdiamond
  convert hwidth using 1 <;> ring

end
end WangZahlLot.Obl.wz_flat_factored_improvement
