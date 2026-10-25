-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_concentrated_convex_factorization.Prism.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Coefficient
import Submission.WZ.Obl.wz_unit_segment_convex_slab_cover.Geometry

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace WangZahlLot.Obl.wz_concentrated_convex_factorization

open Set MeasureTheory Metric
open scoped ENNReal

noncomputable section

abbrev Frame := OrthonormalBasis (Fin 3) ℝ Space

/-- The first frame vector is longitudinal; the third is the narrow transverse direction. -/
def prism (b : Frame) (z : Space) (a c : ℝ) : Set Space :=
  {p | |inner ℝ (b 0) (p - z)| ≤ 2 ∧
       |inner ℝ (b 1) (p - z)| ≤ c ∧ |inner ℝ (b 2) (p - z)| ≤ a}

lemma prism_mono (b : Frame) (z : Space) {a c a' c' : ℝ}
    (ha : a ≤ a') (hc : c ≤ c') : prism b z a c ⊆ prism b z a' c' := by
  rintro p ⟨h0, h1, h2⟩
  exact ⟨h0, h1.trans hc, h2.trans ha⟩

lemma prism_volume (b : Frame) (z : Space) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    volume (prism b z a c) = ENNReal.ofReal (16 * a * c) := by
  let d : Fin 3 → ℝ := ![2, c, a]
  have he : prism b z a c = {p : Space | ∀ i, -d i ≤ b.repr (p - z) i ∧
      b.repr (p - z) i ≤ d i} := by
    ext p
    simp only [mem_ofPred_eq, OrthonormalBasis.repr_apply_apply]
    constructor
    · rintro ⟨h0, h1, h2⟩ i
      fin_cases i
      · exact abs_le.mp h0
      · exact abs_le.mp h1
      · exact abs_le.mp h2
    · intro h
      exact ⟨abs_le.mpr (h 0), abs_le.mpr (h 1), abs_le.mpr (h 2)⟩
  rw [he, WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.coordinate_box_volume]
  simp only [Fin.prod_univ_three]
  change ENNReal.ofReal (2 - -2) * ENNReal.ofReal (c - -c) *
    ENNReal.ofReal (a - -a) = _
  simp only [sub_neg_eq_add]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

lemma prism_convex (b : Frame) (z : Space) (a c : ℝ) : Convex ℝ (prism b z a c) := by
  have hc' (i : Fin 3) (r : ℝ) : Convex ℝ {p : Space | |inner ℝ (b i) (p - z)| ≤ r} := by
    have he : {p : Space | |inner ℝ (b i) (p - z)| ≤ r} =
        {p | -r + inner ℝ (b i) z ≤ inner ℝ (b i) p} ∩
          {p | inner ℝ (b i) p ≤ r + inner ℝ (b i) z} := by
      ext p
      simp only [mem_ofPred_eq, mem_inter_iff, inner_sub_right, abs_le]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    rw [he]
    exact (convex_halfSpace_ge (innerSL ℝ (b i)).toLinearMap.isLinear _).inter
      (convex_halfSpace_le (innerSL ℝ (b i)).toLinearMap.isLinear _)
  exact (hc' 0 2).inter ((hc' 1 c).inter (hc' 2 a))

lemma prism_image (b : Frame) (z : Space) (a c : ℝ) :
    ∃ e : AffineIsometryEquiv ℝ Space Space,
      prism b z a c = e '' {p : Space | |p 0| ≤ a ∧ |p 1| ≤ c ∧ |p 2| ≤ 2} := by
  let b' := b.reindex (Equiv.swap (0 : Fin 3) 2)
  let e : AffineIsometryEquiv ℝ Space Space :=
    b'.repr.symm.toAffineIsometryEquiv.trans (AffineIsometryEquiv.vaddConst ℝ z)
  refine ⟨e, ?_⟩
  have he (p : Space) : e p = b'.repr.symm p + z := rfl
  have hb0 : b' 0 = b 2 := by simp [b', OrthonormalBasis.reindex_apply]
  have hb1 : b' 1 = b 1 := by
    simp [b', OrthonormalBasis.reindex_apply, Equiv.swap_apply_def]
  have hb2 : b' 2 = b 0 := by simp [b', OrthonormalBasis.reindex_apply]
  ext p
  constructor
  · intro hp
    refine ⟨b'.repr (p - z), ?_, ?_⟩
    · change |b'.repr (p - z) 0| ≤ a ∧ |b'.repr (p - z) 1| ≤ c ∧
        |b'.repr (p - z) 2| ≤ 2
      simp only [OrthonormalBasis.repr_apply_apply, hb0, hb1, hb2]
      exact ⟨hp.2.2, hp.2.1, hp.1⟩
    · rw [he, b'.repr.symm_apply_apply, sub_add_cancel]
  · rintro ⟨q, hq, rfl⟩
    have hp (i : Fin 3) : inner ℝ (b' i) (e q - z) = q i := by
      rw [← OrthonormalBasis.repr_apply_apply, he, add_sub_cancel_right,
        b'.repr.apply_symm_apply]
    change |inner ℝ (b 0) (e q - z)| ≤ 2 ∧ |inner ℝ (b 1) (e q - z)| ≤ c ∧
      |inner ℝ (b 2) (e q - z)| ≤ a
    rw [← hb2, ← hb1, ← hb0, hp, hp, hp]
    exact ⟨hq.2.2, hq.2.1, hq.1⟩

lemma tube_prism {δ : ℝ} (hδ : δ ≤ 1) (x : Space) {v : Space} (hv : ‖v‖ = 1) :
    ∃ b : Frame, Tube δ x v ⊆ prism b x δ δ := by
  obtain ⟨b, hb⟩ := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.exists_basis_first hv
  refine ⟨b, ?_⟩
  intro p hp
  have htrans (i : Fin 3) (hi : i ≠ 0) : |inner ℝ (b i) (p - x)| ≤ δ := by
    have hi0 : inner ℝ (b i) v = 0 := by
      rw [← hb, orthonormal_iff_ite.mp b.orthonormal]
      simp [hi]
    simpa only [inner_sub_right, mem_ofPred_eq] using
      WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.tube_subset_slab
        (b.norm_eq_one i) hi0 x δ hp
  refine ⟨?_, htrans 1 (by decide), htrans 2 (by decide)⟩
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq
  have hi := abs_real_inner_le_norm (b 0) (p - (x + t • v))
  rw [b.norm_eq_one, one_mul, ← dist_eq_norm] at hi
  have he : inner ℝ (b 0) (p - x) = inner ℝ (b 0) (p - (x + t • v)) + t := by
    rw [hb]
    simp [inner_sub_right, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hv]
    ring
  rw [he]
  have ht' : |t| ≤ 1 := by simpa [abs_of_nonneg ht.1] using ht.2
  exact (abs_add_le _ _).trans (by linarith [hi.trans hpq.le])

/-- Removing a component in a unit direction does not increase norm. -/
def transverse (v y : Space) : Space := y - inner ℝ v y • v

lemma transverse_inner {v : Space} (hv : ‖v‖ = 1) (y : Space) :
    inner ℝ v (transverse v y) = 0 := by
  simp [transverse, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hv]

lemma transverse_norm_le {v : Space} (hv : ‖v‖ = 1) (y : Space) :
    ‖transverse v y‖ ≤ ‖y‖ := by
  have he : ‖transverse v y‖ ^ 2 = ‖y‖ ^ 2 - (inner ℝ v y) ^ 2 := by
    rw [transverse, norm_sub_sq_real]
    simp [norm_smul, Real.norm_eq_abs, real_inner_smul_right, real_inner_comm y v, hv,
      sq_abs]
    ring
  nlinarith [sq_nonneg (inner ℝ v y), norm_nonneg (transverse v y), norm_nonneg y]

lemma transverse_eval {v u : Space} (huv : inner ℝ u v = 0) (y : Space) :
    inner ℝ u (transverse v y) = inner ℝ u y := by
  simp [transverse, inner_sub_right, inner_smul_right, huv]

lemma abs_inner_le_transverse {v u : Space} (hu : ‖u‖ = 1)
    (huv : inner ℝ u v = 0) (y : Space) : |inner ℝ u y| ≤ ‖transverse v y‖ := by
  simpa [transverse_eval huv, hu] using abs_real_inner_le_norm u (transverse v y)

end
end WangZahlLot.Obl.wz_concentrated_convex_factorization
