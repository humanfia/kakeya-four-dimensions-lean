-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.CoarseGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Prisms
import Submission.WZ.Obl.wz_transverse_cell_weighted_cover

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set Metric
open scoped Pointwise

noncomputable section

abbrev prismFrame (e : AffineIsometryEquiv ℝ Space Space) : Fin 3 → Space :=
  fun i => e.linearIsometryEquiv (EuclideanSpace.single i 1)

theorem prismFrame_orthonormal (e : AffineIsometryEquiv ℝ Space Space) :
    Orthonormal ℝ (prismFrame e) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [prismFrame, e.linearIsometryEquiv.inner_map_map]
  exact orthonormal_iff_ite.mp EuclideanSpace.orthonormal_single i j

theorem prismFrame_coordinates (e : AffineIsometryEquiv ℝ Space Space)
    (p : Space) (i : Fin 3) : inner ℝ (prismFrame e i) (e p - e 0) = p i := by
  have he : e p - e 0 = e.linearIsometryEquiv p := by
    simpa using (e.map_vsub p 0).symm
  rw [he]
  simp [prismFrame, EuclideanSpace.inner_single_left]

theorem standardPrism_norm_le {a b : ℝ} (ha : a ≤ 1) (hb : b ≤ 1)
    {p : Space} (hp : p ∈ standardPrism a b) : ‖p‖ ≤ 4 := by
  have h0 : |p 0| ≤ 1 := hp.1.trans ha
  have h1 : |p 1| ≤ 1 := hp.2.1.trans hb
  have h2 := hp.2.2
  have hs := EuclideanSpace.real_norm_sq_eq p
  rw [Fin.sum_univ_three] at hs
  have hs0 := sq_le_sq' (abs_le.mp h0).1 (abs_le.mp h0).2
  have hs1 := sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
  have hs2 := sq_le_sq' (abs_le.mp h2).1 (abs_le.mp h2).2
  nlinarith [norm_nonneg p]

theorem prism_center_norm_lt {a b : ℝ} (ha : a ≤ 1) (hb : b ≤ 1)
    (e : AffineIsometryEquiv ℝ Space Space)
    (hmeet : (e '' standardPrism a b ∩ unitBall).Nonempty) : ‖e 0‖ < 5 := by
  obtain ⟨_, ⟨p, hp, rfl⟩, hB⟩ := hmeet
  have hd : dist (e 0) (e p) ≤ 4 := by
    simpa using standardPrism_norm_le ha hb hp
  have hn : ‖e p‖ < 1 := mem_ball_zero_iff.mp hB
  have ht := norm_le_norm_add_norm_sub (e p) (e 0)
  rw [← dist_eq_norm, dist_comm (e p) (e 0)] at ht
  linarith

theorem normalized_prism_subset {a b κ : ℝ} (hκ : 0 ≤ κ) (hκmax : κ ≤ 1 / 1000000)
    (e : AffineIsometryEquiv ℝ Space Space) :
    (fun p : Space => κ • p) '' (e '' standardPrism a b) ⊆
      WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism (κ * a) (κ * b)
        (κ • e 0) (prismFrame e) := by
  rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
  have hc (i : Fin 3) :
      |inner ℝ (prismFrame e i) (κ • e p - κ • e 0)| = κ * |p i| := by
    rw [← smul_sub, inner_smul_right, prismFrame_coordinates, abs_mul, abs_of_nonneg hκ]
  change _ ∧ _ ∧ _
  rw [hc 0, hc 1, hc 2]
  refine ⟨mul_le_mul_of_nonneg_left hp.1 hκ,
    mul_le_mul_of_nonneg_left hp.2.1 hκ, ?_⟩
  have := mul_le_mul_of_nonneg_left hp.2.2 hκ
  linarith

theorem volume_smul_image {κ : ℝ} (hκ : 0 ≤ κ) (S : Set Space) :
    volume ((fun p : Space => κ • p) '' S) = ENNReal.ofReal (κ ^ 3) * volume S := by
  change volume (κ • S) = _
  rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, abs_of_nonneg (pow_nonneg hκ _)]

theorem volume_smul_preimage {κ : ℝ} (hκ : 0 < κ) (S : Set Space) :
    volume ((fun p : Space => κ • p) ⁻¹' S) = ENNReal.ofReal (κ⁻¹ ^ 3) * volume S := by
  rw [show (fun p : Space => κ • p) ⁻¹' S = (fun p : Space => κ⁻¹ • p) '' S by
    ext p
    constructor
    · intro hp
      exact ⟨κ • p, hp, inv_smul_smul₀ hκ.ne' p⟩
    · rintro ⟨q, hq, rfl⟩
      simpa [smul_smul, hκ.ne'] using hq]
  exact volume_smul_image (inv_nonneg.mpr hκ.le) S

theorem tube_volume_upper {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (x v : Space) (hv : ‖v‖ = 1) : volume (tube r x v) ≤ ENNReal.ofReal (56 * r ^ 2) := by
  have hseg : segment ℝ x (x + v) ⊆ segment ℝ x (x + (6 : ℝ) • v) := by
    rw [segment_eq_image', segment_eq_image']
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨t / 6, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    simp only [add_sub_cancel_left]
    module
  have hsub := thickening_subset_of_subset r hseg
  apply (measure_mono hsub).trans
  apply (WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.cylinder_volume_le hv x hr).trans
  apply ENNReal.ofReal_le_ofReal
  nlinarith [sq_nonneg r]

theorem tube_convex (r : ℝ) (x v : Space) : Convex ℝ (tube r x v) :=
  (convex_segment x (x + v)).thickening r

theorem prism_neighborhood_coordinates {a b r : ℝ}
    (e : AffineIsometryEquiv ℝ Space Space) {p : Space}
    (hp : p ∈ thickening r (e '' standardPrism a b)) :
    |inner ℝ (prismFrame e 0) (p - e 0)| ≤ a + r ∧
    |inner ℝ (prismFrame e 1) (p - e 0)| ≤ b + r ∧
    |inner ℝ (prismFrame e 2) (p - e 0)| ≤ 2 + r := by
  obtain ⟨_, ⟨q, hq, rfl⟩, hpq⟩ := mem_thickening_iff.mp hp
  have hcoord (i : Fin 3) (B : ℝ) (h : |q i| ≤ B) :
      |inner ℝ (prismFrame e i) (p - e 0)| ≤ B + r := by
    have hn : ‖prismFrame e i‖ = 1 := (prismFrame_orthonormal e).norm_eq_one i
    have he : p - e 0 = (p - e q) + (e q - e 0) := by module
    rw [he, inner_add_right, prismFrame_coordinates]
    have hi := abs_real_inner_le_norm (prismFrame e i) (p - e q)
    rw [hn, one_mul, ← dist_eq_norm] at hi
    exact (abs_add_le _ _).trans (by linarith)
  exact ⟨hcoord 0 a hq.1, hcoord 1 b hq.2.1, hcoord 2 2 hq.2.2⟩

theorem prism_neighborhood_volume {a b : ℝ} (hab : a ≤ b) (hb1 : b ≤ 1)
    (e : AffineIsometryEquiv ℝ Space Space) :
    volume (thickening (2 * b) (e '' standardPrism a b)) ≤ ENNReal.ofReal (288 * b ^ 2) := by
  have h := WangZahlLot.Obl.wz_transverse_cell_weighted_cover.volume_le_of_coords
    (prismFrame_orthonormal e) (fun _ => e 0) ![3 * b, 3 * b, 4]
    (thickening (2 * b) (e '' standardPrism a b)) (by
      intro p hp i
      have hc := prism_neighborhood_coordinates e hp
      fin_cases i
      · change |inner ℝ (prismFrame e 0) (p - e 0)| ≤ 3 * b
        linarith [hc.1]
      · change |inner ℝ (prismFrame e 1) (p - e 0)| ≤ 3 * b
        linarith [hc.2.1]
      · change |inner ℝ (prismFrame e 2) (p - e 0)| ≤ 4
        linarith [hc.2.2])
  change volume _ ≤ ENNReal.ofReal (8 * (3 * b * (3 * b) * 4)) at h
  convert h using 1 <;> congr 1 <;> ring

theorem normalized_prism_neighborhood_subset {a b κ : ℝ}
    (hab : a ≤ b) (hb1 : b ≤ 1) (hκ : 0 ≤ κ) (hκmax : κ ≤ 1 / 100000000)
    (e : AffineIsometryEquiv ℝ Space Space) :
    (fun p : Space => κ • p) '' thickening (2 * b) (e '' standardPrism a b) ⊆
      WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism (3 * κ * b) (3 * κ * b)
        (κ • e 0) (prismFrame e) := by
  rintro _ ⟨p, hp, rfl⟩
  have hc := prism_neighborhood_coordinates e hp
  have he (i : Fin 3) : |inner ℝ (prismFrame e i) (κ • p - κ • e 0)| =
      κ * |inner ℝ (prismFrame e i) (p - e 0)| := by
    rw [← smul_sub, inner_smul_right, abs_mul, abs_of_nonneg hκ]
  change _ ∧ _ ∧ _
  rw [he 0, he 1, he 2]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hc.1 hκ,
      mul_le_mul_of_nonneg_left hab hκ]
  · nlinarith [mul_le_mul_of_nonneg_left hc.2.1 hκ]
  · nlinarith [mul_le_mul_of_nonneg_left hc.2.2 hκ,
      mul_le_mul_of_nonneg_left hb1 hκ]

end

end WangZahlLot.Obl.wz_nonflat_factored_improvement
