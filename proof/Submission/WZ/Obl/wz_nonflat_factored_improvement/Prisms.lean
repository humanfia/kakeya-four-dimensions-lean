-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.Prisms.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Basic
import Submission.WZ.Obl.wz_frostman_rigid_copies_volume
import Submission.WZ.Obl.wz_affine_robust_cluster_estimate

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (pd areaSq pd_sq_le_areaSq pd_nonneg)

/-- The model prism is convex, including degenerate choices of its widths. -/
theorem standardPrism_convex (a b : ℝ) : Convex ℝ (standardPrism a b) := by
  intro x hx y hy t s ht hs hts
  have hcoord (i : Fin 3) (B : ℝ) (hx : |x i| ≤ B) (hy : |y i| ≤ B) :
      |(t • x + s • y) i| ≤ B := by
    change |t * x i + s * y i| ≤ B
    calc
      _ ≤ |t * x i| + |s * y i| := abs_add_le _ _
      _ = t * |x i| + s * |y i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ht, abs_of_nonneg hs]
      _ ≤ t * B + s * B := by gcongr
      _ = B := by rw [← add_mul, hts, one_mul]
  exact ⟨hcoord 0 a hx.1 hy.1, hcoord 1 b hx.2.1 hy.2.1,
    hcoord 2 2 hx.2.2 hy.2.2⟩

theorem standardPrism_eq_preimage (a b : ℝ) :
    standardPrism a b = WithLp.ofLp ⁻¹'
      (Set.pi Set.univ (fun i : Fin 3 => Set.Icc (-(![a, b, 2] i)) (![a, b, 2] i))) := by
  ext p
  simp only [standardPrism, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi,
    Set.mem_univ, forall_true_left, Set.mem_Icc, Fin.forall_fin_succ]
  simp [abs_le]

/-- In the precise normalization of the frozen statement the prism volume is `16ab`. -/
theorem standardPrism_volume {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    volume (standardPrism a b) = ENNReal.ofReal (16 * a * b) := by
  rw [standardPrism_eq_preimage]
  rw [(PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    ((MeasurableSet.univ_pi fun _ => measurableSet_Icc).nullMeasurableSet)]
  rw [volume_pi_pi]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Real.volume_Icc]
  rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ b - -b),
    ← ENNReal.ofReal_mul (by linarith : 0 ≤ a - -a)]
  congr 1
  ring

theorem prism_convex {a b : ℝ} {W : Set Space}
    (hW : ∃ e : AffineIsometryEquiv ℝ Space Space, W = e '' standardPrism a b) :
    Convex ℝ W := by
  obtain ⟨e, rfl⟩ := hW
  exact (standardPrism_convex a b).affine_image e.toAffineEquiv.toAffineMap

theorem prism_volume {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {W : Set Space}
    (hW : ∃ e : AffineIsometryEquiv ℝ Space Space, W = e '' standardPrism a b) :
    volume W = ENNReal.ofReal (16 * a * b) := by
  obtain ⟨e, rfl⟩ := hW
  rw [WangZahlLot.Obl.wz_frostman_rigid_copies_volume.affine_volume_image]
  exact standardPrism_volume ha hb

/-- The convex-count hypothesis bounds the occupancy of each prism in its exact volume units. -/
theorem prism_occupancy_upper {δ a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    {n : ℕ} {x v : Fin n → Space} {W : Set Space}
    (hW : ∃ e : AffineIsometryEquiv ℝ Space Space, W = e '' standardPrism a b)
    (hcount : ConvexCount δ c x v) :
    (Set.ncard {i | tube δ (x i) (v i) ⊆ W} : ℝ) * δ ^ 2 ≤ 16 * c * a * b := by
  have h := hcount W (prism_convex hW)
  rw [prism_volume ha hb hW, ← ENNReal.ofReal_mul hc] at h
  have h' := (ENNReal.ofReal_le_ofReal_iff
    (show 0 ≤ c * (16 * a * b) by positivity)).mp h
  nlinarith

/-- The long axis of the standard prism. -/
noncomputable def prismAxis : Space := EuclideanSpace.single 2 1

theorem prismAxis_unit : ‖prismAxis‖ = 1 := by simp [prismAxis]

/-- Every unit segment in a thin prism has direction within `4b` of its long axis. -/
theorem direction_in_standardPrism {a b : ℝ} (hab : a ≤ b) {x v : Space}
    (hv : ‖v‖ = 1) (h0 : x ∈ standardPrism a b) (h1 : x + v ∈ standardPrism a b) :
    pd v prismAxis ≤ 4 * b := by
  have hb : 0 ≤ b := (abs_nonneg _).trans h0.2.1
  have hcoord (i : Fin 3) (B : ℝ) (hx : |x i| ≤ B) (hy : |(x + v) i| ≤ B) :
      |v i| ≤ 2 * B := by
    calc
      |v i| = |(x + v) i - x i| := by simp
      _ ≤ |(x + v) i| + |x i| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  have hzero : |v 0| ≤ 2 * b := (hcoord 0 a h0.1 h1.1).trans (by linarith)
  have hone : |v 1| ≤ 2 * b := hcoord 1 b h0.2.1 h1.2.1
  have harea := pd_sq_le_areaSq hv prismAxis_unit
  have hareaEq : areaSq v prismAxis = (v 0) ^ 2 + (v 1) ^ 2 := by
    simp [areaSq, prismAxis]
  rw [hareaEq] at harea
  have hzero' : (v 0) ^ 2 ≤ (2 * b) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hzero
  have hone' : (v 1) ^ 2 ≤ (2 * b) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hone
  nlinarith [pd_nonneg v prismAxis]

/-- A prism lies in a cylinder of radius `2b` about its long central segment. -/
theorem standardPrism_subset_capsule {a b : ℝ} (hab : a ≤ b) (hb : 0 < b) :
    standardPrism a b ⊆ Metric.thickening (2 * b)
      (segment ℝ ((-2 : ℝ) • prismAxis) ((2 : ℝ) • prismAxis)) := by
  intro p hp
  refine Metric.mem_thickening_iff.mpr ⟨(p 2) • prismAxis, ?_, ?_⟩
  · rw [segment_eq_image']
    refine ⟨(p 2 + 2) / 4, ?_, ?_⟩
    · rcases abs_le.mp hp.2.2 with ⟨hl, hu⟩
      exact ⟨by linarith, by linarith⟩
    · module
  · rw [dist_eq_norm]
    have hsq : ‖p - (p 2) • prismAxis‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
      rw [WangZahlLot.Obl.wz_affine_robust_cluster_estimate.norm_sq_coords]
      simp [prismAxis]
    have h0 : |p 0| ≤ b := hp.1.trans hab
    have h1 : |p 1| ≤ b := hp.2.1
    have h0' : (p 0) ^ 2 ≤ b ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb.le).mpr h0
    have h1' : (p 1) ^ 2 ≤ b ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb.le).mpr h1
    nlinarith [sq_pos_of_pos hb, norm_nonneg (p - (p 2) • prismAxis)]

/-- The corresponding enclosing cylinder after an arbitrary rigid motion. -/
theorem prism_subset_capsule {a b : ℝ} (hab : a ≤ b) (hb : 0 < b)
    (e : AffineIsometryEquiv ℝ Space Space) :
    e '' standardPrism a b ⊆ Metric.thickening (2 * b)
      (segment ℝ (e ((-2 : ℝ) • prismAxis)) (e ((2 : ℝ) • prismAxis))) := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨q, hq, hpq⟩ := Metric.mem_thickening_iff.mp
    (standardPrism_subset_capsule hab hb hp)
  refine Metric.mem_thickening_iff.mpr ⟨e q, ?_, by simpa using hpq⟩
  have he := image_segment ℝ e.toAffineEquiv.toAffineMap
    ((-2 : ℝ) • prismAxis) ((2 : ℝ) • prismAxis)
  change e '' segment ℝ ((-2 : ℝ) • prismAxis) ((2 : ℝ) • prismAxis) =
    segment ℝ (e ((-2 : ℝ) • prismAxis)) (e ((2 : ℝ) • prismAxis)) at he
  rw [← he]
  exact ⟨q, hq, rfl⟩

end WangZahlLot.Obl.wz_nonflat_factored_improvement
