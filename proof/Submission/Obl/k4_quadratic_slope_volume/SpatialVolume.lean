import Mathlib
import Submission.Obl.k4_quadratic_slope_volume.PolynomialSlices

namespace Submission.Obl.k4_quadratic_slope_volume

open Set MeasureTheory
open scoped ENNReal

/-- The moving horizontal box has area proportional to `|det D|`. -/
theorem volume_ellipse (D : Matrix (Fin 2) (Fin 2) ℝ) (hD : D.det ≠ 0)
    (c : EuclideanSpace ℝ (Fin 2)) (K : ℝ) (hK : 0 ≤ K) :
    volume {y : EuclideanSpace ℝ (Fin 2) | ‖(D⁻¹).toEuclideanLin (y - c)‖ ≤ K} =
      ENNReal.ofReal (Real.pi * K ^ 2 * |D.det|) := by
  have hdet : ((D⁻¹).toEuclideanLin).det = D.det⁻¹ := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin,
      Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  have heq : {y : EuclideanSpace ℝ (Fin 2) | ‖(D⁻¹).toEuclideanLin (y - c)‖ ≤ K} =
      (fun y => y + -c) ⁻¹' ((D⁻¹).toEuclideanLin ⁻¹' Metric.closedBall 0 K) := by
    ext y
    simp [sub_eq_add_neg]
  rw [heq, measure_preimage_add_right volume (-c),
    Measure.addHaar_preimage_linearMap volume (by rw [hdet]; exact inv_ne_zero hD),
    hdet, inv_inv, EuclideanSpace.volume_closedBall_fin_two]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow hK]
  ring

/-- A coordinate form of the same area estimate. -/
theorem volume_coordinate_ellipse (D : Matrix (Fin 2) (Fin 2) ℝ) (hD : D.det ≠ 0)
    (c u : EuclideanSpace ℝ (Fin 2)) (t K : ℝ) (hK : 0 ≤ K) :
    volume {y : Fin 2 → ℝ | ‖(D⁻¹).toEuclideanLin
      (WithLp.toLp 2 (fun i => y i - c i - t * u i))‖ ≤ K} =
      ENNReal.ofReal (Real.pi * K ^ 2 * |D.det|) := by
  have heq : {y : Fin 2 → ℝ | ‖(D⁻¹).toEuclideanLin
      (WithLp.toLp 2 (fun i => y i - c i - t * u i))‖ ≤ K} =
      WithLp.toLp 2 ⁻¹' {y : EuclideanSpace ℝ (Fin 2) |
        ‖(D⁻¹).toEuclideanLin (y - (c + t • u))‖ ≤ K} := by
    ext y
    have hv : WithLp.toLp 2 (fun i => y i - c i - t * u i) =
        WithLp.toLp 2 y - (c + t • u) := by
      ext i
      simp
      ring
    simp only [mem_ofPred_eq, mem_preimage, hv]
  rw [heq, (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurableEmbedding]
  exact volume_ellipse D hD _ K hK

/-- Fiberwise quadratic sublevel bounds control a three-dimensional spatial
slice over an arbitrary measurable horizontal region. -/
theorem volume_quadratic_slice_over_base (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (t ε β : ℝ) (hε : 0 ≤ ε) (hβ : 0 < β)
    (B : Set (Fin 2 → ℝ)) (hB : MeasurableSet B) :
    volume {z : (Fin 2 → ℝ) × ℝ | z.1 ∈ B ∧
      |MvPolynomial.eval ![t, z.1 0, z.1 1, z.2] P| ≤ ε ∧
      β ≤ |MvPolynomial.eval ![t, z.1 0, z.1 1, z.2]
        (MvPolynomial.pderiv (3 : Fin 4) P)|} ≤
      ENNReal.ofReal (4 * ε / β) * volume B := by
  classical
  let S : Set ((Fin 2 → ℝ) × ℝ) := {z | z.1 ∈ B ∧
      |MvPolynomial.eval ![t, z.1 0, z.1 1, z.2] P| ≤ ε ∧
      β ≤ |MvPolynomial.eval ![t, z.1 0, z.1 1, z.2]
        (MvPolynomial.pderiv (3 : Fin 4) P)|}
  have hcont (Q : MvPolynomial (Fin 4) ℝ) :
      Continuous (fun z : (Fin 2 → ℝ) × ℝ => MvPolynomial.eval ![t, z.1 0, z.1 1, z.2] Q) := by
    apply Q.continuous_eval.comp
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  have hS : MeasurableSet S := (hB.preimage measurable_fst).inter
    ((measurableSet_le (hcont P).abs.measurable measurable_const).inter
      (measurableSet_le measurable_const (hcont _).abs.measurable))
  have hfiber (y : Fin 2 → ℝ) :
      volume {w : ℝ | |MvPolynomial.eval ![t, y 0, y 1, w] P| ≤ ε ∧
        β ≤ |MvPolynomial.eval ![t, y 0, y 1, w] (MvPolynomial.pderiv (3 : Fin 4) P)|} ≤
        ENNReal.ofReal (4 * ε / β) := by
    have hv (w : ℝ) : Function.update ![t, y 0, y 1, (0 : ℝ)] (3 : Fin 4) w =
        ![t, y 0, y 1, w] := by
      funext i
      fin_cases i <;> dsimp <;> simp
    simpa only [hv] using volume_quadratic_coordinate_sublevel P hP
      ![t, y 0, y 1, (0 : ℝ)] (3 : Fin 4) ε β hε hβ
  change ((volume : Measure (Fin 2 → ℝ)).prod (volume : Measure ℝ)) S ≤ _
  rw [Measure.prod_apply hS, ← lintegral_indicator_const hB]
  apply lintegral_mono
  intro y
  by_cases hy : y ∈ B
  · simpa [S, hy] using hfiber y
  · simp [S, hy]

/-- In product coordinates, each allowed spatial slice has volume at most an
absolute constant times `K^4 * a * |det D|`. -/
theorem volume_quadratic_slice_product (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (D : Matrix (Fin 2) (Fin 2) ℝ) (hD : D.det ≠ 0)
    (c u : EuclideanSpace ℝ (Fin 2)) (t a K : ℝ) (ha : 0 < a) (hK : 1 ≤ K) :
    volume {z : (Fin 2 → ℝ) × ℝ |
      ‖(D⁻¹).toEuclideanLin (WithLp.toLp 2 (fun i => z.1 i - c i - t * u i))‖ ≤ K ∧
      |MvPolynomial.eval ![t, z.1 0, z.1 1, z.2] P| ≤ K * a ∧
      K⁻¹ / 16 ≤ |MvPolynomial.eval ![t, z.1 0, z.1 1, z.2]
        (MvPolynomial.pderiv (3 : Fin 4) P)|} ≤
      ENNReal.ofReal (64 * Real.pi * K ^ 4 * a * |D.det|) := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let B : Set (Fin 2 → ℝ) := {y | ‖(D⁻¹).toEuclideanLin
    (WithLp.toLp 2 (fun i => y i - c i - t * u i))‖ ≤ K}
  have hB : MeasurableSet B := by
    have hcoord : Continuous (fun y : Fin 2 → ℝ =>
        WithLp.toLp 2 (fun i => y i - c i - t * u i)) := by fun_prop
    have hlin : Continuous (D⁻¹).toEuclideanLin := LinearMap.continuous_of_finiteDimensional _
    exact (isClosed_le (hlin.comp hcoord).norm continuous_const).measurableSet
  have h := volume_quadratic_slice_over_base P hP t (K * a) (K⁻¹ / 16)
    (by positivity) (by positivity) B hB
  change volume _ ≤ _ at h
  calc
    volume {z : (Fin 2 → ℝ) × ℝ |
      ‖(D⁻¹).toEuclideanLin (WithLp.toLp 2 (fun i => z.1 i - c i - t * u i))‖ ≤ K ∧
      |MvPolynomial.eval ![t, z.1 0, z.1 1, z.2] P| ≤ K * a ∧
      K⁻¹ / 16 ≤ |MvPolynomial.eval ![t, z.1 0, z.1 1, z.2]
        (MvPolynomial.pderiv (3 : Fin 4) P)|} ≤
        ENNReal.ofReal (4 * (K * a) / (K⁻¹ / 16)) * volume B := h
    _ = ENNReal.ofReal (64 * Real.pi * K ^ 4 * a * |D.det|) := by
      rw [volume_coordinate_ellipse D hD c u t K hKpos.le,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      ring

/-- The allowed spatial region in the Euclidean coordinates used by the frozen
slope-volume statement. -/
theorem volume_quadratic_spatial_slice (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (D : Matrix (Fin 2) (Fin 2) ℝ) (hD : D.det ≠ 0)
    (c u : EuclideanSpace ℝ (Fin 2)) (t a K : ℝ) (ha : 0 < a) (hK : 1 ≤ K) :
    volume {x : EuclideanSpace ℝ (Fin 3) |
      ‖(D⁻¹).toEuclideanLin (WithLp.toLp 2 (fun i => x i.castSucc - c i - t * u i))‖ ≤ K ∧
      |MvPolynomial.eval ![t, x 0, x 1, x 2] P| ≤ K * a ∧
      K⁻¹ / 16 ≤ |MvPolynomial.eval ![t, x 0, x 1, x 2]
        (MvPolynomial.pderiv (3 : Fin 4) P)|} ≤
      ENNReal.ofReal (64 * Real.pi * K ^ 4 * a * |D.det|) := by
  let e : (Fin 3 → ℝ) ≃ᵐ ((Fin 2 → ℝ) × ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)).trans
      MeasurableEquiv.prodComm
  have he : MeasurePreserving e :=
    Measure.measurePreserving_swap.comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2))
  have he_apply (x : Fin 3 → ℝ) : e x = ((fun i : Fin 2 => x i.castSucc), x 2) := by
    change ((fun i : Fin 2 => x ((Fin.last 2).succAbove i)), x (Fin.last 2)) = _
    rw [Fin.succAbove_last]
    rfl
  let T : Set ((Fin 2 → ℝ) × ℝ) := {z |
      ‖(D⁻¹).toEuclideanLin (WithLp.toLp 2 (fun i => z.1 i - c i - t * u i))‖ ≤ K ∧
      |MvPolynomial.eval ![t, z.1 0, z.1 1, z.2] P| ≤ K * a ∧
      K⁻¹ / 16 ≤ |MvPolynomial.eval ![t, z.1 0, z.1 1, z.2]
        (MvPolynomial.pderiv (3 : Fin 4) P)|}
  have hset : {x : EuclideanSpace ℝ (Fin 3) |
      ‖(D⁻¹).toEuclideanLin (WithLp.toLp 2 (fun i => x i.castSucc - c i - t * u i))‖ ≤ K ∧
      |MvPolynomial.eval ![t, x 0, x 1, x 2] P| ≤ K * a ∧
      K⁻¹ / 16 ≤ |MvPolynomial.eval ![t, x 0, x 1, x 2]
        (MvPolynomial.pderiv (3 : Fin 4) P)|} = WithLp.ofLp ⁻¹' (e ⁻¹' T) := by
    ext x
    simp only [mem_preimage, he_apply, T, mem_ofPred_eq]
    rfl
  rw [hset, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding,
    he.measure_preimage_emb e.measurableEmbedding]
  exact volume_quadratic_slice_product P hP D hD c u t a K ha hK

end Submission.Obl.k4_quadratic_slope_volume
