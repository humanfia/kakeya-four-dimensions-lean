import Submission.Obl.k4_dk4_smoothed_problem.FiniteSmoothing.Smoothing
import Submission.Obl.k4_dk4_smoothed_problem.NativeFormat

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_dk4_smoothed_problem.Framework

abbrev PairCoefficients := (Fin 3 → ℝ) × (Fin 3 → ℝ)

/-- The unobserved index can be held fixed throughout the initial smoothing. -/
noncomputable def packLine (p : PairCoefficients) : Coefficients :=
  (0, concatenateCoefficients 3 3 p)

theorem measurableEmbedding_packLine : MeasurableEmbedding packLine :=
  (concatenateCoefficients 3 3).measurableEmbedding.prodMk_left 0

theorem packLine_coordinate (p : PairCoefficients) (i : Fin 3) :
    (packLine p).2 (Fin.castAdd 3 i) = p.1 i :=
  concatenateCoefficients_castAdd p i

theorem packLine_slope_coordinate (p : PairCoefficients) (i : Fin 3) :
    (packLine p).2 (Fin.natAdd 3 i) = p.2 i :=
  concatenateCoefficients_natAdd p i

theorem packLine_eq_vector (p : PairCoefficients) :
    packLine p = (0, ![p.1 0, p.1 1, p.1 2, p.2 0, p.2 1, p.2 2]) := by
  have hb0 := packLine_coordinate p 0
  have hb1 := packLine_coordinate p 1
  have hb2 := packLine_coordinate p 2
  have hs0 := packLine_slope_coordinate p 0
  have hs1 := packLine_slope_coordinate p 1
  have hs2 := packLine_slope_coordinate p 2
  apply Prod.ext
  · rfl
  · ext j
    fin_cases j <;> simp_all

theorem packLine_trajectory (p : PairCoefficients) (t : ℝ) :
    WithLp.toLp 2 (trajectoryPoint (packLine p) t) =
      FiniteSmoothing.graphLine p.1 p.2 t := by
  have hb0 := packLine_coordinate p 0
  have hb1 := packLine_coordinate p 1
  have hb2 := packLine_coordinate p 2
  have hs0 := packLine_slope_coordinate p 0
  have hs1 := packLine_slope_coordinate p 1
  have hs2 := packLine_slope_coordinate p 2
  ext j
  fin_cases j <;>
    simp_all [trajectoryPoint, FiniteSmoothing.graphLine]

noncomputable def nativePrior {n : ℕ} (r : ℝ)
    (b s : Fin n → Fin 3 → ℝ) : Measure Coefficients :=
  Measure.map packLine (FiniteSmoothing.smoothedPrior r b s)

/-- Identify the helper construction with the entirely expanded Mathlib prior
used in the frozen smoothing children. -/
theorem nativePrior_spatialCoords_eq {n : ℕ} (r : ℝ)
    (x v : Fin n → EuclideanSpace ℝ (Fin 4)) :
    nativePrior r (fun i => FiniteSmoothing.spatialCoords (x i))
        (fun i => FiniteSmoothing.spatialCoords (v i)) =
      Measure.map (fun p : PairCoefficients =>
        ((0 : ℕ), (![p.1 0, p.1 1, p.1 2, p.2 0, p.2 1, p.2 2] : Fin 6 → ℝ)))
        ((n : ENNReal)⁻¹ • ∑ i : Fin n,
          (ProbabilityTheory.cond volume
            (Icc (fun a : Fin 3 => x i a.succ - r) (fun a => x i a.succ + r))).prod
          (ProbabilityTheory.cond volume
            (Icc (fun a : Fin 3 => v i a.succ - r) (fun a => v i a.succ + r)))) := by
  have hcoord (w : EuclideanSpace ℝ (Fin 4)) :
      FiniteSmoothing.spatialCoords w = fun a : Fin 3 => w a.succ := by
    ext a
    fin_cases a <;> rfl
  simp only [nativePrior, FiniteSmoothing.smoothedPrior, FiniteSmoothing.boxLaw,
    FiniteSmoothing.coordBox, hcoord]
  congr 1
  exact funext packLine_eq_vector

theorem nativePrior_probability {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (b s : Fin n → Fin 3 → ℝ) : IsProbabilityMeasure (nativePrior r b s) := by
  letI := FiniteSmoothing.smoothedPrior_isProbabilityMeasure hn hr b s
  exact inferInstanceAs (IsProbabilityMeasure (Measure.map packLine _))

theorem nativePrior_apply {n : ℕ} (r : ℝ) (b s : Fin n → Fin 3 → ℝ)
    (A : Set Coefficients) :
    nativePrior r b s A = FiniteSmoothing.smoothedPrior r b s (packLine ⁻¹' A) :=
  measurableEmbedding_packLine.map_apply _ A

theorem nativePrior_prod_apply {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (b s : Fin n → Fin 3 → ℝ) (A : Set (Coefficients × ℝ)) :
    (nativePrior r b s).prod volume A =
      (FiniteSmoothing.smoothedPrior r b s).prod volume
        ((Prod.map packLine id) ⁻¹' A) := by
  letI := FiniteSmoothing.smoothedPrior_isProbabilityMeasure hn hr b s
  have hmap := Measure.map_prod_map (FiniteSmoothing.smoothedPrior r b s)
    (volume : Measure ℝ) measurableEmbedding_packLine.measurable measurable_id
  rw [Measure.map_id] at hmap
  rw [nativePrior, hmap,
    (measurableEmbedding_packLine.prodMap MeasurableEmbedding.id).map_apply]

noncomputable def componentHeight (n : ℕ) (r : ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ((2 * r) ^ 6)⁻¹

theorem componentHeight_pos {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    0 < componentHeight n r := by
  unfold componentHeight
  positivity

theorem ofReal_componentHeight {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (componentHeight n r) =
      (n : ENNReal)⁻¹ * (ENNReal.ofReal (2 * r) ^ 3)⁻¹ *
        (ENNReal.ofReal (2 * r) ^ 3)⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrR : 0 < 2 * r := by positivity
  rw [componentHeight, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_inv_of_pos hnR, ENNReal.ofReal_natCast,
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow hrR.le]
  rw [show (6 : ℕ) = 3 + 3 from rfl, pow_add,
    ENNReal.mul_inv (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
      (Or.inl (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]
  exact (mul_assoc _ _ _).symm

/-- Each coefficient component is a single box with a constant density height. -/
theorem nativePrior_representation {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (b s : Fin n → Fin 3 → ℝ) :
    nativePrior r b s = ∑ j : Fin n, ENNReal.ofReal (componentHeight n r) •
      Measure.map (fun x : Fin 6 → ℝ => ((0 : ℕ), x))
        (volume.restrict ((concatenateCoefficients 3 3).symm ⁻¹'
          (FiniteSmoothing.coordBox r (b j) ×ˢ FiniteSmoothing.coordBox r (s j)))) := by
  have hprior : FiniteSmoothing.smoothedPrior r b s =
      ∑ j : Fin n, ENNReal.ofReal (componentHeight n r) •
        ((volume.restrict (FiniteSmoothing.coordBox r (b j))).prod
          (volume.restrict (FiniteSmoothing.coordBox r (s j)))) := by
    unfold FiniteSmoothing.smoothedPrior
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [FiniteSmoothing.boxLaw_eq, FiniteSmoothing.boxLaw_eq,
      Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, smul_smul,
      ofReal_componentHeight hn hr]
  rw [nativePrior, hprior]
  exact map_finite_product_prior 0 _ _
    (fun j => FiniteSmoothing.measurableSet_coordBox r (b j))
    (fun j => FiniteSmoothing.measurableSet_coordBox r (s j)) _

theorem nativePrior_slope_le {n : ℕ} {r : ℝ} (hr : 0 < r)
    (b s : Fin n → Fin 3 → ℝ)
    (hs : Pairwise (fun i j => Disjoint
      (FiniteSmoothing.coordBox r (s i)) (FiniteSmoothing.coordBox r (s j))))
    (Z : Set (EuclideanSpace ℝ (Fin 3))) :
    nativePrior r b s
      {l | (WithLp.toLp 2 ![l.2 3, l.2 4, l.2 5] : EuclideanSpace ℝ (Fin 3)) ∈ Z} ≤
      (n : ENNReal)⁻¹ * (ENNReal.ofReal (2 * r) ^ 3)⁻¹ * volume Z := by
  rw [nativePrior_apply]
  have heq : packLine ⁻¹'
      {l | (WithLp.toLp 2 ![l.2 3, l.2 4, l.2 5] : EuclideanSpace ℝ (Fin 3)) ∈ Z} =
      univ ×ˢ {v : Fin 3 → ℝ | WithLp.toLp 2 v ∈ Z} := by
    ext p
    have hs0 := packLine_slope_coordinate p 0
    have hs1 := packLine_slope_coordinate p 1
    have hs2 := packLine_slope_coordinate p 2
    have hv : ![(packLine p).2 3, (packLine p).2 4, (packLine p).2 5] = p.2 := by
      ext j
      fin_cases j <;> simp_all
    simp only [mem_preimage, mem_setOf_eq, mem_prod, mem_univ, true_and, hv]
  rw [heq]
  have hvol : volume {v : Fin 3 → ℝ | WithLp.toLp 2 v ∈ Z} = volume Z := by
    have he := (PiLp.volume_preserving_toLp (Fin 3)).map_eq
    have hZ := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin 3)) => μ Z) he
    rw [← MeasurableEquiv.coe_toLp, (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).map_apply] at hZ
    exact hZ
  simpa only [hvol] using FiniteSmoothing.smoothedPrior_slope_le hr b s hs
    {v : Fin 3 → ℝ | WithLp.toLp 2 v ∈ Z}

end Submission.Obl.k4_dk4_smoothed_problem.Framework
