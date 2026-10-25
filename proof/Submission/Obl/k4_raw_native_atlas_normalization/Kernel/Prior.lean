/- Adapted from this LOT tree, obligation o064, session x0214, commit a612574618456ee4cdb4d54c4cee48847fe99758,
   Submission/Lib/K4ChartLifting/Prior.lean. Original provenance is retained below. -/
import Submission.Obl.k4_raw_native_atlas_normalization.Kernel.Normalized

/-!
# The normalized prior

The coefficient normalization is affine with linear part `normMatrix`, of determinant
`q³ (det D⁻¹)²`; it is a homeomorphism with inverse `denormCoeff`. Lebesgue measure
restricted to `S` is pushed to `|det normMatrix|⁻¹` times Lebesgue measure restricted to
`denormCoeff ⁻¹' S`, so a piecewise-Lebesgue prior restricted to an assignment and
normalized is again piecewise Lebesgue (`Frame.map_normTraj_prior`), with the pieces
`denormCoeff ⁻¹' (A j ∩ {x | (i j, x) ∈ A₀})`.
-/
namespace Submission.Obl.k4_raw_native_atlas_normalization.Kernel
open MeasureTheory MvPolynomial

theorem det6_shape (a b c d t q : ℝ) :
    (!![a, b, 0, t * a, t * b, 0;
        c, d, 0, t * c, t * d, 0;
        0, 0, 1, 0, 0, t;
        0, 0, 0, q * a, q * b, 0;
        0, 0, 0, q * c, q * d, 0;
        0, 0, 0, 0, 0, q] : Matrix (Fin 6) (Fin 6) ℝ).det = q ^ 3 * (a * d - b * c) ^ 2 := by
  simp (disch := decide) [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.succAbove_of_castSucc_lt, Fin.succAbove_of_le_castSucc]
  ring

namespace Frame
variable (F : Frame)

/-- The linear part of the coefficient normalization. -/
noncomputable def normMatrix : Matrix (Fin 6) (Fin 6) ℝ :=
  !![F.D⁻¹ 0 0, F.D⁻¹ 0 1, 0, F.t₀ * F.D⁻¹ 0 0, F.t₀ * F.D⁻¹ 0 1, 0;
     F.D⁻¹ 1 0, F.D⁻¹ 1 1, 0, F.t₀ * F.D⁻¹ 1 0, F.t₀ * F.D⁻¹ 1 1, 0;
     0, 0, 1, 0, 0, F.t₀;
     0, 0, 0, F.q * F.D⁻¹ 0 0, F.q * F.D⁻¹ 0 1, 0;
     0, 0, 0, F.q * F.D⁻¹ 1 0, F.q * F.D⁻¹ 1 1, 0;
     0, 0, 0, 0, 0, F.q]

theorem det_normMatrix : F.normMatrix.det = F.q ^ 3 * F.D⁻¹.det ^ 2 := by
  rw [normMatrix, det6_shape, Matrix.det_fin_two]

theorem normCoeff_eq (l : Fin 6 → ℝ) :
    F.normCoeff l = F.normMatrix.mulVec l + F.normCoeff 0 := by
  funext e
  fin_cases e <;> simp [normCoeff, normMatrix, dotProduct, Fin.sum_univ_succ] <;>
    ring

theorem normCoeff_denormCoeff (hq : F.q ≠ 0) (hD : IsUnit F.D.det) (l : Fin 6 → ℝ) :
    F.normCoeff (F.denormCoeff l) = l := by
  have hm : F.D⁻¹ * F.D = 1 := Matrix.nonsing_inv_mul F.D hD
  have h00 : F.D⁻¹ 0 0 * F.D 0 0 + F.D⁻¹ 0 1 * F.D 1 0 = 1 := by
    have := congrFun (congrFun hm 0) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : F.D⁻¹ 0 0 * F.D 0 1 + F.D⁻¹ 0 1 * F.D 1 1 = 0 := by
    have := congrFun (congrFun hm 0) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : F.D⁻¹ 1 0 * F.D 0 0 + F.D⁻¹ 1 1 * F.D 1 0 = 0 := by
    have := congrFun (congrFun hm 1) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : F.D⁻¹ 1 0 * F.D 0 1 + F.D⁻¹ 1 1 * F.D 1 1 = 1 := by
    have := congrFun (congrFun hm 1) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  funext e
  fin_cases e <;> simp [denormCoeff, normCoeff, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    field_simp
  · linear_combination l 0 * h00 + l 1 * h01
  · linear_combination l 0 * h10 + l 1 * h11
  · linear_combination l 3 * h00 + l 4 * h01
  · linear_combination l 3 * h10 + l 4 * h11

theorem det_normMatrix_ne_zero (hq : F.q ≠ 0) (hD : IsUnit F.D.det) : F.normMatrix.det ≠ 0 := by
  rw [det_normMatrix, Matrix.det_nonsing_inv]
  have : F.D.det ≠ 0 := hD.ne_zero
  simp [hq, Ring.inverse_eq_inv', this]

theorem continuous_normCoeff : Continuous F.normCoeff := by
  have : F.normCoeff = fun l => fun e => MvPolynomial.eval l (F.normCoeffPoly e) := by
    funext l; exact (congrFun (F.eval_normCoeffPoly l) ·) |> funext |>.symm
  rw [this]
  exact continuous_pi fun e => MvPolynomial.continuous_eval _

theorem map_normCoeff_volume (hq : F.q ≠ 0) (hD : IsUnit F.D.det) :
    Measure.map F.normCoeff volume = ENNReal.ofReal |F.normMatrix.det|⁻¹ • volume := by
  have hfun : F.normCoeff = (fun x => x + F.normCoeff 0) ∘ (Matrix.toLin' F.normMatrix) := by
    funext l; simp [F.normCoeff_eq l, Matrix.toLin'_apply]
  rw [hfun, ← Measure.map_map (measurable_add_const _)
    (LinearMap.continuous_on_pi _).measurable,
    Real.map_matrix_volume_pi_eq_smul_volume_pi (F.det_normMatrix_ne_zero hq hD),
    Measure.map_smul, map_add_right_eq_self, abs_inv]
  exact (measurable_add_const _).aemeasurable

/-- The coefficient normalization as a homeomorphism. -/
noncomputable def normHomeomorph (hq : F.q ≠ 0) (hD : IsUnit F.D.det) :
    (Fin 6 → ℝ) ≃ₜ (Fin 6 → ℝ) where
  toFun := F.normCoeff
  invFun := F.denormCoeff
  left_inv := F.denormCoeff_normCoeff hq hD
  right_inv := F.normCoeff_denormCoeff hq hD
  continuous_toFun := F.continuous_normCoeff
  continuous_invFun := F.continuous_denormCoeff

theorem map_normCoeff_restrict (hq : F.q ≠ 0) (hD : IsUnit F.D.det) (S : Set (Fin 6 → ℝ)) :
    Measure.map F.normCoeff (volume.restrict S) =
      ENNReal.ofReal |F.normMatrix.det|⁻¹ • volume.restrict (F.denormCoeff ⁻¹' S) := by
  set e := (F.normHomeomorph hq hD).toMeasurableEquiv
  have he : (e : (Fin 6 → ℝ) → (Fin 6 → ℝ)) = F.normCoeff := rfl
  have hvol : Measure.map e volume = ENNReal.ofReal |F.normMatrix.det|⁻¹ • volume := by
    rw [he]; exact F.map_normCoeff_volume hq hD
  ext T hT
  have key : Measure.map e volume (T ∩ F.denormCoeff ⁻¹' S) =
      (ENNReal.ofReal |F.normMatrix.det|⁻¹ • volume) (T ∩ F.denormCoeff ⁻¹' S) := by rw [hvol]
  rw [e.map_apply] at key
  have hpre : e ⁻¹' (T ∩ F.denormCoeff ⁻¹' S) = e ⁻¹' T ∩ S := by
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff]
    rw [he, F.denormCoeff_normCoeff hq hD]
  rw [hpre] at key
  rw [← he, e.map_apply, Measure.smul_apply, Measure.restrict_apply hT,
    Measure.restrict_apply (e.measurable hT), key, Measure.smul_apply]

/-- The normalized prior of a piecewise-Lebesgue prior is again piecewise Lebesgue, on the
normalized pieces, with densities multiplied by `|det normMatrix|⁻¹`. -/
theorem map_normTraj_prior (hq : F.q ≠ 0) (hD : IsUnit F.D.det) {m : ℕ} (c : Fin m → ℝ)
    (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)) (A₀ : Set Trajectory)
    (hA₀ : MeasurableSet A₀) :
    Measure.map F.normTraj ((∑ j, ENNReal.ofReal (c j) •
        Measure.map (fun x => (i j, x)) (volume.restrict (A j))).restrict A₀) =
      ∑ j, (ENNReal.ofReal (c j) * ENNReal.ofReal |F.normMatrix.det|⁻¹) •
        Measure.map (fun x => (i j, x)) (volume.restrict
          (F.denormCoeff ⁻¹' (A j ∩ {x | (i j, x) ∈ A₀}))) := by
  have hmk : ∀ n : ℕ, Measurable (fun x : Fin 6 → ℝ => ((n, x) : Trajectory)) :=
    fun n => measurable_const.prodMk measurable_id
  have hN : Measurable F.normTraj := ChartSystem.measurable_normTraj F
  have hres : (∑ j, ENNReal.ofReal (c j) •
      Measure.map (fun x => (i j, x)) (volume.restrict (A j))).restrict A₀ =
      ∑ j, ENNReal.ofReal (c j) • Measure.map (fun x => (i j, x))
        (volume.restrict (A j ∩ {x | (i j, x) ∈ A₀})) := by
    ext t ht
    simp only [Measure.restrict_apply ht, Measure.coe_finsetSum, Finset.sum_apply,
      Measure.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Measure.map_apply (hmk _) (ht.inter hA₀), Measure.map_apply (hmk _) ht,
      Measure.restrict_apply ((hmk _) (ht.inter hA₀)), Measure.restrict_apply ((hmk _) ht)]
    congr 2
    ext x; simp [and_assoc, and_comm, and_left_comm]
  rw [hres, Measure.map_finset_sum hN.aemeasurable]
  apply Finset.sum_congr rfl
  intro j _
  rw [Measure.map_smul, Measure.map_map hN (hmk _)]
  have hcomp : F.normTraj ∘ (fun x => (i j, x)) = (fun x => (i j, x)) ∘ F.normCoeff := rfl
  rw [hcomp, ← Measure.map_map (hmk _) F.continuous_normCoeff.measurable,
    F.map_normCoeff_restrict hq hD, Measure.map_smul, smul_smul]
  all_goals first | exact (hmk _).aemeasurable | exact hN.aemeasurable

end Frame
end Submission.Obl.k4_raw_native_atlas_normalization.Kernel
