import Submission.Lib.K4ChartLifting.Prior

/-!
# Formats of normalized pieces and events

The inverse normalization as polynomials of degree at most one, on coefficients
(`denormCoeffPoly`) and on incidences (`denormIncPoly`); normalized prior pieces and
the slices of normalized events keep the sign format.
-/
namespace Submission.Lib.K4ChartLifting
open MeasureTheory MvPolynomial

namespace Frame
variable (F : Frame)

/-- The inverse normalization of coefficients as polynomials of degree at most one. -/
noncomputable def denormCoeffPoly : Fin 6 → MvPolynomial (Fin 6) ℝ :=
  let a₀ : MvPolynomial (Fin 6) ℝ := C (F.D 0 0) * X 0 + C (F.D 0 1) * X 1
  let a₁ : MvPolynomial (Fin 6) ℝ := C (F.D 1 0) * X 0 + C (F.D 1 1) * X 1
  let b₀ : MvPolynomial (Fin 6) ℝ := C (F.D 0 0) * X 3 + C (F.D 0 1) * X 4
  let b₁ : MvPolynomial (Fin 6) ℝ := C (F.D 1 0) * X 3 + C (F.D 1 1) * X 4
  let v₀ := C (F.u 0) + C F.q⁻¹ * b₀
  let v₁ := C (F.u 1) + C F.q⁻¹ * b₁
  let s₃ := C F.q⁻¹ * X 5
  ![a₀ + C (F.c 0) + C (F.t₀ * F.u 0) - C F.t₀ * v₀,
    a₁ + C (F.c 1) + C (F.t₀ * F.u 1) - C F.t₀ * v₁,
    X 2 - C F.t₀ * s₃, v₀, v₁, s₃]

theorem eval_denormCoeffPoly (l : Fin 6 → ℝ) :
    (fun e => eval l (F.denormCoeffPoly e)) = F.denormCoeff l := by
  funext e
  fin_cases e <;> simp [denormCoeffPoly, denormCoeff, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem totalDegree_denormCoeffPoly_le (e : Fin 6) :
    (F.denormCoeffPoly e).totalDegree ≤ 1 := by
  have hX : ∀ i : Fin 6, (X i : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 1 := fun i => deg1_X i
  have hlin : ∀ (a b : ℝ) (i j : Fin 6),
      (C a * X i + C b * X j : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 1 :=
    fun a b i j => deg1_add (deg1_C_mul _ (hX i)) (deg1_C_mul _ (hX j))
  have hv : ∀ (u a b : ℝ) (i j : Fin 6),
      (C u + C F.q⁻¹ * (C a * X i + C b * X j) : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 1 :=
    fun u a b i j => deg1_add (deg1_C _) (deg1_C_mul _ (hlin _ _ _ _))
  fin_cases e
  · exact deg1_sub (deg1_add (deg1_add (hlin _ _ _ _) (deg1_C _)) (deg1_C _))
      (deg1_C_mul _ (hv _ _ _ _ _))
  · exact deg1_sub (deg1_add (deg1_add (hlin _ _ _ _) (deg1_C _)) (deg1_C _))
      (deg1_C_mul _ (hv _ _ _ _ _))
  · exact deg1_sub (hX 2) (deg1_C_mul _ (deg1_C_mul _ (hX 5)))
  · exact hv _ _ _ _ _
  · exact hv _ _ _ _ _
  · exact deg1_C_mul _ (hX 5)

/-- Normalized prior pieces keep the sign format. -/
theorem fmt_denorm_piece {H : ℝ} {D : ℕ} {S : Set (Fin 6 → ℝ)} (h : Fmt H D S) :
    Fmt H D (F.denormCoeff ⁻¹' S) := by
  have := h.preimage F.denormCoeffPoly F.totalDegree_denormCoeffPoly_le
  refine this.congr ?_
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, F.eval_denormCoeffPoly]

/-- The incidence-level inverse normalization `(x₀..x₅, x₆) ↦ (denormCoeff x, t₀ + q x₆)`. -/
noncomputable def denormIncPoly : Fin 7 → MvPolynomial (Fin 7) ℝ :=
  Fin.lastCases (C F.t₀ + C F.q * X 6)
    (fun e => bind₁ (fun j : Fin 6 => (X j.castSucc : MvPolynomial (Fin 7) ℝ))
      (F.denormCoeffPoly e))

theorem eval_denormIncPoly (x : Fin 7 → ℝ) :
    (fun e => eval x (F.denormIncPoly e)) =
      Fin.lastCases (F.t₀ + F.q * x 6) (fun e => F.denormCoeff (fun j => x j.castSucc) e) := by
  funext e
  refine Fin.lastCases ?_ (fun e => ?_) e
  · rw [denormIncPoly, Fin.lastCases_last, Fin.lastCases_last]
    simp
  · simp only [denormIncPoly, Fin.lastCases_castSucc, eval_bind₁', eval_X]
    exact congrFun (F.eval_denormCoeffPoly (fun j => x j.castSucc)) e

theorem totalDegree_denormIncPoly_le (e : Fin 7) : (F.denormIncPoly e).totalDegree ≤ 1 := by
  refine Fin.lastCases ?_ (fun e => ?_) e
  · simp only [denormIncPoly, Fin.lastCases_last]
    exact deg1_add (deg1_C _) (deg1_C_mul _ (deg1_X _))
  · simp only [denormIncPoly, Fin.lastCases_castSucc]
    exact (totalDegree_bind₁_le_of_le_one _ (fun j => deg1_X _) _).trans
      (F.totalDegree_denormCoeffPoly_le e)

/-- The slices of a normalized event keep the sign format. -/
theorem fmt_normEvent_slice {A₀ : Set Trajectory} {E : Set Incidence} (i : ℕ) {HA HE : ℝ}
    {DA DE : ℕ} (hA : Fmt HA DA {x | (i, x) ∈ A₀})
    (hE : Fmt HE DE {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ E}) :
    Fmt (HA + 2 + HE) (max (max DA 1) DE) {x : Fin 7 → ℝ |
      ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ F.normEvent A₀ E} := by
  have h1 := hA.preimage (fun e : Fin 6 => F.denormIncPoly e.castSucc)
    (fun e => F.totalDegree_denormIncPoly_le _)
  have hlo := Fmt.sign (n := 7) (le_refl (1 : ℝ)) (X 6 : MvPolynomial (Fin 7) ℝ)
  have hhi := Fmt.sign (n := 7) (le_refl (1 : ℝ)) (1 - X 6 : MvPolynomial (Fin 7) ℝ)
  have h2 := (hlo.inter hhi).mono (le_refl _) (show max (X 6 : MvPolynomial (Fin 7) ℝ).totalDegree
      (1 - X 6 : MvPolynomial (Fin 7) ℝ).totalDegree ≤ 1 from
        max_le (deg1_X _) (deg1_sub (by simp) (deg1_X _)))
  have h3 := hE.preimage F.denormIncPoly F.totalDegree_denormIncPoly_le
  have h := (h1.inter h2).inter h3
  have hH : HA + (1 + 1) + HE = HA + 2 + HE := by ring
  rw [hH] at h
  refine h.congr ?_
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, normEvent, eval_X, map_sub, map_one,
    sub_nonneg]
  have e1 : (fun e : Fin 6 => eval x (F.denormIncPoly e.castSucc)) =
      F.denormCoeff (fun j => x j.castSucc) := by
    funext e
    have := congrFun (F.eval_denormIncPoly x) e.castSucc
    rw [Fin.lastCases_castSucc] at this
    exact this
  have e3 : eval x (F.denormIncPoly 6) = F.t₀ + F.q * x 6 := by
    have := congrFun (F.eval_denormIncPoly x) (Fin.last 6)
    rw [Fin.lastCases_last] at this
    exact this
  rw [e1, e3]
  simp only [Set.mem_Icc]
  tauto

end Frame
end Submission.Lib.K4ChartLifting
