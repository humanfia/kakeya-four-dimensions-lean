/-
Adapted from this LOT tree o198, session x0691, commit 9816360a0a6a894f89615acd484d1584ad77897e,
Submission/Obl/k4_balanced_native_packet_transport/NativeCoordinates.lean. Existing source attributions below are retained.
-/
import Submission.Obl.k4_uncapped_native_capping.Definitions
import Submission.Obl.k4_eligibility_sign_description.Families

/-!
The frozen interpolation coefficients give exact values on every time block.
The native signal argument follows the same-tree o178/x0588
`ScalarRetiming.lean` (8c538276); the proof here uses the accepted quadratic
restriction lemma directly and needs no open ancestor module.
-/
namespace Submission.Obl.k4_uncapped_native_capping

open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_eligibility_sign_description
noncomputable section

/-- The tangent interpolation agrees with its original affine coordinate. -/
theorem nativeCoeff_scalarY (P : MvPolynomial (Fin 4) ℝ)
    (t₀ q a : ℝ) (v : Fin 3 → ℝ) {A : Set Traj} {l : Traj}
    (hl : l ∈ A) (τ : ℝ) :
    scalarY (nativeCoeff P t₀ q a v A l) τ =
      a + ∑ i : Fin 3, v i * x l (t₀ + q * τ) i.castSucc := by
  simp [nativeCoeff, scalarY, hl, x, Fin.sum_univ_three]
  ring

/-- Restricting a native quadratic to the original line and block is quadratic. -/
theorem native_signal_quadratic (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (t₀ q : ℝ) (l : Traj) :
    Quadratic (fun τ => MvPolynomial.eval (x l (t₀ + q * τ)) P) := by
  have h := Quadratic.mv_line P hP (x l t₀)
    ![q, q * l.2 3, q * l.2 4, q * l.2 5]
  convert h using 1
  funext τ
  apply congrArg (fun z : Fin 4 → ℝ => MvPolynomial.eval z P)
  funext i
  fin_cases i <;> simp [x] <;> ring

/-- The scalar signal is the unchanged native polynomial in block time. -/
theorem nativeCoeff_scalarX (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ q a : ℝ) (v : Fin 3 → ℝ) {A : Set Traj} {l : Traj}
    (hl : l ∈ A) (τ : ℝ) :
    scalarX (nativeCoeff P t₀ q a v A l) τ =
      MvPolynomial.eval (x l (t₀ + q * τ)) P := by
  classical
  obtain ⟨α, β, γ, h⟩ := native_signal_quadratic P hP t₀ q l
  simp only [nativeCoeff, if_pos hl, scalarX]
  change MvPolynomial.eval (x l t₀) P +
      τ * (4 * MvPolynomial.eval (x l (t₀ + q / 2)) P -
        3 * MvPolynomial.eval (x l t₀) P - MvPolynomial.eval (x l (t₀ + q)) P) +
      τ ^ 2 * (2 * (MvPolynomial.eval (x l (t₀ + q)) P +
        MvPolynomial.eval (x l t₀) P - 2 * MvPolynomial.eval (x l (t₀ + q / 2)) P)) = _
  dsimp only at h
  have h₀ := h 0
  have hm := h (1 / 2)
  have h₁ := h 1
  simp only [mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0)] at h₀
  simp only [mul_one, one_pow] at h₁
  rw [show t₀ + q / 2 = t₀ + q * (1 / 2) by ring, hm, h₀, h₁, h τ]
  ring

theorem measurable_nativeCoeff (P : MvPolynomial (Fin 4) ℝ)
    (t₀ q a : ℝ) (v : Fin 3 → ℝ) {A : Set Traj} (hA : MeasurableSet A) :
    Measurable (nativeCoeff P t₀ q a v A) := by
  have hX (t : ℝ) : Measurable (fun l : Traj => MvPolynomial.eval (x l t) P) :=
    P.continuous_eval.measurable.comp (by unfold x; fun_prop)
  have hY (t : ℝ) : Measurable
      (fun l : Traj => a + ∑ i : Fin 3, v i * x l t i.castSucc) := by
    unfold x
    fun_prop
  unfold nativeCoeff
  apply Measurable.ite hA
  · apply Measurable.of_eval
    intro i
    fin_cases i
    · exact hY t₀
    · exact (hY (t₀ + q)).sub (hY t₀)
    · exact hX t₀
    · exact (((hX (t₀ + q / 2)).const_mul 4).sub ((hX t₀).const_mul 3)).sub (hX (t₀ + q))
    · exact (((hX (t₀ + q)).add (hX t₀)).sub ((hX (t₀ + q / 2)).const_mul 2)).const_mul 2
  · exact measurable_const

/-- The same original native value is observed after a refinement of time. -/
theorem nativeCoeff_retime_value (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ q a a' : ℝ) (v v' : Fin 3 → ℝ) {A C : Set Traj} (hAC : A ⊆ C)
    {l : Traj} (hl : l ∈ A) (τ : ℝ) :
    scalarX (nativeCoeff P t₀ q a' v' A l) τ =
      scalarX (nativeCoeff P 0 1 a v C l) (t₀ + q * τ) := by
  rw [nativeCoeff_scalarX P hP t₀ q a' v' hl,
    nativeCoeff_scalarX P hP 0 1 a v (hAC hl)]
  simp only [zero_add, one_mul]

/-- Subtracting one fixed physical tangent center and dividing by block length
gives an affine contraction back to the source tangent coordinate. -/
theorem nativeCoeff_retime_tangent (P : MvPolynomial (Fin 4) ℝ)
    (t₀ q a c : ℝ) (hq : q ≠ 0) (v : Fin 3 → ℝ)
    {A C : Set Traj} (hAC : A ⊆ C) {l : Traj} (hl : l ∈ A) (τ : ℝ) :
    scalarY (nativeCoeff P 0 1 a v C l) (t₀ + q * τ) =
      c + q * scalarY
        (nativeCoeff P t₀ q ((a - c) / q) (fun i => v i / q) A l) τ := by
  rw [nativeCoeff_scalarY P 0 1 a v (hAC hl),
    nativeCoeff_scalarY P t₀ q ((a - c) / q) (fun i => v i / q) hl]
  simp only [zero_add, one_mul, Fin.sum_univ_three]
  field_simp
  ring

end
end Submission.Obl.k4_uncapped_native_capping
