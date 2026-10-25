import Submission.Obl.k4_eligibility_sign_description.Families
import Submission.Obl.k4_horizon_chart_assembly.NativeGeometry
import Submission.Lib.K4MovingMeshBoxes.Projection

namespace Submission.Obl.k4_general_parent_projected_layers

open Set MeasureTheory

noncomputable section

/-- Original spacetime trajectory; no coordinate of the hidden variable is rescaled. -/
def point (b : Fin 6 → ℝ) (t : ℝ) : Fin 4 → ℝ :=
  ![t, b 0 + t * b 3, b 1 + t * b 4, b 2 + t * b 5]

def signal (P : MvPolynomial (Fin 4) ℝ) (b : Fin 6 → ℝ) (t : ℝ) : ℝ :=
  MvPolynomial.eval (point b t) P

theorem signal_quadratic (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (b : Fin 6 → ℝ) :
    Submission.Obl.k4_eligibility_sign_description.Quadratic (signal P b) := by
  convert Submission.Obl.k4_eligibility_sign_description.Quadratic.mv_line P hP
    ![0, b 0, b 1, b 2] ![1, b 3, b 4, b 5] using 1
  funext t
  apply congrArg (fun z : Fin 4 → ℝ => MvPolynomial.eval z P)
  funext i
  fin_cases i <;> simp [point]

/-- The scalar coefficients keep the original observable and normalize only Y. -/
def scalarCoeff (P : MvPolynomial (Fin 4) ℝ) (g y₀ y₁ : ℝ)
    (b : Fin 6 → ℝ) : Fin 5 → ℝ :=
  ![(b 1 - y₀) / g, (b 4 - y₁) / g,
    signal P b 0,
    4 * signal P b (1 / 2) - signal P b 1 - 3 * signal P b 0,
    2 * signal P b 1 - 4 * signal P b (1 / 2) + 2 * signal P b 0]

theorem scalarCoeff_y (P : MvPolynomial (Fin 4) ℝ) (g y₀ y₁ : ℝ)
    (b : Fin 6 → ℝ) (t : ℝ) :
    scalarCoeff P g y₀ y₁ b 0 + t * scalarCoeff P g y₀ y₁ b 1 =
      (b 1 + t * b 4 - y₀ - t * y₁) / g := by
  simp only [scalarCoeff, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem scalarCoeff_x (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (g y₀ y₁ : ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    scalarCoeff P g y₀ y₁ b 2 + t * scalarCoeff P g y₀ y₁ b 3 +
      t ^ 2 * scalarCoeff P g y₀ y₁ b 4 = signal P b t := by
  have h := Submission.Obl.k4_horizon_chart_assembly.quadraticCoefficients_eval
    (signal_quadratic P hP b) t
  change signal P b 0 + t * (4 * signal P b (1 / 2) - signal P b 1 -
    3 * signal P b 0) + t ^ 2 * (2 * signal P b 1 -
    4 * signal P b (1 / 2) + 2 * signal P b 0) = signal P b t
  change signal P b 0 + t * (-signal P b 1 + 4 * signal P b (1 / 2) -
    3 * signal P b 0) + t ^ 2 * (2 * signal P b 1 -
    4 * signal P b (1 / 2) + 2 * signal P b 0) = signal P b t at h
  convert h using 1 <;> ring

theorem continuous_signal (P : MvPolynomial (Fin 4) ℝ) (t : ℝ) :
    Continuous (fun b : Fin 6 → ℝ => signal P b t) := by
  apply P.continuous_eval.comp
  unfold point
  fun_prop

theorem measurable_scalarCoeff {α : Type*} [MeasurableSpace α]
    {b : α → Fin 6 → ℝ} (hb : Measurable b)
    (P : MvPolynomial (Fin 4) ℝ) (g y₀ y₁ : ℝ) :
    Measurable (fun l => scalarCoeff P g y₀ y₁ (b l)) := by
  have hs (t : ℝ) := (continuous_signal P t).measurable.comp hb
  have he (i : Fin 6) := (measurable_pi_apply i).comp hb
  apply Measurable.of_eval
  intro i
  fin_cases i <;> simp only [scalarCoeff, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact ((he 1).sub_const y₀).div_const g
  · exact ((he 4).sub_const y₁).div_const g
  · exact hs 0
  · exact (((hs (1 / 2)).const_mul 4).sub (hs 1)).sub ((hs 0).const_mul 3)
  · exact (((hs 1).const_mul 2).sub ((hs (1 / 2)).const_mul 4)).add ((hs 0).const_mul 2)

/-- Bounding the observable in time bounds its scalar coefficients, even when
its original polynomial coefficients and hidden trajectory coordinates are large. -/
theorem scalarCoeff_bound {P : MvPolynomial (Fin 4) ℝ} {g y₀ y₁ K : ℝ}
    {b : Fin 6 → ℝ} (hg : 0 < g) (hK : 1 ≤ K)
    (hy₀ : |b 1 - y₀| ≤ g) (hy₁ : |b 4 - y₁| ≤ g)
    (hs : ∀ t ∈ Icc (0 : ℝ) 1, |signal P b t| ≤ K) :
    ∀ i, |scalarCoeff P g y₀ y₁ b i| ≤ 8 * K := by
  have hs₀ := hs 0 (by norm_num)
  have hs₁ := hs 1 (by norm_num)
  have hsh := hs (1 / 2) (by norm_num)
  intro i
  fin_cases i
  · change |(b 1 - y₀) / g| ≤ 8 * K
    rw [abs_div, abs_of_pos hg]
    have hdiv := (div_le_one hg).mpr hy₀
    linarith
  · change |(b 4 - y₁) / g| ≤ 8 * K
    rw [abs_div, abs_of_pos hg]
    have hdiv := (div_le_one hg).mpr hy₁
    linarith
  · change |signal P b 0| ≤ 8 * K
    linarith
  · change |4 * signal P b (1 / 2) - signal P b 1 - 3 * signal P b 0| ≤ 8 * K
    rw [abs_le] at hs₀ hs₁ hsh ⊢
    constructor <;> linarith
  · change |2 * signal P b 1 - 4 * signal P b (1 / 2) + 2 * signal P b 0| ≤ 8 * K
    rw [abs_le] at hs₀ hs₁ hsh ⊢
    constructor <;> linarith

/-- The full-time signal bound is a measurable condition on original trajectories. -/
theorem measurableSet_signal_bound {α : Type*} [MeasurableSpace α]
    {b : α → Fin 6 → ℝ} (hb : Measurable b)
    (P : MvPolynomial (Fin 4) ℝ) (K : ℝ) :
    MeasurableSet {l | ∀ t ∈ Icc (0 : ℝ) 1, |signal P (b l) t| ≤ K} := by
  have hclosed : IsClosed {v : Fin 6 → ℝ | ∀ t ∈ Icc (0 : ℝ) 1,
      |signal P v t| ≤ K} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun t => isClosed_iInter fun _ =>
      isClosed_le (continuous_signal P t).abs continuous_const
  exact hclosed.measurableSet.preimage hb

end

end Submission.Obl.k4_general_parent_projected_layers
