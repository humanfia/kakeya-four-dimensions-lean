import Mathlib
import Submission.Lib.K4QuadraticSublevel

/-!
# The native signal along a trajectory

For a test `P` of total degree at most two, `t ↦ P (point b t)` is a quadratic in time.
We name its three coefficients by evaluation at `t = 0, 1/2, 1`, so that they are
continuous in the line coefficients `b`, and bound them by the sup of the signal on `[0,1]`.
This is the scalar observable of the projected groups (paper Section 8.2).

Adapted from: here:o200 (session x0701, Submission/Obl/k4_finite_projected_horizontal_candidates/LineSignal.lean).
-/

namespace Submission.Lib.K4ProjectedGroups

open MvPolynomial

noncomputable section

/-- The point of the frozen trajectory `![t, b 0 + t b 3, b 1 + t b 4, b 2 + t b 5]`. -/
def point (b : Fin 6 → ℝ) (t : ℝ) : Fin 4 → ℝ :=
  ![t, b 0 + t * b 3, b 1 + t * b 4, b 2 + t * b 5]

/-- Evaluating a multivariate polynomial at a polynomial point and then at `t` is evaluating
at the values: `(aeval f p).eval t = eval (fun i => (f i).eval t) p`. -/
theorem eval_aeval_eq (σ : Type*) (p : MvPolynomial σ ℝ) (f : σ → Polynomial ℝ) (t : ℝ) :
    (MvPolynomial.aeval f p).eval t = MvPolynomial.eval (fun i => (f i).eval t) p := by
  rw [← Polynomial.coe_evalRingHom, ← MvPolynomial.coe_aeval_eq_eval]
  rw [show (Polynomial.evalRingHom t) ((MvPolynomial.aeval f) p) =
    ((Polynomial.aeval t).comp (MvPolynomial.aeval f)) p from rfl]
  rw [MvPolynomial.comp_aeval]
  rfl

/-- A polynomial of total degree at most two is quadratic along every affine line: the
substituted univariate polynomial has degree at most two. -/
theorem eval_line_quadratic {σ : Type*} (p : MvPolynomial σ ℝ) (hp : p.totalDegree ≤ 2)
    (a b : σ → ℝ) : ∃ A B C : ℝ, ∀ t,
      MvPolynomial.eval (fun i => a i + t * b i) p = A * t ^ 2 + B * t + C := by
  let f : σ → Polynomial ℝ := fun i => Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X
  have hf1 : ∀ i, (f i).natDegree ≤ 1 := by
    intro i
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le (by simp)
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  have hdeg : (MvPolynomial.aeval f p).natDegree ≤ 2 := by
    simpa using MvPolynomial.aeval_natDegree_le p hp f hf1
  obtain ⟨A, B, C, h⟩ := Submission.Lib.K4QuadraticSublevel.quadratic_eq_coefficients _ hdeg
  refine ⟨A, B, C, fun t => ?_⟩
  have hpt : (fun i => a i + t * b i) = fun i => (f i).eval t := by
    funext i; simp only [f, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X]; ring
  rw [hpt, ← eval_aeval_eq σ p f t, h]
  simp

/-- The native signal of the line `b` at time `t`. -/
def sig (P : MvPolynomial (Fin 4) ℝ) (b : Fin 6 → ℝ) (t : ℝ) : ℝ :=
  eval (point b t) P

/-- Constant coefficient of the signal. -/
def sc0 (P : MvPolynomial (Fin 4) ℝ) (b : Fin 6 → ℝ) : ℝ := sig P b 0

/-- Linear coefficient of the signal. -/
def sc1 (P : MvPolynomial (Fin 4) ℝ) (b : Fin 6 → ℝ) : ℝ :=
  4 * sig P b (1 / 2) - 3 * sig P b 0 - sig P b 1

/-- Quadratic coefficient of the signal. -/
def sc2 (P : MvPolynomial (Fin 4) ℝ) (b : Fin 6 → ℝ) : ℝ :=
  2 * (sig P b 1 - 2 * sig P b (1 / 2) + sig P b 0)

theorem point_eq_line (b : Fin 6 → ℝ) (t : ℝ) :
    point b t = fun i => (![0, b 0, b 1, b 2] : Fin 4 → ℝ) i +
      t * (![1, b 3, b 4, b 5] : Fin 4 → ℝ) i := by
  funext i
  fin_cases i <;> simp [point]

theorem sig_quadratic {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2)
    (b : Fin 6 → ℝ) : ∃ A B C : ℝ, ∀ t, sig P b t = A * t ^ 2 + B * t + C := by
  obtain ⟨A, B, C, h⟩ := eval_line_quadratic P hP
    (![0, b 0, b 1, b 2] : Fin 4 → ℝ) (![1, b 3, b 4, b 5] : Fin 4 → ℝ)
  refine ⟨A, B, C, fun t => ?_⟩
  rw [sig, point_eq_line]
  exact h t

theorem sig_eq {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2)
    (b : Fin 6 → ℝ) (t : ℝ) :
    sig P b t = sc0 P b + t * sc1 P b + t ^ 2 * sc2 P b := by
  obtain ⟨A, B, C, h⟩ := sig_quadratic hP b
  simp only [sc0, sc1, sc2, h]
  ring

theorem abs_sc0_le {P : MvPolynomial (Fin 4) ℝ} {b : Fin 6 → ℝ} {K : ℝ}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, |sig P b t| ≤ K) : |sc0 P b| ≤ K :=
  h 0 ⟨le_rfl, zero_le_one⟩

theorem abs_sc1_le {P : MvPolynomial (Fin 4) ℝ} {b : Fin 6 → ℝ} {K : ℝ}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, |sig P b t| ≤ K) : |sc1 P b| ≤ 8 * K := by
  have h0 := abs_le.mp (h 0 ⟨le_rfl, zero_le_one⟩)
  have h1 := abs_le.mp (h 1 ⟨zero_le_one, le_rfl⟩)
  have hh := abs_le.mp (h (1 / 2) ⟨by norm_num, by norm_num⟩)
  rw [sc1, abs_le]
  constructor <;> linarith

theorem abs_sc2_le {P : MvPolynomial (Fin 4) ℝ} {b : Fin 6 → ℝ} {K : ℝ}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, |sig P b t| ≤ K) : |sc2 P b| ≤ 8 * K := by
  have h0 := abs_le.mp (h 0 ⟨le_rfl, zero_le_one⟩)
  have h1 := abs_le.mp (h 1 ⟨zero_le_one, le_rfl⟩)
  have hh := abs_le.mp (h (1 / 2) ⟨by norm_num, by norm_num⟩)
  rw [sc2, abs_le]
  constructor <;> linarith

theorem continuous_sig (P : MvPolynomial (Fin 4) ℝ) (t : ℝ) :
    Continuous (fun b : Fin 6 → ℝ => sig P b t) := by
  unfold sig
  apply (MvPolynomial.continuous_eval P).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp [point] <;> fun_prop

theorem continuous_sig_time (P : MvPolynomial (Fin 4) ℝ) (b : Fin 6 → ℝ) :
    Continuous (fun t : ℝ => sig P b t) := by
  unfold sig
  apply (MvPolynomial.continuous_eval P).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp [point] <;> fun_prop

theorem continuous_sc0 (P : MvPolynomial (Fin 4) ℝ) : Continuous (sc0 P) :=
  continuous_sig P 0

theorem continuous_sc1 (P : MvPolynomial (Fin 4) ℝ) : Continuous (sc1 P) := by
  unfold sc1
  have := continuous_sig P (1 / 2)
  have := continuous_sig P 0
  have := continuous_sig P 1
  fun_prop

theorem continuous_sc2 (P : MvPolynomial (Fin 4) ℝ) : Continuous (sc2 P) := by
  unfold sc2
  have := continuous_sig P (1 / 2)
  have := continuous_sig P 0
  have := continuous_sig P 1
  fun_prop

/-- The joint map `(line, time) ↦ signal` is continuous. -/
theorem continuous_sig_uncurry (P : MvPolynomial (Fin 4) ℝ) :
    Continuous (fun q : (Fin 6 → ℝ) × ℝ => sig P q.1 q.2) := by
  unfold sig
  apply (MvPolynomial.continuous_eval P).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp [point] <;> fun_prop

end

end Submission.Lib.K4ProjectedGroups
