import Mathlib

/-!
# Two specializations of the continuation input

The continuation input (o113, the second hypothesis of the frozen statement) controls a fixed
polynomial expression `H(z) = Q(z, f_1(z), …, f_m(z))` of simple quadratic sheets along a broken
segment.  We use it twice:

* with two sheets and `Q = w₁ - w₂`, so that `H` is the difference of the sheets: a small
  difference near the start bounds the difference near the end and its jets there, and small jets
  at the end bound the difference near the start (`cont_diff_forward`, `cont_diff_backward`);
* with one sheet and `Q` a quadratic test, so that `H(z) = Q(z, f(z))`
  (`cont_eval_forward`).
-/

namespace Submission.Lib.K4QuadraticSheets

open MvPolynomial

/-- The continuation input, verbatim (the second hypothesis of the frozen statement). -/
abbrev ContInput : Prop := ∀ n m D s : ℕ, ∃ q : ℕ, ∃ C : ℝ, s ≤ q ∧ 0 < C ∧ ∀ A : ℝ, 2 ≤ A → ∀ a b c : EuclideanSpace ℂ (Fin n), ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 → ∀ (P : Fin m → MvPolynomial (Fin (n + 1)) ℂ) (f : Fin m → EuclideanSpace ℂ (Fin n) → ℂ) (Q : MvPolynomial (Fin (n + m)) ℂ), (fun U : Set (EuclideanSpace ℂ (Fin n)) => (fun H : EuclideanSpace ℂ (Fin n) → ℂ => (∀ i, P i ≠ 0 ∧ (P i).totalDegree ≤ 2 ∧ DifferentiableOn ℂ (f i) U ∧ ∀ z ∈ U, MvPolynomial.eval (Fin.snoc (fun j : Fin n => z j) (f i z)) (P i) = 0 ∧ MvPolynomial.eval (Fin.snoc (fun j : Fin n => z j) (f i z)) (MvPolynomial.pderiv (Fin.last n) (P i)) ≠ 0) → Q.totalDegree ≤ D → ∀ V : ℝ, 0 ≤ V → ((∀ z ∈ Metric.closedBall a ((8 * A)⁻¹), ‖H z‖ ≤ V) → (∀ z ∈ Metric.closedBall c ((8 * A)⁻¹), ‖H z‖ ≤ A ^ C * V) ∧ ∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℂ j H c‖ ≤ A ^ C * V) ∧ ((∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℂ j H c‖ ≤ V) → ∀ z ∈ Metric.closedBall a ((8 * A)⁻¹), ‖H z‖ ≤ A ^ C * V)) (fun z => MvPolynomial.eval (Fin.append (fun j : Fin n => z j) (fun i : Fin m => f i z)) Q)) (Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c))

variable {n : ℕ}

local notation "E" => EuclideanSpace ℂ (Fin n)

/-- A simple quadratic sheet on a set, in the form the continuation input asks for. -/
def SimpleSheet (P : MvPolynomial (Fin (n + 1)) ℂ) (f : E → ℂ) (U : Set E) : Prop :=
  P ≠ 0 ∧ P.totalDegree ≤ 2 ∧ DifferentiableOn ℂ f U ∧ ∀ z ∈ U,
    MvPolynomial.eval (Fin.snoc (fun j : Fin n => z j) (f z)) P = 0 ∧
    MvPolynomial.eval (Fin.snoc (fun j : Fin n => z j) (f z))
      (MvPolynomial.pderiv (Fin.last n) P) ≠ 0

theorem SimpleSheet.mono {P : MvPolynomial (Fin (n + 1)) ℂ} {f : E → ℂ} {U U' : Set E}
    (h : SimpleSheet P f U) (hU : U' ⊆ U) : SimpleSheet P f U' :=
  ⟨h.1, h.2.1, h.2.2.1.mono hU, fun z hz => h.2.2.2 z (hU hz)⟩

/-- The difference polynomial `w₁ - w₂` in the two hidden coordinates. -/
noncomputable def diffPoly (n : ℕ) : MvPolynomial (Fin (n + 2)) ℂ :=
  X (Fin.natAdd n (0 : Fin 2)) - X (Fin.natAdd n (1 : Fin 2))

theorem totalDegree_diffPoly (n : ℕ) : (diffPoly n).totalDegree ≤ 1 := by
  unfold diffPoly
  apply (totalDegree_sub _ _).trans
  apply max_le <;> simp [totalDegree_X]

theorem eval_append_diffPoly (u : Fin n → ℂ) (v : Fin 2 → ℂ) :
    eval (Fin.append u v) (diffPoly n) = v 0 - v 1 := by
  simp [diffPoly]

/-- **Forward comparison of two sheets.**  A small difference of two simple sheets near the start
of a broken segment stays polynomially small near its end, together with its jets there. -/
theorem cont_diff_forward (hC : ContInput) (s : ℕ) :
    ∃ q : ℕ, ∃ C : ℝ, s ≤ q ∧ 0 < C ∧ ∀ A : ℝ, 2 ≤ A → ∀ a b c : EuclideanSpace ℂ (Fin 3),
      ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 → ∀ (P₁ P₂ : MvPolynomial (Fin 4) ℂ)
      (f₁ f₂ : EuclideanSpace ℂ (Fin 3) → ℂ),
      SimpleSheet P₁ f₁ (Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c)) →
      SimpleSheet P₂ f₂ (Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c)) →
      ∀ V : ℝ, 0 ≤ V →
        ((∀ z ∈ Metric.closedBall a ((8 * A)⁻¹), ‖f₁ z - f₂ z‖ ≤ V) →
          (∀ z ∈ Metric.closedBall c ((8 * A)⁻¹), ‖f₁ z - f₂ z‖ ≤ A ^ C * V) ∧
          ∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℂ j (fun z => f₁ z - f₂ z) c‖ ≤ A ^ C * V) ∧
        ((∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℂ j (fun z => f₁ z - f₂ z) c‖ ≤ V) →
          ∀ z ∈ Metric.closedBall a ((8 * A)⁻¹), ‖f₁ z - f₂ z‖ ≤ A ^ C * V) := by
  obtain ⟨q, C, hsq, hC0, hmain⟩ := hC 3 2 1 s
  refine ⟨q, C, hsq, hC0, ?_⟩
  intro A hA a b c ha hb hc P₁ P₂ f₁ f₂ h₁ h₂ V hV
  have key := hmain A hA a b c ha hb hc ![P₁, P₂] ![f₁, f₂] (diffPoly 3)
  have hHz : ∀ z : EuclideanSpace ℂ (Fin 3), MvPolynomial.eval
      (Fin.append (fun j : Fin 3 => z j) (fun i : Fin 2 => (![f₁, f₂] : Fin 2 → _ → ℂ) i z))
      (diffPoly 3) = f₁ z - f₂ z := by
    intro z
    rw [eval_append_diffPoly]
    simp
  have hH : (fun z : EuclideanSpace ℂ (Fin 3) => MvPolynomial.eval
      (Fin.append (fun j : Fin 3 => z j) (fun i : Fin 2 => (![f₁, f₂] : Fin 2 → _ → ℂ) i z))
      (diffPoly 3)) = fun z => f₁ z - f₂ z := funext hHz
  simp only [hH] at key
  simp only [hHz] at key
  apply key ?_ (totalDegree_diffPoly 3) V hV
  intro i
  fin_cases i
  · exact h₁
  · exact h₂

/-- **Comparison of a sheet with a fixed test.**  The value of a fixed test of degree at most
`D` on a simple sheet, small near the start of a broken segment, stays polynomially small near
its end; and small jets at the end make it small near the start. -/
theorem cont_eval (hC : ContInput) (D : ℕ) :
    ∃ q : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 2 ≤ A → ∀ a b c : EuclideanSpace ℂ (Fin 3),
      ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 → ∀ (P Q : MvPolynomial (Fin 4) ℂ)
      (f : EuclideanSpace ℂ (Fin 3) → ℂ),
      SimpleSheet P f (Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c)) →
      Q.totalDegree ≤ D → ∀ V : ℝ, 0 ≤ V →
        ((∀ z ∈ Metric.closedBall a ((8 * A)⁻¹),
            ‖MvPolynomial.eval (Fin.snoc (fun j : Fin 3 => z j) (f z)) Q‖ ≤ V) →
          (∀ z ∈ Metric.closedBall c ((8 * A)⁻¹),
            ‖MvPolynomial.eval (Fin.snoc (fun j : Fin 3 => z j) (f z)) Q‖ ≤ A ^ C * V) ∧
          ∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℂ j (fun z =>
            MvPolynomial.eval (Fin.snoc (fun j : Fin 3 => z j) (f z)) Q) c‖ ≤ A ^ C * V) ∧
        ((∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℂ j (fun z =>
            MvPolynomial.eval (Fin.snoc (fun j : Fin 3 => z j) (f z)) Q) c‖ ≤ V) →
          ∀ z ∈ Metric.closedBall a ((8 * A)⁻¹),
            ‖MvPolynomial.eval (Fin.snoc (fun j : Fin 3 => z j) (f z)) Q‖ ≤ A ^ C * V) := by
  obtain ⟨q, C, _, hC0, hmain⟩ := hC 3 1 D 0
  refine ⟨q, C, hC0, ?_⟩
  intro A hA a b c ha hb hc P Q f hf hQ V hV
  have key := hmain A hA a b c ha hb hc ![P] ![f] Q
  have hHz : ∀ z : EuclideanSpace ℂ (Fin 3), MvPolynomial.eval
      (Fin.append (fun j : Fin 3 => z j) (fun i : Fin 1 => (![f] : Fin 1 → _ → ℂ) i z)) Q =
      MvPolynomial.eval (Fin.snoc (fun j : Fin 3 => z j) (f z)) Q := by
    intro z
    rw [Fin.append_right_eq_snoc]
    simp
  have hH : (fun z : EuclideanSpace ℂ (Fin 3) => MvPolynomial.eval
      (Fin.append (fun j : Fin 3 => z j) (fun i : Fin 1 => (![f] : Fin 1 → _ → ℂ) i z)) Q) =
      fun z => MvPolynomial.eval (Fin.snoc (fun j : Fin 3 => z j) (f z)) Q := funext hHz
  simp only [hH] at key
  simp only [hHz] at key
  apply key ?_ hQ V hV
  intro i
  fin_cases i
  exact hf

end Submission.Lib.K4QuadraticSheets
