import Submission.Obl.k4_eligibility_sign_description.Interval
import Submission.Obl.k4_eligibility_sign_description.Signs
import Submission.Lib.K4QuadraticSublevel

namespace Submission.Obl.k4_eligibility_sign_description

noncomputable section

variable {σ X : Type*}

/-- A real function which is a polynomial of degree at most two. -/
def Quadratic (f : ℝ → ℝ) : Prop :=
  ∃ A B C : ℝ, ∀ t, f t = A * t ^ 2 + B * t + C

lemma Quadratic.of_polynomial (p : Polynomial ℝ) (hp : p.natDegree ≤ 2) :
    Quadratic (fun t => p.eval t) := by
  obtain ⟨A, B, C, hp⟩ := Submission.Lib.K4QuadraticSublevel.quadratic_eq_coefficients p hp
  refine ⟨A, B, C, ?_⟩
  intro t
  simp [hp]

lemma Quadratic.interpolation {f : ℝ → ℝ} (hf : Quadratic f) (t : ℝ) :
    f t = ((f 1 + f (-1)) / 2 - f 0) * t ^ 2 +
      ((f 1 - f (-1)) / 2) * t + f 0 := by
  obtain ⟨A, B, C, hf⟩ := hf
  simp only [hf]
  ring

lemma Quadratic.sub_const {f : ℝ → ℝ} (hf : Quadratic f) (k : ℝ) :
    Quadratic (fun t => k - f t) := by
  obtain ⟨A, B, C, hf⟩ := hf
  refine ⟨-A, -B, k - C, fun t => ?_⟩
  dsimp only
  rw [hf]
  ring

lemma Quadratic.add_const {f : ℝ → ℝ} (hf : Quadratic f) (k : ℝ) :
    Quadratic (fun t => k + f t) := by
  obtain ⟨A, B, C, hf⟩ := hf
  refine ⟨A, B, k + C, fun t => ?_⟩
  dsimp only
  rw [hf]
  ring

def SignPositive (strict : Bool) (s : SignType) : Prop :=
  if strict then s = 1 else 0 ≤ s

lemma signPositive_iff (strict : Bool) (x : ℝ) :
    SignPositive strict (SignType.sign x) ↔ Positive strict x := by
  cases strict <;> simp [SignPositive, Positive, sign_eq_one_iff]

/-- The six polynomial tests for a quadratic have total degree at most four. -/
lemma SignRep.quadratic (v : X → σ → ℝ) (strict : Bool)
    (A B C : MvPolynomial σ ℝ) (hA : A.totalDegree ≤ 2)
    (hB : B.totalDegree ≤ 2) (hC : C.totalDegree ≤ 2)
    (l r : ℝ) (hlr : l ≤ r) :
    SignRep v 6 4 (fun x => ∀ t ∈ Set.Icc l r,
      Positive strict (MvPolynomial.eval (v x) A * t ^ 2 +
        MvPolynomial.eval (v x) B * t + MvPolynomial.eval (v x) C)) := by
  let atTime := fun t : ℝ => MvPolynomial.C (t ^ 2) * A + MvPolynomial.C t * B + C
  let leftDeriv := MvPolynomial.C (2 * l) * A + B
  let rightDeriv := MvPolynomial.C (2 * r) * A + B
  let disc := MvPolynomial.C 4 * A * C - B ^ 2
  let p : Fin 6 → MvPolynomial σ ℝ :=
    ![atTime l, atTime r, A, leftDeriv, rightDeriv, disc]
  have ht : ∀ t, (atTime t).totalDegree ≤ 2 := by
    intro t
    exact degree_add_le (degree_add_le ((degree_C_mul_le _ _).trans hA)
      ((degree_C_mul_le _ _).trans hB)) hC
  have hdL : leftDeriv.totalDegree ≤ 2 :=
    degree_add_le ((degree_C_mul_le _ _).trans hA) hB
  have hdR : rightDeriv.totalDegree ≤ 2 :=
    degree_add_le ((degree_C_mul_le _ _).trans hA) hB
  have hd : disc.totalDegree ≤ 4 := by
    apply degree_sub_le
    · exact (MvPolynomial.totalDegree_mul _ _).trans
        (add_le_add ((degree_C_mul_le _ _).trans hA) hC)
    · exact (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 hB)
  refine ⟨p, {w | SignPositive strict (w 0) ∧ SignPositive strict (w 1) ∧
    (w 2 ≤ 0 ∨ 0 ≤ w 3 ∨ w 4 ≤ 0 ∨ SignPositive strict (w 5))}, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact (ht l).trans (by decide)
    · exact (ht r).trans (by decide)
    · exact hA.trans (by decide)
    · exact hdL.trans (by decide)
    · exact hdR.trans (by decide)
    · exact hd
  · intro x
    simp only [Set.mem_setOf_eq, p, Matrix.cons_val_zero, Matrix.cons_val_succ,
      signPositive_iff, sign_nonpos_iff, sign_nonneg_iff]
    simpa [atTime, leftDeriv, rightDeriv, disc, mul_comm, mul_left_comm, mul_assoc] using
      (quadratic_positive_iff strict (MvPolynomial.eval (v x) A)
        (MvPolynomial.eval (v x) B) (MvPolynomial.eval (v x) C) l r hlr).symm

/-- Interpolation turns a quadratic family of polynomials into a uniform sign description. -/
lemma SignRep.quadratic_family (v : X → σ → ℝ) (strict : Bool)
    (F : ℝ → MvPolynomial σ ℝ) (hdeg : ∀ t, (F t).totalDegree ≤ 2)
    (hquad : ∀ x, Quadratic (fun t => MvPolynomial.eval (v x) (F t)))
    (l r : ℝ) (hlr : l ≤ r) :
    SignRep v 6 4 (fun x => ∀ t ∈ Set.Icc l r,
      Positive strict (MvPolynomial.eval (v x) (F t))) := by
  let A := MvPolynomial.C (1 / 2) * (F 1 + F (-1)) - F 0
  let B := MvPolynomial.C (1 / 2) * (F 1 - F (-1))
  have hA : A.totalDegree ≤ 2 := degree_sub_le
    ((degree_C_mul_le _ _).trans (degree_add_le (hdeg 1) (hdeg (-1)))) (hdeg 0)
  have hB : B.totalDegree ≤ 2 := (degree_C_mul_le _ _).trans
    (degree_sub_le (hdeg 1) (hdeg (-1)))
  refine (SignRep.quadratic v strict A B (F 0) hA hB (hdeg 0) l r hlr).congr ?_
  intro x
  apply forall₂_congr
  intro t ht
  have heq : MvPolynomial.eval (v x) (F t) =
      MvPolynomial.eval (v x) A * t ^ 2 + MvPolynomial.eval (v x) B * t +
        MvPolynomial.eval (v x) (F 0) := by
    calc
      _ = ((MvPolynomial.eval (v x) (F 1) + MvPolynomial.eval (v x) (F (-1))) / 2 -
          MvPolynomial.eval (v x) (F 0)) * t ^ 2 +
          ((MvPolynomial.eval (v x) (F 1) - MvPolynomial.eval (v x) (F (-1))) / 2) * t +
          MvPolynomial.eval (v x) (F 0) := (hquad x).interpolation t
      _ = _ := by simp [A, B]; ring
  rw [heq]

end
end Submission.Obl.k4_eligibility_sign_description
