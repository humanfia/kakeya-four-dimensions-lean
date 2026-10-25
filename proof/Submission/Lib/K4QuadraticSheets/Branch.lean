import Mathlib
import Submission.Lib.K4QuadraticSheets.QuadTest

/-!
# Holomorphic root branches of quadratic tests

On a set where the discriminant of a quadratic test, divided by a fixed nonzero `λ`, stays in the
slit plane, the principal square root gives a holomorphic square root `S` of the discriminant, and
`(-β + S) / c` (or `-γ / β` when `c = 0`) is a holomorphic simple root of the test: the test
vanishes on it and its hidden derivative equals `S` (respectively `β`), which is nonzero.
These are exactly the sheets that the continuation input accepts.
-/

namespace Submission.Lib.K4QuadraticSheets

open MvPolynomial

section Differentiability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Evaluating a polynomial at differentiable coordinates is differentiable. -/
theorem differentiableAt_eval_comp {σ : Type*} {f : E → σ → ℂ} {z : E}
    (hf : ∀ i, DifferentiableAt ℂ (fun x => f x i) z) (p : MvPolynomial σ ℂ) :
    DifferentiableAt ℂ (fun x => eval (f x) p) z := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C]
    exact differentiableAt_const a
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, eval_X]
    exact hp.mul (hf i)

theorem differentiableOn_eval_comp {σ : Type*} {f : E → σ → ℂ} {s : Set E}
    (hf : ∀ i, DifferentiableOn ℂ (fun x => f x i) s) (hs : IsOpen s) (p : MvPolynomial σ ℂ) :
    DifferentiableOn ℂ (fun x => eval (f x) p) s := by
  intro z hz
  exact (differentiableAt_eval_comp
    (fun i => (hf i z hz).differentiableAt (hs.mem_nhds hz)) p).differentiableWithinAt

end Differentiability

section Coordinates

variable {n : ℕ}

/-- The coordinate function of the Euclidean space. -/
theorem differentiable_coord (j : Fin n) :
    Differentiable ℂ (fun z : EuclideanSpace ℂ (Fin n) => z j) :=
  (EuclideanSpace.proj (𝕜 := ℂ) j).differentiable

/-- The coordinates of `Fin.snoc z (g z)` are differentiable when `g` is. -/
theorem differentiableAt_snoc_coord {g : EuclideanSpace ℂ (Fin n) → ℂ}
    {z : EuclideanSpace ℂ (Fin n)} (hg : DifferentiableAt ℂ g z) (i : Fin (n + 1)) :
    DifferentiableAt ℂ (fun x : EuclideanSpace ℂ (Fin n) =>
      (Fin.snoc (fun j : Fin n => x j) (g x) : Fin (n + 1) → ℂ) i) z := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hg
  · simpa using (differentiable_coord j).differentiableAt

theorem differentiable_qb (P : MvPolynomial (Fin (n + 1)) ℂ) :
    Differentiable ℂ (fun z : EuclideanSpace ℂ (Fin n) => qb P (fun j => z j)) := by
  intro z
  exact differentiableAt_eval_comp
    (differentiableAt_snoc_coord (differentiableAt_const (0 : ℂ))) _

theorem differentiable_qg (P : MvPolynomial (Fin (n + 1)) ℂ) :
    Differentiable ℂ (fun z : EuclideanSpace ℂ (Fin n) => qg P (fun j => z j)) := by
  intro z
  exact differentiableAt_eval_comp
    (differentiableAt_snoc_coord (differentiableAt_const (0 : ℂ))) _

theorem differentiable_qdisc (P : MvPolynomial (Fin (n + 1)) ℂ) :
    Differentiable ℂ (fun z : EuclideanSpace ℂ (Fin n) => qdisc P (fun j => z j)) := by
  unfold qdisc
  exact ((differentiable_qb P).pow 2).sub ((differentiable_const _).mul (differentiable_qg P))

/-- The coordinates of `Fin.snoc z 0` are analytic. -/
theorem analyticAt_snoc_zero_coord (z : EuclideanSpace ℂ (Fin n)) (i : Fin (n + 1)) :
    AnalyticAt ℂ (fun x : EuclideanSpace ℂ (Fin n) =>
      (Fin.snoc (fun j : Fin n => x j) (0 : ℂ) : Fin (n + 1) → ℂ) i) z := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using analyticAt_const
  · simpa using (EuclideanSpace.proj (𝕜 := ℂ) j).analyticAt z

theorem analyticAt_eval_snoc_zero (Q : MvPolynomial (Fin (n + 1)) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) :
    AnalyticAt ℂ (fun x : EuclideanSpace ℂ (Fin n) =>
      eval (Fin.snoc (fun j : Fin n => x j) (0 : ℂ) : Fin (n + 1) → ℂ) Q) z := by
  have := AnalyticAt.aeval_mvPolynomial (A := ℂ) (B := ℂ)
    (f := fun x : EuclideanSpace ℂ (Fin n) =>
      (Fin.snoc (fun j : Fin n => x j) (0 : ℂ) : Fin (n + 1) → ℂ))
    (fun i => analyticAt_snoc_zero_coord z i) Q
  simpa [MvPolynomial.aeval_eq_eval] using this

theorem analyticAt_qb (P : MvPolynomial (Fin (n + 1)) ℂ) (z : EuclideanSpace ℂ (Fin n)) :
    AnalyticAt ℂ (fun z : EuclideanSpace ℂ (Fin n) => qb P (fun j => z j)) z :=
  analyticAt_eval_snoc_zero _ z

theorem analyticAt_qg (P : MvPolynomial (Fin (n + 1)) ℂ) (z : EuclideanSpace ℂ (Fin n)) :
    AnalyticAt ℂ (fun z : EuclideanSpace ℂ (Fin n) => qg P (fun j => z j)) z :=
  analyticAt_eval_snoc_zero _ z

theorem analyticAt_qdisc (P : MvPolynomial (Fin (n + 1)) ℂ) (z : EuclideanSpace ℂ (Fin n)) :
    AnalyticAt ℂ (fun z : EuclideanSpace ℂ (Fin n) => qdisc P (fun j => z j)) z := by
  unfold qdisc
  exact ((analyticAt_qb P z).pow 2).sub (analyticAt_const.mul (analyticAt_qg P z))

end Coordinates

section SquareRoot

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A rotated principal square root: `μ * (d / λ) ^ (1/2)`. -/
noncomputable def rotSqrt (lam μ d : ℂ) : ℂ := μ * (d / lam) ^ (1 / 2 : ℂ)

theorem rotSqrt_sq {lam μ : ℂ} (hlam : lam ≠ 0) (hμ : μ ^ 2 = lam) (d : ℂ) :
    rotSqrt lam μ d ^ 2 = d := by
  unfold rotSqrt
  have h2 : ((d / lam) ^ (1 / 2 : ℂ)) ^ 2 = d / lam := by
    have := Complex.cpow_nat_inv_pow (d / lam) (n := 2) (by norm_num)
    simp only [Nat.cast_ofNat] at this
    rw [one_div]
    exact this
  rw [mul_pow, h2, hμ]
  field_simp

theorem rotSqrt_ne_zero {lam μ : ℂ} (hlam : lam ≠ 0) (hμ : μ ^ 2 = lam) {d : ℂ} (hd : d ≠ 0) :
    rotSqrt lam μ d ≠ 0 := by
  intro h
  apply hd
  rw [← rotSqrt_sq hlam hμ d, h]
  ring

theorem analyticOnNhd_rotSqrt {lam μ : ℂ} {d : E → ℂ} {s : Set E}
    (hd : ∀ z ∈ s, AnalyticAt ℂ d z) (hslit : ∀ z ∈ s, d z / lam ∈ Complex.slitPlane) :
    AnalyticOnNhd ℂ (fun z => rotSqrt lam μ (d z)) s := by
  intro z hz
  unfold rotSqrt
  exact analyticAt_const.mul (((hd z hz).div analyticAt_const (by
    intro h0; have := hslit z hz; rw [h0, div_zero] at this
    exact Complex.slitPlane_ne_zero this rfl)).cpow analyticAt_const (hslit z hz))

theorem differentiableOn_rotSqrt {lam μ : ℂ} {d : E → ℂ} {s : Set E}
    (hd : DifferentiableOn ℂ d s) (hslit : ∀ z ∈ s, d z / lam ∈ Complex.slitPlane) :
    DifferentiableOn ℂ (fun z => rotSqrt lam μ (d z)) s := by
  unfold rotSqrt
  have h1 : DifferentiableOn ℂ (fun z => d z / lam) s := by
    simp only [div_eq_mul_inv]
    exact hd.mul_const _
  exact (differentiableOn_const μ).mul (h1.cpow_const hslit)

end SquareRoot

section Root

variable {n : ℕ}

/-- The root of the quadratic test selected by a square root `S` of its discriminant. -/
noncomputable def rootOf (P : MvPolynomial (Fin (n + 1)) ℂ) (z : Fin n → ℂ) (S : ℂ) : ℂ :=
  if qc P = 0 then -(qg P z) / qb P z else (-(qb P z) + S) / qc P

theorem eval_rootOf {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P.totalDegree ≤ 2)
    {z : Fin n → ℂ} {S : ℂ} (hS : S ^ 2 = qdisc P z) (hd : qdisc P z ≠ 0) :
    eval (Fin.snoc z (rootOf P z S) : Fin (n + 1) → ℂ) P = 0 := by
  rw [eval_snoc_quadratic P hP, rootOf]
  split_ifs with hc
  · have hb : qb P z ≠ 0 := by
      intro hb
      apply hd
      rw [qdisc, hb, hc]
      ring
    rw [hc]
    field_simp
    ring
  · have key : qg P z + qb P z * ((-qb P z + S) / qc P) + qc P / 2 * ((-qb P z + S) / qc P) ^ 2
        = (S ^ 2 - (qb P z ^ 2 - 2 * qc P * qg P z)) / (2 * qc P) := by
      field_simp
      ring
    rw [key, hS, qdisc, sub_self, zero_div]

theorem eval_pderiv_rootOf {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P.totalDegree ≤ 2)
    {z : Fin n → ℂ} {S : ℂ} (hS : S ^ 2 = qdisc P z) (hd : qdisc P z ≠ 0) :
    eval (Fin.snoc z (rootOf P z S) : Fin (n + 1) → ℂ) (pderiv (Fin.last n) P) ≠ 0 := by
  have h := pderiv_sq_eq_qdisc_of_root P hP z _ (eval_rootOf hP hS hd)
  intro h0
  rw [h0] at h
  exact hd (by rw [← h]; ring)

theorem eval_pderiv_rootOf_of_qc_ne_zero {P : MvPolynomial (Fin (n + 1)) ℂ}
    (hP : P.totalDegree ≤ 2) (hc : qc P ≠ 0) (z : Fin n → ℂ) (S : ℂ) :
    eval (Fin.snoc z (rootOf P z S) : Fin (n + 1) → ℂ) (pderiv (Fin.last n) P) = S := by
  rw [eval_snoc_pderiv P hP]
  simp only [rootOf, hc, ite_false]
  field_simp
  ring

/-- A holomorphic simple root branch of a test on an open set of the Euclidean space, built
from a holomorphic square root of its discriminant. -/
theorem differentiableOn_rootOf {P : MvPolynomial (Fin (n + 1)) ℂ}
    {S : EuclideanSpace ℂ (Fin n) → ℂ} {s : Set (EuclideanSpace ℂ (Fin n))}
    (hSd : DifferentiableOn ℂ S s) (hd : ∀ z ∈ s, qdisc P (fun j => z j) ≠ 0) :
    DifferentiableOn ℂ (fun z => rootOf P (fun j => z j) (S z)) s := by
  unfold rootOf
  by_cases hc : qc P = 0
  · simp only [hc, ite_true, div_eq_mul_inv]
    refine ((differentiable_qg P).neg.differentiableOn).mul
      ((differentiable_qb P).differentiableOn.inv ?_)
    intro z hz hb
    apply hd z hz
    rw [qdisc, hb, hc]
    ring
  · simp only [hc, ite_false, div_eq_mul_inv]
    exact (((differentiable_qb P).neg.differentiableOn).add hSd).mul_const _

/-- The root branch is analytic wherever the square root is and the discriminant is nonzero. -/
theorem analyticAt_rootOf {P : MvPolynomial (Fin (n + 1)) ℂ}
    {S : EuclideanSpace ℂ (Fin n) → ℂ} {z : EuclideanSpace ℂ (Fin n)}
    (hS : AnalyticAt ℂ S z) (hd : qdisc P (fun j => z j) ≠ 0) :
    AnalyticAt ℂ (fun z => rootOf P (fun j => z j) (S z)) z := by
  unfold rootOf
  by_cases hc : qc P = 0
  · simp only [hc, ite_true]
    refine AnalyticAt.div (analyticAt_qg P z).neg (analyticAt_qb P z) ?_
    intro hb
    apply hd
    rw [qdisc, hb, hc]
    ring
  · simp only [hc, ite_false]
    exact AnalyticAt.div ((analyticAt_qb P z).neg.add hS) analyticAt_const hc

theorem analyticOnNhd_rootOf {P : MvPolynomial (Fin (n + 1)) ℂ}
    {S : EuclideanSpace ℂ (Fin n) → ℂ} {s : Set (EuclideanSpace ℂ (Fin n))}
    (hS : AnalyticOnNhd ℂ S s) (hd : ∀ z ∈ s, qdisc P (fun j => z j) ≠ 0) :
    AnalyticOnNhd ℂ (fun z => rootOf P (fun j => z j) (S z)) s :=
  fun z hz => analyticAt_rootOf (hS z hz) (hd z hz)

/-- The sheet data accepted by the continuation input, from a holomorphic square root. -/
theorem sheet_of_sqrt {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P.totalDegree ≤ 2)
    {S : EuclideanSpace ℂ (Fin n) → ℂ} {s : Set (EuclideanSpace ℂ (Fin n))}
    (hSd : DifferentiableOn ℂ S s) (hS : ∀ z ∈ s, S z ^ 2 = qdisc P (fun j => z j))
    (hd : ∀ z ∈ s, qdisc P (fun j => z j) ≠ 0) :
    DifferentiableOn ℂ (fun z => rootOf P (fun j => z j) (S z)) s ∧
      ∀ z ∈ s, eval (Fin.snoc (fun j : Fin n => z j) (rootOf P (fun j => z j) (S z)) :
          Fin (n + 1) → ℂ) P = 0 ∧
        eval (Fin.snoc (fun j : Fin n => z j) (rootOf P (fun j => z j) (S z)) :
          Fin (n + 1) → ℂ) (pderiv (Fin.last n) P) ≠ 0 :=
  ⟨differentiableOn_rootOf hSd hd, fun z hz =>
    ⟨eval_rootOf hP (hS z hz) (hd z hz), eval_pderiv_rootOf hP (hS z hz) (hd z hz)⟩⟩

end Root

end Submission.Lib.K4QuadraticSheets
