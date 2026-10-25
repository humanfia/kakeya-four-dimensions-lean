import Mathlib
import Submission.Obl.k4_quadratic_sheet_continuation.TuranAlg

/-!
# Reduction of polynomials in square roots to sums over subsets

A polynomial `q` in variables `Y i` with coefficients in `ℂ[X]`, evaluated at `Y i = s i t`
where `s i t ^ 2 = Δ i (t)`, equals `∑ T, N_T(t) ∏ i ∈ T, s i t` (`eval_eq_sum_reduce`), with
`deg N_T ≤ d + deg q` whenever every coefficient of `q` has degree at most `d`.
-/

namespace Submission.Obl.k4_quadratic_sheet_continuation

open Polynomial Finset

noncomputable section

variable {m : ℕ}

/-- All coefficients of `q` have degree at most `d`. -/
def CoeffDegLe (q : MvPolynomial (Fin m) ℂ[X]) (d : ℕ) : Prop :=
  ∀ ν, (q.coeff ν).natDegree ≤ d

namespace CoeffDegLe

theorem mono {q : MvPolynomial (Fin m) ℂ[X]} {d e : ℕ} (h : CoeffDegLe q d) (hde : d ≤ e) :
    CoeffDegLe q e := fun ν => (h ν).trans hde

theorem add {p q : MvPolynomial (Fin m) ℂ[X]} {d : ℕ} (hp : CoeffDegLe p d)
    (hq : CoeffDegLe q d) : CoeffDegLe (p + q) d := by
  intro ν
  rw [MvPolynomial.coeff_add]
  exact (natDegree_add_le _ _).trans (max_le (hp ν) (hq ν))

theorem sub {p q : MvPolynomial (Fin m) ℂ[X]} {d : ℕ} (hp : CoeffDegLe p d)
    (hq : CoeffDegLe q d) : CoeffDegLe (p - q) d := by
  intro ν
  rw [MvPolynomial.coeff_sub]
  exact (natDegree_sub_le _ _).trans (max_le (hp ν) (hq ν))

theorem neg {p : MvPolynomial (Fin m) ℂ[X]} {d : ℕ} (hp : CoeffDegLe p d) :
    CoeffDegLe (-p) d := by
  intro ν
  rw [MvPolynomial.coeff_neg, natDegree_neg]
  exact hp ν

theorem mul {p q : MvPolynomial (Fin m) ℂ[X]} {d e : ℕ} (hp : CoeffDegLe p d)
    (hq : CoeffDegLe q e) : CoeffDegLe (p * q) (d + e) := by
  classical
  intro ν
  rw [MvPolynomial.coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro x _
  exact natDegree_mul_le.trans (add_le_add (hp _) (hq _))

theorem C (a : ℂ[X]) : CoeffDegLe (MvPolynomial.C a : MvPolynomial (Fin m) ℂ[X]) a.natDegree := by
  classical
  intro ν
  rw [MvPolynomial.coeff_C]
  split_ifs
  · exact le_rfl
  · simp

theorem X (i : Fin m) : CoeffDegLe (MvPolynomial.X i : MvPolynomial (Fin m) ℂ[X]) 0 := by
  classical
  intro ν
  rw [MvPolynomial.coeff_X']
  split_ifs <;> simp

theorem pow {p : MvPolynomial (Fin m) ℂ[X]} {d : ℕ} (hp : CoeffDegLe p d) (k : ℕ) :
    CoeffDegLe (p ^ k) (k * d) := by
  induction k with
  | zero =>
    rw [pow_zero, zero_mul]
    have := C (m := m) 1
    simpa using this
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact ih.mul hp

theorem sum {ι : Type*} (S : Finset ι) (p : ι → MvPolynomial (Fin m) ℂ[X]) {d : ℕ}
    (hp : ∀ i ∈ S, CoeffDegLe (p i) d) : CoeffDegLe (∑ i ∈ S, p i) d := by
  classical
  intro ν
  rw [MvPolynomial.coeff_sum]
  exact natDegree_sum_le_of_forall_le _ _ (fun i hi => hp i hi ν)

theorem prod {ι : Type*} (S : Finset ι) (p : ι → MvPolynomial (Fin m) ℂ[X]) (d : ι → ℕ)
    (hp : ∀ i ∈ S, CoeffDegLe (p i) (d i)) : CoeffDegLe (∏ i ∈ S, p i) (∑ i ∈ S, d i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have := C (m := m) 1
    simpa using this
  | insert a S ha ih =>
    rw [prod_insert ha, sum_insert ha]
    exact (hp a (mem_insert_self a S)).mul (ih (fun i hi => hp i (mem_insert_of_mem hi)))

end CoeffDegLe

/-- The indices with odd exponent. -/
def oddSet (μ : Fin m →₀ ℕ) : Finset (Fin m) := univ.filter (fun i => μ i % 2 = 1)

/-- The numerator of the `T`-component after reducing `Y i ^ 2 = Δ i`. -/
def reduceN (Δ : Fin m → ℂ[X]) (q : MvPolynomial (Fin m) ℂ[X]) (T : Finset (Fin m)) : ℂ[X] :=
  ∑ μ ∈ q.support.filter (fun μ => oddSet μ = T), q.coeff μ * ∏ i, Δ i ^ (μ i / 2)

theorem natDegree_reduceN_le {Δ : Fin m → ℂ[X]} (hΔ : ∀ i, (Δ i).natDegree ≤ 2)
    {q : MvPolynomial (Fin m) ℂ[X]} {d : ℕ} (hq : CoeffDegLe q d) (T : Finset (Fin m)) :
    (reduceN Δ q T).natDegree ≤ d + q.totalDegree := by
  classical
  apply natDegree_sum_le_of_forall_le
  intro μ hμ
  have hμs : μ ∈ q.support := (mem_filter.mp hμ).1
  have htot : ∑ i, μ i ≤ q.totalDegree := by
    have := MvPolynomial.le_totalDegree hμs
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
  calc (q.coeff μ * ∏ i, Δ i ^ (μ i / 2)).natDegree
      ≤ (q.coeff μ).natDegree + (∏ i, Δ i ^ (μ i / 2)).natDegree := natDegree_mul_le
    _ ≤ d + ∑ i, (Δ i ^ (μ i / 2)).natDegree := add_le_add (hq μ) (natDegree_prod_le _ _)
    _ ≤ d + ∑ i, μ i := by
        gcongr with i
        calc (Δ i ^ (μ i / 2)).natDegree ≤ (μ i / 2) * (Δ i).natDegree := natDegree_pow_le
          _ ≤ (μ i / 2) * 2 := Nat.mul_le_mul_left _ (hΔ i)
          _ ≤ μ i := Nat.div_mul_le_self _ _
    _ ≤ d + q.totalDegree := by omega

theorem eval_eq_sum_reduce (Δ : Fin m → ℂ[X]) (s : Fin m → ℂ → ℂ) (q : MvPolynomial (Fin m) ℂ[X])
    {t : ℂ} (hsq : ∀ i, s i t ^ 2 = (Δ i).eval t) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom t) (fun i => s i t) q =
      ∑ T : Finset (Fin m), (reduceN Δ q T).eval t * radProd s T t := by
  classical
  rw [MvPolynomial.eval₂_eq']
  have hterm : ∀ μ ∈ q.support, (Polynomial.evalRingHom t) (q.coeff μ) * ∏ i, s i t ^ μ i =
      ((q.coeff μ) * ∏ i, Δ i ^ (μ i / 2)).eval t * radProd s (oddSet μ) t := by
    intro μ _
    rw [Polynomial.coe_evalRingHom, eval_mul, eval_prod, mul_assoc]
    congr 1
    rw [radProd, oddSet, prod_filter, ← prod_mul_distrib]
    apply prod_congr rfl
    intro i _
    rw [eval_pow, ← hsq i, ← pow_mul]
    conv_lhs => rw [← Nat.div_add_mod (μ i) 2, pow_add]
    rw [mul_comm 2 (μ i / 2)]
    congr 1
    rcases Nat.mod_two_eq_zero_or_one (μ i) with h | h
    · rw [h, if_neg (by omega), pow_zero]
    · rw [h, if_pos rfl, pow_one]
  rw [sum_congr rfl hterm]
  rw [← sum_fiberwise_of_maps_to (s := q.support) (t := univ) (g := oddSet)
    (fun _ _ => mem_univ _)]
  apply sum_congr rfl
  intro T _
  rw [reduceN, eval_finsetSum, sum_mul]
  apply sum_congr rfl
  intro μ hμ
  rw [(mem_filter.mp hμ).2]

end

end Submission.Obl.k4_quadratic_sheet_continuation
