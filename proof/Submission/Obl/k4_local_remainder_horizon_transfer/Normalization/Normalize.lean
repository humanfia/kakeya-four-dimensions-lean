/-
Adapted from this LOT tree, o064, session x0214, commit 1213d02,
Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/Normalize.lean.
Earlier provenance is preserved below.
-/
import Submission.Obl.k4_local_remainder_horizon_transfer.Normalization.Basic
import Submission.Obl.k4_local_remainder_horizon_transfer.Normalization.PolyAlgebra

/-!
# Normalizing through a parent chart (version 2)

A parent chart of a version-2 problem has a time block `[t₀, t₀ + q]`, an affine
spatial center `c + t u` and an invertible spatial matrix `D`. Paper Lemma 2.13
(`lem:normalization`) regards it as a new world with time `τ = (t - t₀) / q`,
spatial coordinate `z = D⁻¹ (y - c - t u)`, and the hidden coordinate `w`
retained. This file records the affine change of trajectory coefficients, the
corresponding change of graph points, and the lifting of child tests, centers
and frames back to the original coordinates.
-/

namespace Submission.Obl.k4_local_remainder_horizon_transfer.Normalization

open MvPolynomial

section DegreeOne

variable {σ : Type*}

theorem deg1_add {p q : MvPolynomial σ ℝ} (hp : p.totalDegree ≤ 1) (hq : q.totalDegree ≤ 1) :
    (p + q).totalDegree ≤ 1 := (totalDegree_add _ _).trans (max_le hp hq)

theorem deg1_sub {p q : MvPolynomial σ ℝ} (hp : p.totalDegree ≤ 1) (hq : q.totalDegree ≤ 1) :
    (p - q).totalDegree ≤ 1 := (totalDegree_sub _ _).trans (max_le hp hq)

theorem deg1_C_mul (a : ℝ) {p : MvPolynomial σ ℝ} (hp : p.totalDegree ≤ 1) :
    (C a * p).totalDegree ≤ 1 := (totalDegree_mul _ _).trans (by rw [totalDegree_C]; omega)

theorem deg1_mul_C (a : ℝ) {p : MvPolynomial σ ℝ} (hp : p.totalDegree ≤ 1) :
    (p * C a).totalDegree ≤ 1 := (totalDegree_mul _ _).trans (by rw [totalDegree_C]; omega)

theorem deg1_X (i : σ) : (X i : MvPolynomial σ ℝ).totalDegree ≤ 1 := by simp

theorem deg1_C (a : ℝ) : (C a : MvPolynomial σ ℝ).totalDegree ≤ 1 := by simp

end DegreeOne

/-- Evaluation of a substitution. -/
theorem eval_bind₁' {σ τ : Type*} (x : τ → ℝ) (g : σ → MvPolynomial τ ℝ)
    (φ : MvPolynomial σ ℝ) :
    eval x (bind₁ g φ) = eval (fun i => eval x (g i)) φ := by
  have := eval₂Hom_bind₁ (RingHom.id ℝ) x g φ
  simpa [MvPolynomial.coe_eval₂Hom] using this

/-- The data of a parent chart used for normalization. -/
structure Frame where
  /-- start of the time block -/
  t₀ : ℝ
  /-- length of the time block -/
  q : ℝ
  /-- spatial center at time zero -/
  c : Plane
  /-- spatial center velocity -/
  u : Plane
  /-- spatial matrix -/
  D : Matrix (Fin 2) (Fin 2) ℝ

namespace Frame

variable (F : Frame)

/-- The normalized coefficients of a trajectory. -/
noncomputable def normCoeff (l : Fin 6 → ℝ) : Fin 6 → ℝ :=
  let a₀ := l 0 + F.t₀ * l 3 - F.c 0 - F.t₀ * F.u 0
  let a₁ := l 1 + F.t₀ * l 4 - F.c 1 - F.t₀ * F.u 1
  let b₀ := l 3 - F.u 0
  let b₁ := l 4 - F.u 1
  ![F.D⁻¹ 0 0 * a₀ + F.D⁻¹ 0 1 * a₁,
    F.D⁻¹ 1 0 * a₀ + F.D⁻¹ 1 1 * a₁,
    l 2 + F.t₀ * l 5,
    F.q * (F.D⁻¹ 0 0 * b₀ + F.D⁻¹ 0 1 * b₁),
    F.q * (F.D⁻¹ 1 0 * b₀ + F.D⁻¹ 1 1 * b₁),
    F.q * l 5]

/-- The normalized trajectory; the internal index is kept. -/
noncomputable def normTraj (l : Trajectory) : Trajectory := (l.1, F.normCoeff l.2)

/-- The affine substitution expressing normalized graph coordinates through the
original ones: `τ = (t - t₀) / q`, `z = D⁻¹ (y - c - t u)`, `w = w`. -/
noncomputable def subst : Fin 4 → MvPolynomial (Fin 4) ℝ :=
  ![C F.q⁻¹ * (X 0 - C F.t₀),
    C (F.D⁻¹ 0 0) * (X 1 - C (F.c 0) - X 0 * C (F.u 0)) +
      C (F.D⁻¹ 0 1) * (X 2 - C (F.c 1) - X 0 * C (F.u 1)),
    C (F.D⁻¹ 1 0) * (X 1 - C (F.c 0) - X 0 * C (F.u 0)) +
      C (F.D⁻¹ 1 1) * (X 2 - C (F.c 1) - X 0 * C (F.u 1)),
    X 3]

/-- Evaluating the substitution at an original graph point gives the normalized
graph point at the normalized time. -/
theorem eval_subst (hq : F.q ≠ 0) (l : Trajectory) (t : ℝ) :
    (fun i => eval (graphPoint l t) (F.subst i)) =
      graphPoint (F.normTraj l) ((t - F.t₀) / F.q) := by
  funext i
  fin_cases i <;>
    simp [subst, graphPoint, normTraj, normCoeff] <;> field_simp <;> ring

theorem totalDegree_subst_le (i : Fin 4) : (F.subst i).totalDegree ≤ 1 := by
  fin_cases i
  · exact deg1_C_mul _ (deg1_sub (deg1_X _) (deg1_C _))
  · exact deg1_add (deg1_C_mul _ (deg1_sub (deg1_sub (deg1_X _) (deg1_C _))
      (deg1_mul_C _ (deg1_X _)))) (deg1_C_mul _ (deg1_sub (deg1_sub (deg1_X _) (deg1_C _))
      (deg1_mul_C _ (deg1_X _))))
  · exact deg1_add (deg1_C_mul _ (deg1_sub (deg1_sub (deg1_X _) (deg1_C _))
      (deg1_mul_C _ (deg1_X _)))) (deg1_C_mul _ (deg1_sub (deg1_sub (deg1_X _) (deg1_C _))
      (deg1_mul_C _ (deg1_X _))))
  · exact deg1_X _

theorem pderiv_three_subst_three : pderiv (3 : Fin 4) (F.subst 3) = 1 := by
  simp [subst]

theorem pderiv_three_subst_of_ne (j : Fin 4) (hj : j ≠ 3) :
    pderiv (3 : Fin 4) (F.subst j) = 0 := by
  fin_cases j <;> simp_all [subst, pderiv_X]

/-- The lifted test `δ · R'(τ, z, w)` in original graph coordinates. -/
noncomputable def liftTest (δ : ℝ) (R : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 4) ℝ :=
  δ • bind₁ F.subst R

theorem eval_liftTest (hq : F.q ≠ 0) (δ : ℝ) (R : MvPolynomial (Fin 4) ℝ)
    (l : Trajectory) (t : ℝ) :
    eval (graphPoint l t) (F.liftTest δ R) =
      δ * eval (graphPoint (F.normTraj l) ((t - F.t₀) / F.q)) R := by
  rw [liftTest, MvPolynomial.smul_eval, ← F.eval_subst hq l t, eval_bind₁']

theorem pderiv_liftTest (δ : ℝ) (R : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (F.liftTest δ R) = F.liftTest δ (pderiv 3 R) := by
  rw [liftTest, liftTest, Derivation.map_smul,
    pderiv_bind₁_of_diagonal F.subst 3 F.pderiv_three_subst_three F.pderiv_three_subst_of_ne]

theorem totalDegree_liftTest_le (δ : ℝ) (R : MvPolynomial (Fin 4) ℝ) :
    (F.liftTest δ R).totalDegree ≤ R.totalDegree :=
  (totalDegree_smul_le _ _).trans (totalDegree_bind₁_le_of_le_one _ F.totalDegree_subst_le R)

/-- The lifted spatial center. -/
noncomputable def liftCenter (c' u' : Plane) : Plane :=
  F.c + Matrix.toEuclideanLin F.D c' - (F.t₀ / F.q) • Matrix.toEuclideanLin F.D u'

/-- The lifted spatial center velocity. -/
noncomputable def liftSpeed (u' : Plane) : Plane := F.u + F.q⁻¹ • Matrix.toEuclideanLin F.D u'

theorem planarPoint_normTraj (hq : F.q ≠ 0) (l : Trajectory) (t : ℝ) :
    planarPoint (F.normTraj l) ((t - F.t₀) / F.q) =
      Matrix.toEuclideanLin F.D⁻¹ (planarPoint l t - F.c - t • F.u) := by
  ext i
  fin_cases i <;>
    simp [planarPoint, normTraj, normCoeff, Matrix.toLpLin_apply,
      Matrix.vecHead, Matrix.vecTail] <;>
    field_simp <;> ring

theorem toEuclideanLin_mul_inv_apply (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : IsUnit A.det)
    (v : Plane) : Matrix.toEuclideanLin A (Matrix.toEuclideanLin A⁻¹ v) = v := by
  have h := Matrix.toLpLin_mul_same (p := 2) A A⁻¹
  rw [Matrix.mul_nonsing_inv A hA, Matrix.toLpLin_one] at h
  have := congrArg (fun f => f v) h
  simpa using this.symm

theorem planar_lift (hq : F.q ≠ 0) (hD : IsUnit F.D.det) (c' u' : Plane) (l : Trajectory)
    (t : ℝ) :
    planarPoint l t - F.liftCenter c' u' - t • F.liftSpeed u' =
      Matrix.toEuclideanLin F.D (planarPoint (F.normTraj l) ((t - F.t₀) / F.q) - c' -
        ((t - F.t₀) / F.q) • u') := by
  rw [F.planarPoint_normTraj hq, map_sub, map_sub, map_smul,
    toEuclideanLin_mul_inv_apply F.D hD, liftCenter, liftSpeed]
  have : (t - F.t₀) / F.q = t * F.q⁻¹ - F.t₀ / F.q := by field_simp
  rw [this]
  module

theorem toEuclideanLin_inv_mul_apply (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : IsUnit A.det)
    (v : Plane) : Matrix.toEuclideanLin A⁻¹ (Matrix.toEuclideanLin A v) = v := by
  have h := Matrix.toLpLin_mul_same (p := 2) A⁻¹ A
  rw [Matrix.nonsing_inv_mul A hA, Matrix.toLpLin_one] at h
  have := congrArg (fun f => f v) h
  simpa using this.symm

theorem frame_lift (hq : F.q ≠ 0) (hD : IsUnit F.D.det) (Q' : Matrix (Fin 2) (Fin 2) ℝ)
    (c' u' : Plane) (l : Trajectory) (t : ℝ) :
    Matrix.toEuclideanLin (F.D * Q')⁻¹
        (planarPoint l t - F.liftCenter c' u' - t • F.liftSpeed u') =
      Matrix.toEuclideanLin Q'⁻¹ (planarPoint (F.normTraj l) ((t - F.t₀) / F.q) - c' -
        ((t - F.t₀) / F.q) • u') := by
  rw [F.planar_lift hq hD, Matrix.mul_inv_rev, Matrix.toLpLin_mul_same, LinearMap.comp_apply,
    toEuclideanLin_inv_mul_apply F.D hD]

end Frame

/-- The entrywise `ℓ¹` norm of `2 × 2` matrices is submultiplicative. -/
theorem matrix_l1_mul_le (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    (∑ e : Fin 2, ∑ e' : Fin 2, |(A * B) e e'|) ≤
      (∑ e : Fin 2, ∑ e' : Fin 2, |A e e'|) * (∑ e : Fin 2, ∑ e' : Fin 2, |B e e'|) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  have h := fun (a b c d : ℝ) => abs_add_le (a * b) (c * d)
  simp only [abs_mul] at h
  nlinarith [h (A 0 0) (B 0 0) (A 0 1) (B 1 0), h (A 0 0) (B 0 1) (A 0 1) (B 1 1),
    h (A 1 0) (B 0 0) (A 1 1) (B 1 0), h (A 1 0) (B 0 1) (A 1 1) (B 1 1),
    abs_nonneg (A 0 0), abs_nonneg (A 0 1), abs_nonneg (A 1 0), abs_nonneg (A 1 1),
    abs_nonneg (B 0 0), abs_nonneg (B 0 1), abs_nonneg (B 1 0), abs_nonneg (B 1 1),
    mul_nonneg (abs_nonneg (A 0 0)) (abs_nonneg (B 0 0))]

/-- The block of the finer common partition obtained by subdividing block `j₀`
of the coarse one. -/
def liftBlock {T₀ T' : ℕ} (j₀ : Fin (2 ^ T₀)) (j' : Fin (2 ^ T')) : Fin (2 ^ (T₀ + T')) :=
  ⟨(j₀ : ℕ) * 2 ^ T' + j', by
    have h1 : (j₀ : ℕ) + 1 ≤ 2 ^ T₀ := j₀.2
    have h2 : (j' : ℕ) < 2 ^ T' := j'.2
    calc (j₀ : ℕ) * 2 ^ T' + j' < (j₀ : ℕ) * 2 ^ T' + 2 ^ T' := by omega
      _ = ((j₀ : ℕ) + 1) * 2 ^ T' := by ring
      _ ≤ 2 ^ T₀ * 2 ^ T' := Nat.mul_le_mul_right _ h1
      _ = 2 ^ (T₀ + T') := by rw [pow_add]⟩

theorem mem_timeBlock_liftBlock {T₀ T' : ℕ} (j₀ : Fin (2 ^ T₀)) (j' : Fin (2 ^ T')) (t : ℝ) :
    t ∈ timeBlock (T₀ + T') (liftBlock j₀ j') ↔
      (t - ((j₀ : ℕ) : ℝ) / (2 : ℝ) ^ T₀) / (1 / (2 : ℝ) ^ T₀) ∈ timeBlock T' j' := by
  have ha : (0 : ℝ) < (2 : ℝ) ^ T₀ := by positivity
  have hb : (0 : ℝ) < (2 : ℝ) ^ T' := by positivity
  have hsimp : (t - ((j₀ : ℕ) : ℝ) / (2 : ℝ) ^ T₀) / (1 / (2 : ℝ) ^ T₀) =
      t * (2 : ℝ) ^ T₀ - (j₀ : ℕ) := by field_simp
  rw [hsimp]
  simp only [timeBlock, liftBlock, Set.mem_Icc, pow_add, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · rw [div_le_iff₀ hb]
      rw [div_le_iff₀ (mul_pos ha hb)] at h1
      nlinarith
    · rw [le_div_iff₀ hb]
      rw [le_div_iff₀ (mul_pos ha hb)] at h2
      nlinarith
  · rintro ⟨h1, h2⟩
    constructor
    · rw [div_le_iff₀ (mul_pos ha hb)]
      rw [div_le_iff₀ hb] at h1
      nlinarith
    · rw [le_div_iff₀ (mul_pos ha hb)]
      rw [le_div_iff₀ hb] at h2
      nlinarith

end Submission.Obl.k4_local_remainder_horizon_transfer.Normalization
