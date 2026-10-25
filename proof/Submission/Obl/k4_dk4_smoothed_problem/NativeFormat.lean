/- Adapted within this LOT tree from o006/x0006, Submission/Obl/k4_core/Framework/NativeFormat.lean,
commit c0ee4c6. Prior attributions are retained below. -/

import Submission.Obl.k4_dk4_smoothed_problem.BooleanFormat
import Submission.Obl.k4_dk4_smoothed_problem.Observation
import Submission.Obl.k4_dk4_smoothed_problem.CoefficientCoordinates

/-!
# Boolean polynomial formats for the native smoothing construction

This extends x0154's `HasBoolPolynomialFormat` rather than introducing a second
encoding. Coordinate boxes use two linear threshold tests per coordinate; finite
unions concatenate the test families.
-/

namespace Submission.Obl.k4_dk4_smoothed_problem

open Set

theorem HasBoolPolynomialFormat.empty {σ X : Type*} (coord : X → σ → ℝ) (D : ℕ) :
    HasBoolPolynomialFormat coord ∅ 0 D := by
  refine ⟨Fin.elim0, (fun i => Fin.elim0 i), (fun _ => false), ?_⟩
  intro x
  simp

theorem HasBoolPolynomialFormat.univ {σ X : Type*} (coord : X → σ → ℝ) (D : ℕ) :
    HasBoolPolynomialFormat coord Set.univ 0 D := by
  refine ⟨Fin.elim0, (fun i => Fin.elim0 i), (fun _ => true), ?_⟩
  intro x
  simp

theorem HasBoolPolynomialFormat.compl {σ X : Type*} {coord : X → σ → ℝ}
    {S : Set X} {m d : ℕ} (hS : HasBoolPolynomialFormat coord S m d) :
    HasBoolPolynomialFormat coord Sᶜ m d := by
  classical
  obtain ⟨p, hp, b, hb⟩ := hS
  refine ⟨p, hp, (fun v => !(b v)), ?_⟩
  intro x
  change (¬ x ∈ S) ↔ (! b (fun i => decide (0 ≤ MvPolynomial.eval (coord x) (p i)))) = true
  rw [hb x]
  cases b (fun i => decide (0 ≤ MvPolynomial.eval (coord x) (p i))) <;> decide

theorem HasBoolPolynomialFormat.nonneg {σ X : Type*} (coord : X → σ → ℝ)
    (P : MvPolynomial σ ℝ) (D : ℕ) (hP : P.totalDegree ≤ D) :
    HasBoolPolynomialFormat coord {x | 0 ≤ MvPolynomial.eval (coord x) P} 1 D := by
  classical
  refine ⟨fun _ => P, fun _ => hP, (fun v => v 0), ?_⟩
  intro x
  simp

theorem HasBoolPolynomialFormat.lt_zero {σ X : Type*} (coord : X → σ → ℝ)
    (P : MvPolynomial σ ℝ) (D : ℕ) (hP : P.totalDegree ≤ D) :
    HasBoolPolynomialFormat coord {x | MvPolynomial.eval (coord x) P < 0} 1 D := by
  convert (HasBoolPolynomialFormat.nonneg coord P D hP).compl using 1
  ext x
  simp

/-- A finite union of equally bounded sign predicates is still in the same
individual-degree format, with the sum of their atom counts. -/
theorem HasBoolPolynomialFormat.iUnion {σ X : Type*} {coord : X → σ → ℝ}
    {n m d : ℕ} (S : Fin n → Set X)
    (hS : ∀ j, HasBoolPolynomialFormat coord (S j) m d) :
    HasBoolPolynomialFormat coord (⋃ j, S j) (n * m) d := by
  classical
  simp only [HasBoolPolynomialFormat] at hS
  choose p hp b hb using hS
  let e : Fin (n * m) ≃ Fin n × Fin m := finProdFinEquiv.symm
  refine ⟨fun i => p (e i).1 (e i).2, fun i => hp (e i).1 (e i).2,
    (fun v => decide (∃ j, b j (fun a => v (e.symm (j, a))) = true)), ?_⟩
  intro x
  simp only [Set.mem_iUnion, decide_eq_true_eq, Equiv.apply_symm_apply]
  exact exists_congr fun j => hb j x

/-- An arbitrary coordinate box uses two degree-one atoms per coordinate. -/
theorem HasBoolPolynomialFormat.coordinate_box_on {σ X : Type*} {n : ℕ}
    (coord : X → σ → ℝ) (indices : Fin n → σ) (lo hi : Fin n → ℝ) :
    HasBoolPolynomialFormat coord {x | (fun j => coord x (indices j)) ∈ Icc lo hi}
      (n + n) 1 := by
  classical
  let p : Fin (n + n) → MvPolynomial σ ℝ :=
    Fin.addCases (fun j => MvPolynomial.X (indices j) - MvPolynomial.C (lo j))
      (fun j => MvPolynomial.C (hi j) - MvPolynomial.X (indices j))
  have hp : ∀ i, (p i).totalDegree ≤ 1 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [p, Fin.addCases_left] using
        (MvPolynomial.totalDegree_sub (MvPolynomial.X (indices j)) (MvPolynomial.C (lo j))).trans
          (by simp)
    · simpa only [p, Fin.addCases_right] using
        (MvPolynomial.totalDegree_sub (MvPolynomial.C (hi j)) (MvPolynomial.X (indices j))).trans
          (by simp)
  refine ⟨p, hp, (fun v => decide (∀ i, v i = true)), ?_⟩
  intro x
  simp only [decide_eq_true_eq]
  change (lo ≤ (fun j => coord x (indices j)) ∧ (fun j => coord x (indices j)) ≤ hi) ↔ ∀ i, 0 ≤ MvPolynomial.eval (coord x) (p i)
  constructor
  · intro hx i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [p, Fin.addCases_left, Fin.addCases_right, map_sub,
        MvPolynomial.eval_X, MvPolynomial.eval_C, sub_nonneg] using hx.1 j
    · simpa only [p, Fin.addCases_left, Fin.addCases_right, map_sub,
        MvPolynomial.eval_X, MvPolynomial.eval_C, sub_nonneg] using hx.2 j
  · intro hx
    constructor
    · intro j
      simpa only [p, Fin.addCases_left, Fin.addCases_right, map_sub,
        MvPolynomial.eval_X, MvPolynomial.eval_C, sub_nonneg] using hx (Fin.castAdd n j)
    · intro j
      simpa only [p, Fin.addCases_left, Fin.addCases_right, map_sub,
        MvPolynomial.eval_X, MvPolynomial.eval_C, sub_nonneg] using hx (Fin.natAdd n j)

theorem HasBoolPolynomialFormat.coordinate_box {X : Type*} {n : ℕ}
    (coord : X → Fin n → ℝ) (lo hi : Fin n → ℝ) :
    HasBoolPolynomialFormat coord {x | coord x ∈ Icc lo hi} (n + n) 1 :=
  HasBoolPolynomialFormat.coordinate_box_on coord id lo hi

end Submission.Obl.k4_dk4_smoothed_problem

namespace Submission.Obl.k4_dk4_smoothed_problem.Framework

open Set

/-- Physical point as a function of six coefficients followed by time. -/
def nativePoint (x : Fin 7 → ℝ) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![x 6, x 0 + x 6 * x 3, x 1 + x 6 * x 4, x 2 + x 6 * x 5]

noncomputable def nativeCoordinatePolynomials : Fin 4 → MvPolynomial (Fin 7) ℝ :=
  ![MvPolynomial.X 6,
    MvPolynomial.X 0 + MvPolynomial.X 6 * MvPolynomial.X 3,
    MvPolynomial.X 1 + MvPolynomial.X 6 * MvPolynomial.X 4,
    MvPolynomial.X 2 + MvPolynomial.X 6 * MvPolynomial.X 5]

theorem eval_nativeCoordinatePolynomials (x : Fin 7 → ℝ) (j : Fin 4) :
    MvPolynomial.eval x (nativeCoordinatePolynomials j) = nativePoint x j := by
  fin_cases j <;> simp [nativeCoordinatePolynomials, nativePoint]

theorem degree_nativeCoordinatePolynomials (j : Fin 4) :
    (nativeCoordinatePolynomials j).totalDegree ≤ 2 := by
  fin_cases j
  · simp [nativeCoordinatePolynomials]
  all_goals
    dsimp [nativeCoordinatePolynomials]
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le (by simp) ?_)
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

noncomputable def nativeBallPolynomial (z : EuclideanSpace ℝ (Fin 4)) (r : ℝ) :
    MvPolynomial (Fin 7) ℝ :=
  (∑ j : Fin 4, (nativeCoordinatePolynomials j - MvPolynomial.C (z j)) ^ 2) -
    MvPolynomial.C (r ^ 2)

theorem degree_nativeBallPolynomial (z : EuclideanSpace ℝ (Fin 4)) (r : ℝ) :
    (nativeBallPolynomial z r).totalDegree ≤ 4 := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  refine max_le (MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_) ?_
  · apply (MvPolynomial.totalDegree_pow _ _).trans
    have hsub : (nativeCoordinatePolynomials j - MvPolynomial.C (z j)).totalDegree ≤ 2 :=
      (MvPolynomial.totalDegree_sub _ _).trans
        (max_le (degree_nativeCoordinatePolynomials j) (by simp))
    exact (Nat.mul_le_mul_left 2 hsub).trans (by norm_num)
  · change (MvPolynomial.C (r ^ 2) : MvPolynomial (Fin 7) ℝ).totalDegree ≤ 4
    rw [MvPolynomial.totalDegree_C]
    omega

theorem eval_nativeBallPolynomial (x : Fin 7 → ℝ) (z : EuclideanSpace ℝ (Fin 4)) (r : ℝ) :
    MvPolynomial.eval x (nativeBallPolynomial z r) = ‖nativePoint x - z‖ ^ 2 - r ^ 2 := by
  simp [nativeBallPolynomial, eval_nativeCoordinatePolynomials,
    EuclideanSpace.norm_sq_eq, Real.norm_eq_abs]

theorem nativePoint_mem_ball_iff (x : Fin 7 → ℝ) (z : EuclideanSpace ℝ (Fin 4))
    {r : ℝ} (hr : 0 < r) :
    nativePoint x ∈ Metric.ball z r ↔ MvPolynomial.eval x (nativeBallPolynomial z r) < 0 := by
  rw [Metric.mem_ball, dist_eq_norm, eval_nativeBallPolynomial, sub_lt_zero,
    sq_lt_sq₀ (norm_nonneg _) hr.le]

theorem native_ball_format (z : EuclideanSpace ℝ (Fin 4)) {r : ℝ} (hr : 0 < r) :
    HasBoolPolynomialFormat id {x | nativePoint x ∈ Metric.ball z r} 1 4 := by
  convert HasBoolPolynomialFormat.lt_zero id (nativeBallPolynomial z r) 4
    (degree_nativeBallPolynomial z r) using 1
  ext x
  exact nativePoint_mem_ball_iff x z hr

theorem native_ball_union_format {m : ℕ} (z : Fin m → EuclideanSpace ℝ (Fin 4))
    (r : Fin m → ℝ) (hr : ∀ j, 0 < r j) :
    HasBoolPolynomialFormat id {x | nativePoint x ∈ ⋃ j, Metric.ball (z j) (r j)} m 4 := by
  have heq : {x | nativePoint x ∈ ⋃ j, Metric.ball (z j) (r j)} =
      ⋃ j, {x | nativePoint x ∈ Metric.ball (z j) (r j)} := by
    ext x
    simp
  rw [heq]
  simpa only [Nat.mul_one] using HasBoolPolynomialFormat.iUnion
    (fun j => {x | nativePoint x ∈ Metric.ball (z j) (r j)}) (fun j => native_ball_format (z j) (hr j))

theorem native_time_interval_format :
    HasBoolPolynomialFormat id {x : Fin 7 → ℝ | x 6 ∈ Icc (0 : ℝ) 1} 2 1 := by
  simpa [Set.mem_Icc, Pi.le_def] using HasBoolPolynomialFormat.coordinate_box_on
    (X := Fin 7 → ℝ) id (fun _ : Fin 1 => (6 : Fin 7)) (fun _ => 0) (fun _ => 1)

theorem native_incidence_format {m : ℕ} (z : Fin m → EuclideanSpace ℝ (Fin 4))
    (r : Fin m → ℝ) (hr : ∀ j, 0 < r j) :
    HasBoolPolynomialFormat id
      {x : Fin 7 → ℝ | x 6 ∈ Icc (0 : ℝ) 1 ∧ nativePoint x ∈ ⋃ j, Metric.ball (z j) (r j)}
      (2 + m) 4 := by
  have heq : {x : Fin 7 → ℝ | x 6 ∈ Icc (0 : ℝ) 1 ∧
      nativePoint x ∈ ⋃ j, Metric.ball (z j) (r j)} =
      {x : Fin 7 → ℝ | x 6 ∈ Icc (0 : ℝ) 1} ∩
        {x | nativePoint x ∈ ⋃ j, Metric.ball (z j) (r j)} := by
    ext x
    rfl
  rw [heq]
  exact native_time_interval_format.inter (native_ball_union_format z r hr)

theorem nativePoint_incidenceCoordinates (l : Coefficients) (t : ℝ) :
    nativePoint (Fin.snoc l.2 t) = WithLp.toLp 2 (trajectoryPoint l t) := by
  have h0 : (Fin.snoc l.2 t : Fin 7 → ℝ) (0 : Fin 7) = l.2 0 := Fin.snoc_castSucc (α := fun _ : Fin 7 => ℝ) t l.2 (0 : Fin 6)
  have h1 : (Fin.snoc l.2 t : Fin 7 → ℝ) (1 : Fin 7) = l.2 1 := Fin.snoc_castSucc (α := fun _ : Fin 7 => ℝ) t l.2 (1 : Fin 6)
  have h2 : (Fin.snoc l.2 t : Fin 7 → ℝ) (2 : Fin 7) = l.2 2 := Fin.snoc_castSucc (α := fun _ : Fin 7 => ℝ) t l.2 (2 : Fin 6)
  have h3 : (Fin.snoc l.2 t : Fin 7 → ℝ) (3 : Fin 7) = l.2 3 := Fin.snoc_castSucc (α := fun _ : Fin 7 => ℝ) t l.2 (3 : Fin 6)
  have h4 : (Fin.snoc l.2 t : Fin 7 → ℝ) (4 : Fin 7) = l.2 4 := Fin.snoc_castSucc (α := fun _ : Fin 7 => ℝ) t l.2 (4 : Fin 6)
  have h5 : (Fin.snoc l.2 t : Fin 7 → ℝ) (5 : Fin 7) = l.2 5 := Fin.snoc_castSucc (α := fun _ : Fin 7 => ℝ) t l.2 (5 : Fin 6)
  have h6 : (Fin.snoc l.2 t : Fin 7 → ℝ) (6 : Fin 7) = t := Fin.snoc_last (α := fun _ : Fin 7 => ℝ) t l.2
  ext j
  fin_cases j <;> simp [nativePoint, trajectoryPoint, h0, h1, h2, h3, h4, h5, h6]

/-- The support of one independently smoothed intercept/slope component is a
native degree-one set with twelve threshold atoms. -/
theorem native_packed_box_format (b0 b1 s0 s1 : Fin 3 → ℝ) :
    HasBoolPolynomialFormat id
      ((concatenateCoefficients 3 3).symm ⁻¹' (Icc b0 b1 ×ˢ Icc s0 s1)) 12 1 := by
  rw [preimage_prod_Icc_concatenateCoefficients]
  exact HasBoolPolynomialFormat.coordinate_box id _ _

/-- Coefficient box supports can be imposed on an incidence predicate without
introducing quantified variables. -/
theorem native_coefficient_box_format (lo hi : Fin 6 → ℝ) :
    HasBoolPolynomialFormat id
      {x : Fin 7 → ℝ | (fun j : Fin 6 => x j.castSucc) ∈ Icc lo hi} 12 1 :=
  HasBoolPolynomialFormat.coordinate_box_on id Fin.castSucc lo hi

theorem native_coefficient_box_union_format {n : ℕ} (lo hi : Fin n → Fin 6 → ℝ) :
    HasBoolPolynomialFormat id
      {x : Fin 7 → ℝ | ∃ j, (fun i : Fin 6 => x i.castSucc) ∈ Icc (lo j) (hi j)}
      (n * 12) 1 := by
  have h := HasBoolPolynomialFormat.iUnion
    (fun j => {x : Fin 7 → ℝ | (fun i : Fin 6 => x i.castSucc) ∈ Icc (lo j) (hi j)})
    (fun j => native_coefficient_box_format (lo j) (hi j))
  convert h using 1
  ext x
  simp

/-- The complete bounded initial incidence event has fixed individual degree
four and a linear atom count in the prior components and covering balls. -/
theorem native_bounded_incidence_format {n m : ℕ} (lo hi : Fin n → Fin 6 → ℝ)
    (z : Fin m → EuclideanSpace ℝ (Fin 4)) (r : Fin m → ℝ) (hr : ∀ j, 0 < r j) :
    HasBoolPolynomialFormat id
      {x : Fin 7 → ℝ | (∃ j, (fun i : Fin 6 => x i.castSucc) ∈ Icc (lo j) (hi j)) ∧
        x 6 ∈ Icc (0 : ℝ) 1 ∧ nativePoint x ∈ ⋃ j, Metric.ball (z j) (r j)}
      (n * 12 + (2 + m)) 4 := by
  have h := (native_coefficient_box_union_format lo hi).inter (native_incidence_format z r hr)
  convert h using 1
  · ext x
    rfl
  · norm_num

end Submission.Obl.k4_dk4_smoothed_problem.Framework
