/-
Adapted from: here:root
Original conic proofs by session x0001; pinned dimension argument attributed below.
-/
/-
The exponent-coordinate dimension argument is adapted from
LeanPool.MetricCodes, LeanPool/MetricCodes/HarmonicAnalysis.lean.
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/
import Mathlib

open MvPolynomial

namespace Submission.Lib.K4CubicTests

-- Adapted from LeanPool.MetricCodes.HarmonicAnalysis,
-- LeanPool/MetricCodes/HarmonicAnalysis.lean, exponent-coordinate dimension
-- argument (homogeneousExponentFinset through finrank_homogeneousSubmodule).
-- The original module registers an unrelated global numeral instance; the
-- finite-dimensional instance here is local to preserve frozen statements.
/-- The finite set of exponent vectors of total degree `m` in `n` variables. -/
private def homogeneousExponentFinset (n m : ℕ) :
    Finset (Fin n →₀ ℕ) :=
  (Finset.univ : Finset (Fin n)).finsuppAntidiag m

private abbrev HomogeneousExponent (n m : ℕ) :=
  ↥(homogeneousExponentFinset n m)

private theorem homogeneousExponentFinset_card (n m : ℕ) :
    (homogeneousExponentFinset n m).card =
      (n + m - 1).choose m := by
  classical
  simpa only [homogeneousExponentFinset, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_finsuppAntidiag_nat_eq_choose (s := (Finset.univ : Finset (Fin n))) m)

private theorem mem_homogeneousExponentFinset {n m : ℕ}
    (d : Fin n →₀ ℕ) :
    d ∈ homogeneousExponentFinset n m ↔ d.degree = m := by
  classical
  simp only [homogeneousExponentFinset, Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true,
    Finsupp.degree_eq_sum]

private theorem homogeneousSubmodule_eq_supported_exponents (n m : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin n) ℝ m =
      AddMonoidAlgebra.supported ℝ ℝ
        (homogeneousExponentFinset n m : Set (Fin n →₀ ℕ)) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  congr 1
  ext d
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_homogeneousExponentFinset]

private noncomputable def homogeneousCoefficientEquiv (n m : ℕ) :
    (MvPolynomial.homogeneousSubmodule (Fin n) ℝ m) ≃ₗ[ℝ]
      (HomogeneousExponent n m → ℝ) :=
  (LinearEquiv.ofEq _ _
    (homogeneousSubmodule_eq_supported_exponents n m)).trans
      ((AddMonoidAlgebra.supportedEquivFinsupp
        (homogeneousExponentFinset n m : Set (Fin n →₀ ℕ))).trans
        (Finsupp.linearEquivFunOnFinite ℝ ℝ
          (HomogeneousExponent n m)))

theorem homogeneousSubmodule_finiteDimensional (n m : ℕ) :
    FiniteDimensional ℝ
      (MvPolynomial.homogeneousSubmodule (Fin n) ℝ m) :=
  FiniteDimensional.of_injective
    (homogeneousCoefficientEquiv n m).toLinearMap
    (homogeneousCoefficientEquiv n m).injective

attribute [local instance] homogeneousSubmodule_finiteDimensional

theorem finrank_homogeneousSubmodule (n m : ℕ) :
    Module.finrank ℝ
      (MvPolynomial.homogeneousSubmodule (Fin n) ℝ m) =
        (n + m - 1).choose m := by
  calc
    Module.finrank ℝ
        (MvPolynomial.homogeneousSubmodule (Fin n) ℝ m) =
        Module.finrank ℝ (HomogeneousExponent n m → ℝ) :=
      (homogeneousCoefficientEquiv n m).finrank_eq
    _ = Fintype.card (HomogeneousExponent n m) :=
      Module.finrank_pi ℝ
    _ = (homogeneousExponentFinset n m).card :=
      Fintype.card_coe _
    _ = (n + m - 1).choose m :=
      homogeneousExponentFinset_card n m


/-- The linear polynomial of the line joining two projective points. -/
noncomputable def joiningLine (u v : Fin 3 → ℝ) : MvPolynomial (Fin 3) ℝ :=
  C (u 1 * v 2 - u 2 * v 1) * X 0 +
    C (u 2 * v 0 - u 0 * v 2) * X 1 +
    C (u 0 * v 1 - u 1 * v 0) * X 2

theorem joiningLine_isHomogeneous (u v : Fin 3 → ℝ) : (joiningLine u v).IsHomogeneous 1 :=
  ((isHomogeneous_C_mul_X _ _).add (isHomogeneous_C_mul_X _ _)).add (isHomogeneous_C_mul_X _ _)

theorem eval_joiningLine (u v w : Fin 3 → ℝ) :
    MvPolynomial.eval w (joiningLine u v) = Matrix.det (Matrix.of ![u, v, w]) := by
  rw [Matrix.det_fin_three]
  simp [joiningLine] <;> ring

theorem eval_joiningLine_left (u v : Fin 3 → ℝ) :
    MvPolynomial.eval u (joiningLine u v) = 0 := by
  simp [joiningLine] <;> ring

theorem eval_joiningLine_right (u v : Fin 3 → ℝ) :
    MvPolynomial.eval v (joiningLine u v) = 0 := by
  simp [joiningLine] <;> ring

/-- A cubic vanishing at the six projective points other than `i`. -/
noncomputable def cubicSeparator (p : Fin 7 → Fin 3 → ℝ) (i : Fin 7) : MvPolynomial (Fin 3) ℝ :=
  joiningLine (p (i.succAbove 0)) (p (i.succAbove 1)) *
    joiningLine (p (i.succAbove 2)) (p (i.succAbove 3)) *
    joiningLine (p (i.succAbove 4)) (p (i.succAbove 5))

theorem cubicSeparator_isHomogeneous (p : Fin 7 → Fin 3 → ℝ) (i : Fin 7) :
    (cubicSeparator p i).IsHomogeneous 3 := by
  exact ((joiningLine_isHomogeneous _ _).mul (joiningLine_isHomogeneous _ _)).mul
    (joiningLine_isHomogeneous _ _)

theorem eval_cubicSeparator_other (p : Fin 7 → Fin 3 → ℝ) {i j : Fin 7} (hji : j ≠ i) :
    MvPolynomial.eval (p j) (cubicSeparator p i) = 0 := by
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
  fin_cases k <;> simp [cubicSeparator, eval_joiningLine_left, eval_joiningLine_right]

theorem eval_cubicSeparator_self_ne_zero (p : Fin 7 → Fin 3 → ℝ)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → Matrix.det (Matrix.of ![p i, p j, p k]) ≠ 0)
    (i : Fin 7) : MvPolynomial.eval (p i) (cubicSeparator p i) ≠ 0 := by
  have hpair (a b : Fin 6) (hab : a ≠ b) :
      MvPolynomial.eval (p i) (joiningLine (p (i.succAbove a)) (p (i.succAbove b))) ≠ 0 := by
    rw [eval_joiningLine]
    exact hp _ _ _ (Fin.succAbove_right_injective.ne hab) (Fin.succAbove_ne _ _) (Fin.succAbove_ne _ _)
  simp only [cubicSeparator, map_mul]
  exact mul_ne_zero (mul_ne_zero (hpair 0 1 (by decide)) (hpair 2 3 (by decide)))
    (hpair 4 5 (by decide))

/-- A homogeneous cubic taking value one at `i` and zero at the other points. -/
noncomputable def cubicCardinalPolynomial (p : Fin 7 → Fin 3 → ℝ) (i : Fin 7) :
    MvPolynomial (Fin 3) ℝ :=
  C ((MvPolynomial.eval (p i) (cubicSeparator p i))⁻¹) * cubicSeparator p i

theorem cubicCardinalPolynomial_isHomogeneous (p : Fin 7 → Fin 3 → ℝ) (i : Fin 7) :
    (cubicCardinalPolynomial p i).IsHomogeneous 3 :=
  (cubicSeparator_isHomogeneous p i).C_mul _

theorem eval_cubicCardinalPolynomial (p : Fin 7 → Fin 3 → ℝ)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → Matrix.det (Matrix.of ![p i, p j, p k]) ≠ 0)
    (i j : Fin 7) :
    MvPolynomial.eval (p j) (cubicCardinalPolynomial p i) = if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp [cubicCardinalPolynomial, eval_cubicSeparator_self_ne_zero p hp i]
  · simp [cubicCardinalPolynomial, eval_cubicSeparator_other p (Ne.symm hij), hij]

/-- Homogeneous cubics interpolate arbitrary values on seven projectively general points. -/
theorem exists_homogeneous_cubic_interpolating (p : Fin 7 → Fin 3 → ℝ)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → Matrix.det (Matrix.of ![p i, p j, p k]) ≠ 0)
    (y : Fin 7 → ℝ) :
    ∃ F : MvPolynomial (Fin 3) ℝ, F.IsHomogeneous 3 ∧ ∀ i, MvPolynomial.eval (p i) F = y i := by
  classical
  refine ⟨∑ i : Fin 7, C (y i) * cubicCardinalPolynomial p i, ?_, ?_⟩
  · exact IsHomogeneous.sum _ _ _ fun i _ => (cubicCardinalPolynomial_isHomogeneous p i).C_mul _
  · intro j
    simp [map_sum, eval_cubicCardinalPolynomial p hp, Finset.sum_ite_eq']

/-- Evaluation of homogeneous ternary cubics on seven points. -/
noncomputable def evaluateCubics (p : Fin 7 → Fin 3 → ℝ) :
    MvPolynomial.homogeneousSubmodule (Fin 3) ℝ 3 →ₗ[ℝ] (Fin 7 → ℝ) where
  toFun F i := MvPolynomial.eval (p i) F.val
  map_add' F G := by ext i; simp
  map_smul' r F := by ext i; simp

theorem evaluateCubics_surjective (p : Fin 7 → Fin 3 → ℝ)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → Matrix.det (Matrix.of ![p i, p j, p k]) ≠ 0) :
    Function.Surjective (evaluateCubics p) := by
  intro y
  obtain ⟨F, hF, hy⟩ := exists_homogeneous_cubic_interpolating p hp y
  exact ⟨⟨F, hF⟩, funext hy⟩

/-- The cubics vanishing at the seven projective points form a three-dimensional space. -/
theorem finrank_cubic_vanishing (p : Fin 7 → Fin 3 → ℝ)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → Matrix.det (Matrix.of ![p i, p j, p k]) ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (evaluateCubics p)) = 3 := by
  have hdim := (evaluateCubics p).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (evaluateCubics_surjective p hp), finrank_top] at hdim
  have hhom : Module.finrank ℝ (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ 3) = 10 := by
    rw [finrank_homogeneousSubmodule]
    norm_num [Nat.choose]
  have hpi : Module.finrank ℝ (Fin 7 → ℝ) = 7 := by simp
  omega

/-- Multiplication by a homogeneous conic, restricted to homogeneous linear forms. -/
noncomputable def multiplyConic (q : MvPolynomial (Fin 3) ℝ) (hq : q.IsHomogeneous 2) :
    MvPolynomial.homogeneousSubmodule (Fin 3) ℝ 1 →ₗ[ℝ]
      MvPolynomial.homogeneousSubmodule (Fin 3) ℝ 3 where
  toFun L := ⟨q * L.val, hq.mul L.property⟩
  map_add' L M := by ext; simp [mul_add]
  map_smul' r L := by ext; simp [Algebra.smul_def, mul_left_comm, mul_assoc]

theorem multiplyConic_injective (q : MvPolynomial (Fin 3) ℝ) (hq : q.IsHomogeneous 2) (hne : q ≠ 0) :
    Function.Injective (multiplyConic q hq) := by
  intro L M h
  apply Subtype.ext
  exact mul_left_cancel₀ hne (congrArg Subtype.val h)

/-- The rank-three conic kernel in paper Lemma 6.6(3): every homogeneous cubic
vanishing at the seven points is the conic times a linear form. -/
theorem cubic_vanishing_eq_conic_mul_linear (p : Fin 7 → Fin 3 → ℝ)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → Matrix.det (Matrix.of ![p i, p j, p k]) ≠ 0)
    (q : MvPolynomial (Fin 3) ℝ) (hq : q.IsHomogeneous 2) (hne : q ≠ 0)
    (hqzero : ∀ i, MvPolynomial.eval (p i) q = 0)
    (F : MvPolynomial (Fin 3) ℝ) (hF : F.IsHomogeneous 3)
    (hFzero : ∀ i, MvPolynomial.eval (p i) F = 0) :
    ∃ L : MvPolynomial (Fin 3) ℝ, L.IsHomogeneous 1 ∧ F = q * L := by
  have hle : LinearMap.range (multiplyConic q hq) ≤ LinearMap.ker (evaluateCubics p) := by
    rintro _ ⟨L, rfl⟩
    apply LinearMap.mem_ker.mpr
    ext i
    change MvPolynomial.eval (p i) (q * L.val) = 0
    simp [hqzero i]
  have hrank : Module.finrank ℝ (LinearMap.range (multiplyConic q hq)) = 3 := by
    rw [LinearMap.finrank_range_of_inj (multiplyConic_injective q hq hne),
      finrank_homogeneousSubmodule]
    norm_num [Nat.choose]
  have heq : LinearMap.range (multiplyConic q hq) = LinearMap.ker (evaluateCubics p) :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hrank, finrank_cubic_vanishing p hp])
  have hmem : (⟨F, hF⟩ : MvPolynomial.homogeneousSubmodule (Fin 3) ℝ 3) ∈
      LinearMap.range (multiplyConic q hq) := by
    rw [heq]
    apply LinearMap.mem_ker.mpr
    exact funext hFzero
  obtain ⟨L, hL⟩ := hmem
  exact ⟨L.val, L.property, (congrArg Subtype.val hL).symm⟩

end Submission.Lib.K4CubicTests
