import Submission.Obl.k4_scalar_tangent_isotropic_improvement.PolynomialLipschitz
import Submission.Obl.k4_quadratic_selector_sweep.SignFibers

/-! Fixed-degree coefficient comparison and bounded affine polynomial substitutions. -/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

noncomputable section

open MvPolynomial
open scoped BigOperators

abbrev BinaryIndex (D : ℕ) := Fin (D + 1) × Fin (D + 1)

def boundedPolynomial (D : ℕ) (a : BinaryIndex D → ℝ) : MvPolynomial (Fin 2) ℝ :=
  ∑ b, monomial (binaryExponent b.1 b.2) (a b)

theorem binaryIndex_exponent_injective (D : ℕ) :
    Function.Injective (fun b : BinaryIndex D => binaryExponent b.1 b.2) := by
  intro b c h
  apply Prod.ext
  · exact Fin.ext (by simpa using congrArg (fun d : Fin 2 →₀ ℕ => d 0) h)
  · exact Fin.ext (by simpa using congrArg (fun d : Fin 2 →₀ ℕ => d 1) h)

@[simp] theorem boundedPolynomial_coeff (D : ℕ) (a : BinaryIndex D → ℝ) (b : BinaryIndex D) :
    (boundedPolynomial D a).coeff (binaryExponent b.1 b.2) = a b := by
  classical
  simp [boundedPolynomial, coeff_monomial, (binaryIndex_exponent_injective D).eq_iff]

theorem boundedPolynomial_reconstruct (D : ℕ) (p : MvPolynomial (Fin 2) ℝ)
    (hp : p.totalDegree ≤ D) :
    boundedPolynomial D (fun b => p.coeff (binaryExponent b.1 b.2)) = p := by
  classical
  ext d
  by_cases hb : d 0 ≤ D ∧ d 1 ≤ D
  · let b : BinaryIndex D := (⟨d 0, by omega⟩, ⟨d 1, by omega⟩)
    have he : binaryExponent b.1 b.2 = d := by ext i; fin_cases i <;> simp [b]
    rw [← he, boundedPolynomial_coeff]
  · have hzero : p.coeff d = 0 := by
      apply coeff_eq_zero_of_totalDegree_lt
      change p.totalDegree < d.sum (fun _ n => n)
      rw [binary_exponents_sum]
      omega
    rw [hzero]
    have hneq (b : BinaryIndex D) : binaryExponent b.1 b.2 ≠ d := by
      intro he
      have h0 : (b.1 : ℕ) = d 0 := by simpa using congrArg (fun e : Fin 2 →₀ ℕ => e 0) he
      have h1 : (b.2 : ℕ) = d 1 := by simpa using congrArg (fun e : Fin 2 →₀ ℕ => e 1) he
      have hb0 := b.1.isLt
      have hb1 := b.2.isLt
      omega
    simp only [boundedPolynomial, coeff_sum]
    exact Finset.sum_eq_zero (fun b hb => by simp [coeff_monomial, hneq b])

local instance boundedUnitBoxCompact : CompactSpace UnitBox :=
  isCompact_iff_compactSpace.mp isCompact_Icc

def coefficientEvaluationMap (D : ℕ) : (BinaryIndex D → ℝ) →ₗ[ℝ] C(UnitBox, ℝ) where
  toFun a := ⟨fun x => eval x.val (boundedPolynomial D a),
    (continuous_eval _).comp continuous_subtype_val⟩
  map_add' a b := by
    ext x
    simp [boundedPolynomial, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c a := by
    ext x
    change eval x.val (boundedPolynomial D (c • a)) = c * eval x.val (boundedPolynomial D a)
    simp only [boundedPolynomial, Pi.smul_apply, map_sum, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    simp only [eval_monomial]
    ring

theorem coefficientEvaluationMap_injective (D : ℕ) : Function.Injective (coefficientEvaluationMap D) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  have hpoly : boundedPolynomial D a = 0 := by
    apply MvPolynomial.funext_set (fun _ => Set.Icc (0 : ℝ) 1)
      (fun _ => Set.Icc_infinite (by norm_num))
    intro x hx
    have hx' : x ∈ UnitBox :=
      ⟨fun i => (hx i (by trivial)).1, fun i => (hx i (by trivial)).2⟩
    have h := congrArg (fun f : C(UnitBox, ℝ) => f ⟨x, hx'⟩) ha
    simpa [coefficientEvaluationMap] using h
  funext b
  have h := congrArg (fun p : MvPolynomial (Fin 2) ℝ => p.coeff (binaryExponent b.1 b.2)) hpoly
  simpa using h

theorem exists_binary_coefficient_bound (D : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (p : MvPolynomial (Fin 2) ℝ) (E : ℝ), p.totalDegree ≤ D → 0 ≤ E →
      (∀ x ∈ UnitBox, |eval x p| ≤ E) → ∀ b, |p.coeff b| ≤ C * E := by
  obtain ⟨C, hC, hanti⟩ :=
    (coefficientEvaluationMap D).injective_iff_antilipschitz.mp (coefficientEvaluationMap_injective D)
  refine ⟨C, hC, ?_⟩
  intro p E hp hE hbound d
  let a : BinaryIndex D → ℝ := fun b => p.coeff (binaryExponent b.1 b.2)
  have hnorm : ‖coefficientEvaluationMap D a‖ ≤ E := by
    apply (ContinuousMap.norm_le _ hE).mpr
    intro x
    have h := hbound x.val x.property
    simpa only [coefficientEvaluationMap, LinearMap.coe_mk, AddHom.coe_mk,
      ContinuousMap.coe_mk, a, boundedPolynomial_reconstruct D p hp, Real.norm_eq_abs] using h
  have ha (b : BinaryIndex D) : |a b| ≤ C * E :=
    (norm_le_pi_norm a b).trans
      ((ZeroHomClass.bound_of_antilipschitz (coefficientEvaluationMap D) hanti a).trans
        (mul_le_mul_of_nonneg_left hnorm C.coe_nonneg))
  by_cases hb : d 0 ≤ D ∧ d 1 ≤ D
  · let b : BinaryIndex D := (⟨d 0, by omega⟩, ⟨d 1, by omega⟩)
    have he : binaryExponent b.1 b.2 = d := by ext i; fin_cases i <;> simp [b]
    simpa only [a, he] using ha b
  · have hzero : p.coeff d = 0 := by
      apply coeff_eq_zero_of_totalDegree_lt
      change p.totalDegree < d.sum (fun _ n => n)
      rw [binary_exponents_sum]
      omega
    rw [hzero, abs_zero]
    positivity

/-- An affine change has a coefficient cost depending only on degree and the
size of its parameters. This bound is independent of the direction separation. -/
theorem exists_affine_substitution_coefficient_bound (D : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (p : MvPolynomial (Fin 2) ℝ) (a : Fin 2 → ℝ) (s B L : ℝ),
      p.totalDegree ≤ D → 0 ≤ B → 1 ≤ L → (∀ b, |p.coeff b| ≤ B) →
      (∀ i, |a i| ≤ L) → |s| ≤ L →
      let q := bind₁ (fun i => MvPolynomial.C (a i) + MvPolynomial.C s * X i) p
      q.totalDegree ≤ D ∧ (∀ b, |q.coeff b| ≤ C * B * L ^ (2 * D)) ∧
      (∀ x, eval x q = eval (fun i => a i + s * x i) p) := by
  obtain ⟨C, hC, hcoeff⟩ := exists_binary_coefficient_bound D
  refine ⟨C * ((D : ℝ) + 1) ^ 2 * 2 ^ (2 * D), by positivity, ?_⟩
  intro p a s B L hp hB hL hc ha hs
  let q := bind₁ (fun i => MvPolynomial.C (a i) + MvPolynomial.C s * X i) p
  have hq : q.totalDegree ≤ D :=
    (Submission.Obl.k4_quadratic_selector_sweep.totalDegree_bind_affine _
      (fun i => (totalDegree_add _ _).trans
        (max_le (by simp) ((totalDegree_mul _ _).trans (by simp)))) p).trans hp
  have heval (x : Fin 2 → ℝ) : eval x q = eval (fun i => a i + s * x i) p := by
    change eval₂Hom (RingHom.id ℝ) x (bind₁ _ p) = _
    rw [eval₂Hom_bind₁]
    simp only [map_add, map_mul, eval₂Hom_C, eval₂Hom_X', RingHom.id_apply]
    rfl
  refine ⟨hq, ?_, heval⟩
  have hbound : ∀ x ∈ UnitBox, |eval x q| ≤ ((D : ℝ) + 1) ^ 2 * B * (2 * L) ^ (2 * D) := by
    intro x hx
    rw [heval]
    apply binary_polynomial_eval_bound p D hp hB (by linarith) hc
    intro i
    have hx1 : |x i| ≤ 1 := by rw [abs_of_nonneg (hx.1 i)]; exact hx.2 i
    calc
      |a i + s * x i| ≤ |a i| + |s| * |x i| := by simpa only [abs_mul] using abs_add_le (a i) (s * x i)
      _ ≤ L + L * 1 := add_le_add (ha i) (mul_le_mul hs hx1 (abs_nonneg _) (zero_le_one.trans hL))
      _ = 2 * L := by ring
  intro b
  have h := hcoeff q _ hq (by positivity) hbound b
  exact h.trans_eq (by rw [mul_pow]; ring)

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
