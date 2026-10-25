import Submission.Lib.K4PolynomialRemezThree.Remez
import Submission.Lib.K4PolynomialRemezThree.PolynomialNorm

/-!
Adapted from: here:o114 (session x0383).

Polynomial norm comparison in the precise three base coordinates used for
discriminants. The witness set may be a projection with only outer volume.
-/

namespace Submission.Lib.K4PolynomialRemezThree

open MeasureTheory Set MvPolynomial

/-- Freezing all but one coordinate gives a univariate polynomial of no
larger degree. The monomial degree argument is adapted within this tree from
o007, k4_quadratic_slope_volume/PolynomialSlices.lean. A general library cannot
import an obligation module, so the coordinate-slice kernel is promoted here. -/
theorem polynomial_coordinate_slices (n D : ℕ) (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ D) :
    ∀ (v : Fin n → ℝ) (i : Fin n), ∃ p : Polynomial ℝ,
      p.natDegree ≤ D ∧ ∀ t, p.eval t = eval (Function.update v i t) P := by
  classical
  intro v i
  let q : Fin n → Polynomial ℝ := fun j =>
    if j = i then Polynomial.X else Polynomial.C (v j)
  have hq (j : Fin n) : (q j).natDegree ≤ 1 := by
    dsimp only [q]
    split_ifs <;> simp
  refine ⟨eval₂ Polynomial.C q P, ?_, ?_⟩
  · apply le_trans ?_ hP
    conv_lhs => rw [P.as_sum]
    rw [eval₂_sum]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro m hm
    rw [eval₂_monomial]
    apply (Polynomial.natDegree_C_mul_le _ _).trans
    calc
      (m.prod fun j e => q j ^ e).natDegree ≤
          m.sum (fun j e => (q j ^ e).natDegree) := Polynomial.natDegree_prod_le _ _
      _ ≤ m.sum (fun _ e => e) := by
        apply Finsupp.sum_le_sum
        intro j hj
        exact Polynomial.natDegree_pow_le.trans
          (by simpa using Nat.mul_le_mul_left (m j) (hq j))
      _ ≤ P.totalDegree := le_totalDegree hm
  · intro t
    have heval : ∀ R : MvPolynomial (Fin n) ℝ,
        (eval₂ Polynomial.C q R).eval t = eval (fun j => (q j).eval t) R := by
      intro R
      induction R using MvPolynomial.induction_on with
      | C a => simp
      | add R S hR hS => simp [eval₂_add, hR, hS]
      | mul_X R j hR => simp [eval₂_mul, hR]
    rw [heval]
    apply congrArg (fun z : Fin n → ℝ => eval z P)
    funext j
    by_cases hj : j = i
    · subst j
      simp [q]
    · simp [q, hj]

/-- Remez comparison for an actual real polynomial in the three base variables. -/
theorem polynomial_remez_fin3 (D : ℕ) (P : MvPolynomial (Fin 3) ℝ)
    (hP : P.totalDegree ≤ D) (S : Set (Fin 3 → ℝ)) {η E : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E)
    (hS : S ⊆ Icc (0 : Fin 3 → ℝ) 1)
    (hmass : ENNReal.ofReal η ≤ volume S)
    (hbound : ∀ z ∈ S, |eval z P| ≤ E) :
    ∀ z ∈ Icc (0 : Fin 3 → ℝ) 1,
      |eval z P| ≤ (32 * ((D : ℝ) + 1) / η) ^ (3 * D) * E :=
  separately_polynomial_remez_fin3 (fun z => eval z P) P.continuous_eval D
    (polynomial_coordinate_slices 3 D P hP) S hη hη1 hE hS hmass hbound

/-- Original positive base mass turns a pointwise discriminant bound on that
base set into coefficient bounds on the whole discriminant. -/
theorem exists_coefficient_bound_from_base_mass (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 3) ℝ), P.totalDegree ≤ D →
      ∀ (S : Set (Fin 3 → ℝ)) (η E : ℝ), 0 < η → η ≤ 1 → 0 ≤ E →
      S ⊆ Icc (0 : Fin 3 → ℝ) 1 → ENNReal.ofReal η ≤ volume S →
      (∀ x ∈ S, |eval x P| ≤ E) →
      ∀ d, |P.coeff d| ≤ C * (32 * ((D : ℝ) + 1) / η) ^ (3 * D) * E := by
  obtain ⟨C, hC, hbound⟩ := exists_coefficient_bound_on_unit_cube 3 D
  refine ⟨C, hC, ?_⟩
  intro P hP S η E hη hη1 hE hS hmass hpoint d
  have hunit := polynomial_remez_fin3 D P hP S hη hη1 hE hS hmass hpoint
  have hh := hbound P hP _ (by positivity) hunit d
  simpa only [mul_assoc] using hh

/-- An anchor lower bound controls the outer volume of the real discriminant
sublevel region. The constant is independent of the particular equation. -/
theorem exists_sublevel_bound_from_complex_anchor (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 3) ℝ), P.totalDegree ≤ D →
      ∀ (η E R : ℝ), 0 < η → η ≤ 1 → 0 ≤ E → 1 ≤ R →
      ∀ z : Fin 3 → ℂ, (∀ i, ‖z i‖ ≤ R) →
      C * R ^ D * (32 * ((D : ℝ) + 1) / η) ^ (3 * D) * E <
        ‖eval₂ (algebraMap ℝ ℂ) z P‖ →
      volume (Icc (0 : Fin 3 → ℝ) 1 ∩ {x | |eval x P| ≤ E}) <
        ENNReal.ofReal η := by
  obtain ⟨C, hC, hbound⟩ := exists_complex_bound_from_real_cube 3 D
  refine ⟨C, hC, ?_⟩
  intro P hP η E R hη hη1 hE hR z hz hgap
  by_contra h
  have hmass := le_of_not_gt h
  have hunit := polynomial_remez_fin3 D P hP
    (Icc (0 : Fin 3 → ℝ) 1 ∩ {x | |eval x P| ≤ E})
    hη hη1 hE Set.inter_subset_left hmass (fun _ hx => hx.2)
  apply (not_le_of_gt hgap)
  calc
    _ ≤ C * R ^ D * ((32 * ((D : ℝ) + 1) / η) ^ (3 * D) * E) :=
      hbound P hP _ (by positivity) hunit R hR z hz
    _ = _ := by ring

/-- Quantitative real-anchor sublevel bound. A real anchor may be used for the
converted real discriminants; the detour path can still be complex. -/
theorem volume_sublevel_lt_from_real_anchor (D : ℕ)
    (P : MvPolynomial (Fin 3) ℝ) (hP : P.totalDegree ≤ D)
    {η V : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hV : 0 < V)
    {x : Fin 3 → ℝ} (hx : x ∈ Icc (0 : Fin 3 → ℝ) 1)
    (hlower : V ≤ |eval x P|) :
    volume (Icc (0 : Fin 3 → ℝ) 1 ∩
      {z | |eval z P| ≤ (V / 2) * (η / (32 * ((D : ℝ) + 1))) ^ (3 * D)}) <
      ENNReal.ofReal η := by
  have hC : 0 < 32 * ((D : ℝ) + 1) := by positivity
  have hcancel : (32 * ((D : ℝ) + 1) / η) ^ (3 * D) *
      (η / (32 * ((D : ℝ) + 1))) ^ (3 * D) = 1 := by
    rw [← mul_pow]
    have hh : (32 * ((D : ℝ) + 1) / η) * (η / (32 * ((D : ℝ) + 1))) = 1 := by
      field_simp
    rw [hh, one_pow]
  apply volume_sublevel_lt_of_remez_gap (fun z => eval z P) P.continuous_eval D
    (polynomial_coordinate_slices 3 D P hP) hη hη1 (by positivity) hx
  calc
    _ = (V / 2) * ((32 * ((D : ℝ) + 1) / η) ^ (3 * D) *
        (η / (32 * ((D : ℝ) + 1))) ^ (3 * D)) := by ring
    _ = V / 2 := by rw [hcancel, mul_one]
    _ < V := by linarith
    _ ≤ |eval x P| := hlower

end Submission.Lib.K4PolynomialRemezThree
