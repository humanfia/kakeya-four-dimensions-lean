import Submission.Obl.k4_scalar_initial_true_horizon.Defs

namespace Submission.Obl.k4_scalar_initial_true_horizon

open MeasureTheory Set MvPolynomial
open scoped BigOperators

/-- Normalizing each sign test makes its coefficient budget independent of
its geometric parameters. Positive scalar multiplication preserves all signs. -/
theorem normalize_sign_polynomial {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    ∃ q : MvPolynomial (Fin n) ℝ, q.totalDegree ≤ p.totalDegree ∧
      (∀ a, |q.coeff a| ≤ 1) ∧
      ∀ x, SignType.sign (eval x q) = SignType.sign (eval x p) := by
  classical
  let R : ℝ := 1 + ∑ a ∈ p.support, |p.coeff a|
  have hR : 0 < R := by dsimp [R]; positivity
  have hb (a : Fin n →₀ ℕ) : |p.coeff a| ≤ R := by
    by_cases ha : a ∈ p.support
    · have hs := Finset.single_le_sum (f := fun a => |p.coeff a|)
        (fun a _ => abs_nonneg (p.coeff a)) ha
      dsimp [R]
      linarith
    · rw [notMem_support_iff.mp ha, abs_zero]
      exact hR.le
  refine ⟨R⁻¹ • p, totalDegree_smul_le _ _, ?_, ?_⟩
  · intro a
    rw [coeff_smul, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hR)]
    calc
      R⁻¹ * |p.coeff a| ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left (hb a) (by positivity)
      _ = 1 := inv_mul_cancel₀ hR.ne'
  · intro x
    rw [smul_eq_C_mul, eval_mul, eval_C, sign_mul, sign_pos (inv_pos.mpr hR), one_mul]

/-- Any finite family of polynomial sign tests has the frozen coefficient
format after normalization; only its count and degrees need to be bounded. -/
theorem Format.of_sign_family {n m D : ℕ} {B : ℝ}
    (hB : 1 ≤ B) (hm : (m : ℝ) ≤ B) (p : Fin m → MvPolynomial (Fin n) ℝ)
    (hp : ∀ i, (p i).totalDegree ≤ D) (S : Set (Fin m → SignType)) :
    Format n B D {x | (fun i => SignType.sign (eval x (p i))) ∈ S} := by
  classical
  choose q hdegree hcoeff hsign using fun i => normalize_sign_polynomial (p i)
  refine ⟨m, hm, q, (fun i => ⟨(hdegree i).trans (hp i), fun a => (hcoeff i a).trans hB⟩),
    S, ?_⟩
  ext x
  simp only [mem_ofPred_eq, hsign]

theorem Format.mono {n D D' : ℕ} {B B' : ℝ} {A : Set (Fin n → ℝ)}
    (h : Format n B D A) (hB : B ≤ B') (hD : D ≤ D') : Format n B' D' A := by
  obtain ⟨m, hm, p, hp, S, hS⟩ := h
  exact ⟨m, hm.trans hB, p, fun i => ⟨(hp i).1.trans hD,
    fun a => ((hp i).2 a).trans hB⟩, S, hS⟩

theorem Format.compl {n D : ℕ} {B : ℝ} {A : Set (Fin n → ℝ)}
    (h : Format n B D A) : Format n B D Aᶜ := by
  obtain ⟨m, hm, p, hp, S, rfl⟩ := h
  exact ⟨m, hm, p, hp, Sᶜ, rfl⟩

/-- A bounded number of atoms can implement an arbitrary Boolean rule. -/
theorem Format.of_invariant {n m D : ℕ} {B : ℝ} (hB : 1 ≤ B)
    (hm : (m : ℝ) ≤ B) (p : Fin m → MvPolynomial (Fin n) ℝ)
    (hp : ∀ i, (p i).totalDegree ≤ D) (A : Set (Fin n → ℝ))
    (hinv : ∀ x y, (∀ i, SignType.sign (eval x (p i)) = SignType.sign (eval y (p i))) →
      (x ∈ A ↔ y ∈ A)) : Format n B D A := by
  let S := (fun x => fun i => SignType.sign (eval x (p i))) '' A
  have hA : A = {x | (fun i => SignType.sign (eval x (p i))) ∈ S} := by
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, heq⟩
      exact (hinv y x (congrFun heq)).mp hy
  rw [hA]
  exact Format.of_sign_family hB hm p hp S

/-- Every frozen polynomial sign set is measurable. -/
theorem Format.measurable {n D : ℕ} {B : ℝ} {A : Set (Fin n → ℝ)}
    (h : Format n B D A) : MeasurableSet A := by
  classical
  obtain ⟨m, hm, p, hp, S, rfl⟩ := h
  letI : MeasurableSpace SignType := ⊤
  have hs : Measurable (fun t : ℝ => SignType.sign t) := by
    change Measurable (fun t : ℝ => if 0 < t then (1 : SignType) else if t < 0 then -1 else 0)
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
      (Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const)
  have hv : Measurable (fun x : Fin n → ℝ => fun i => SignType.sign (eval x (p i))) :=
    Measurable.of_eval (fun i => hs.comp (MvPolynomial.continuous_eval (p i)).measurable)
  exact (Set.to_countable S).measurableSet.preimage hv

/-- A Boolean polynomial lookup has the same degree and atom budget in the
three-sign format, with normalized coefficients. -/
theorem Format.of_bool_family {n m D : ℕ} {B : ℝ} (hB : 1 ≤ B)
    (hm : (m : ℝ) ≤ B) (p : Fin m → MvPolynomial (Fin n) ℝ)
    (hp : ∀ i, (p i).totalDegree ≤ D) (b : (Fin m → Bool) → Bool)
    (A : Set (Fin n → ℝ))
    (hA : ∀ x, x ∈ A ↔ b (fun i => decide (0 ≤ eval x (p i))) = true) :
    Format n B D A := by
  classical
  apply Format.of_invariant hB hm p hp A
  intro x y hxy
  have heq : (fun i => decide (0 ≤ eval x (p i))) =
      (fun i => decide (0 ≤ eval y (p i))) := by
    funext i
    congr 1
    simpa only [sign_nonneg_iff] using congrArg (fun s : SignType => 0 ≤ s) (hxy i)
  rw [hA x, hA y, heq]

/-- Reindexing a finite test family preserves its exact count. -/
theorem Format.of_family {n D : ℕ} {ι : Type*} [Fintype ι] {B : ℝ}
    (hB : 1 ≤ B) (hm : (Fintype.card ι : ℝ) ≤ B)
    (p : ι → MvPolynomial (Fin n) ℝ) (hp : ∀ i, (p i).totalDegree ≤ D)
    (S : Set (ι → SignType)) :
    Format n B D {x | (fun i => SignType.sign (eval x (p i))) ∈ S} := by
  classical
  let e := Fintype.equivFin ι
  convert Format.of_sign_family hB hm (fun i => p (e.symm i))
    (fun i => hp (e.symm i)) {s | (fun i => s (e i)) ∈ S} using 1
  ext x
  simp

/-- An intersection concatenates the two families of tests. -/
theorem Format.inter {n D D' : ℕ} {B B' : ℝ} {A A' : Set (Fin n → ℝ)}
    (h : Format n B D A) (h' : Format n B' D' A')
    (hB : 1 ≤ B) (hB' : 1 ≤ B') :
    Format n (B + B') (max D D') (A ∩ A') := by
  classical
  obtain ⟨m, hm, p, hp, S, rfl⟩ := h
  obtain ⟨m', hm', p', hp', S', rfl⟩ := h'
  apply Format.of_family (by linarith) (ι := Fin m ⊕ Fin m')
    (p := Sum.elim p p')
    (S := {s | (fun i => s (Sum.inl i)) ∈ S ∧ (fun i => s (Sum.inr i)) ∈ S'})
  · simp only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add]
    linarith
  · intro i
    cases i with
    | inl i => exact (hp i).1.trans (le_max_left _ _)
    | inr i => exact (hp' i).1.trans (le_max_right _ _)

end Submission.Obl.k4_scalar_initial_true_horizon
