import Submission.Lib.K4MeshListRecovery.SparseTableRecovery

/-!
Adapted from: here:o064

Polynomial format of a finite mesh lookup, including its overflow entry.
The table contents are arbitrary; only its finite geometric cells add tests.
-/

namespace Submission.Lib.K4MeshListRecovery

open Finset MeasureTheory Set MvPolynomial

/-- A lookup on finitely many polynomial floor cells uses two threshold
tests per cell and coordinate, including all half-open boundaries exactly. -/
theorem polynomial_mesh_lookup_format
    {n k D : ℕ} (p : Fin k → MvPolynomial (Fin n) ℝ)
    (hp : ∀ i, (p i).totalDegree ≤ D) (ρ : ℝ)
    (F : Finset (Fin k → ℤ)) (S : Set (Option F)) :
    ∃ m : ℕ, (m : ℝ) ≤ (2 * k * F.card : ℕ) ∧
      ∃ q : Fin m → MvPolynomial (Fin n) ℝ, (∀ i, (q i).totalDegree ≤ D) ∧
      ∃ b : (Fin m → Bool) → Bool, ∀ x,
        finiteObservedCode F (fun x i => ⌊MvPolynomial.eval x (p i) / ρ⌋) x ∈ S ↔
          b (fun i => decide (0 ≤ MvPolynomial.eval x (q i))) = true := by
  classical
  let tag : (Fin n → ℝ) → (Fin k → ℤ) :=
    fun x i => ⌊MvPolynomial.eval x (p i) / ρ⌋
  let atom : (F × Fin k × Bool) → MvPolynomial (Fin n) ℝ := fun q =>
    C ρ⁻¹ * p q.2.1 - C ((q.1.val q.2.1 : ℝ) + if q.2.2 then 1 else 0)
  have hdegree (q : F × Fin k × Bool) : (atom q).totalDegree ≤ D := by
    apply (totalDegree_sub_C_le _ _).trans
    apply (totalDegree_mul _ _).trans
    simpa only [totalDegree_C, zero_add] using hp q.2.1
  let matchBits (bits : (F × Fin k × Bool) → Bool) (c : F) : Prop :=
    ∀ i, bits (c, i, false) = true ∧ bits (c, i, true) = false
  have hmatch (x : Fin n → ℝ) (c : F) :
      matchBits (fun q => decide (0 ≤ MvPolynomial.eval x (atom q))) c ↔ tag x = c.val := by
    rw [funext_iff]
    apply forall_congr'
    intro i
    simp [atom, tag, Int.floor_eq_iff, div_eq_inv_mul]
  have hnot (x : Fin n → ℝ) : (∀ c : F, tag x ≠ c.val) ↔ tag x ∉ F := by
    constructor
    · intro h hx
      exact h ⟨tag x, hx⟩ rfl
    · intro h c heq
      exact h (heq.symm ▸ c.property)
  have hlookup (x : Fin n → ℝ) :
      finiteObservedCode F tag x ∈ S ↔
        (∃ c : F, tag x = c.val ∧ some c ∈ S) ∨ (tag x ∉ F ∧ none ∈ S) := by
    by_cases hx : tag x ∈ F
    · let c : F := ⟨tag x, hx⟩
      have hcode : finiteObservedCode F tag x = some c := by simp [finiteObservedCode, hx, c]
      rw [hcode]
      constructor
      · intro h
        exact Or.inl ⟨c, rfl, h⟩
      · rintro (⟨d, hd, hS⟩ | ⟨hnot, _⟩)
        · have hdc : d = c := Subtype.ext hd.symm
          simpa only [hdc] using hS
        · exact False.elim (hnot hx)
    · have hne (c : F) : tag x ≠ c.val := (hnot x).mpr hx c
      simp [finiteObservedCode, hx, hne]
  let rule : ((F × Fin k × Bool) → Bool) → Bool := fun bits =>
    decide ((∃ c : F, matchBits bits c ∧ some c ∈ S) ∨
      ((∀ c : F, ¬ matchBits bits c) ∧ none ∈ S))
  have hdescr (x : Fin n → ℝ) : finiteObservedCode F tag x ∈ S ↔
      rule (fun q => decide (0 ≤ MvPolynomial.eval x (atom q))) = true := by
    simp only [rule, decide_eq_true_eq, hmatch, hnot]
    exact hlookup x
  let e := Fintype.equivFin (F × Fin k × Bool)
  refine ⟨Fintype.card (F × Fin k × Bool), ?_,
    (fun j => atom (e.symm j)), (fun j => hdegree _),
    (fun v => rule (fun q => v (e q))), ?_⟩
  · simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin, Fintype.card_bool]
    norm_num [mul_assoc, mul_comm, mul_left_comm]
  · intro x
    simpa only [Equiv.symm_apply_apply] using hdescr x

/-- Original observation coordinates may use different mesh widths. -/
theorem polynomial_mixed_mesh_lookup_format
    {n k D : ℕ} (p : Fin k → MvPolynomial (Fin n) ℝ)
    (hp : ∀ i, (p i).totalDegree ≤ D) (ρ : Fin k → ℝ)
    (F : Finset (Fin k → ℤ)) (S : Set (Option F)) :
    ∃ m : ℕ, (m : ℝ) ≤ (2 * k * F.card : ℕ) ∧
      ∃ q : Fin m → MvPolynomial (Fin n) ℝ, (∀ i, (q i).totalDegree ≤ D) ∧
      ∃ b : (Fin m → Bool) → Bool, ∀ x,
        finiteObservedCode F (fun x i => ⌊MvPolynomial.eval x (p i) / ρ i⌋) x ∈ S ↔
          b (fun i => decide (0 ≤ MvPolynomial.eval x (q i))) = true := by
  have hscaled (i : Fin k) : (C (ρ i)⁻¹ * p i).totalDegree ≤ D := by
    apply (totalDegree_mul _ _).trans
    simpa only [totalDegree_C, zero_add] using hp i
  simpa only [map_mul, eval_C, div_one, div_eq_inv_mul, inv_one, one_mul] using
    polynomial_mesh_lookup_format (fun i => C (ρ i)⁻¹ * p i) hscaled 1 F S

end Submission.Lib.K4MeshListRecovery
