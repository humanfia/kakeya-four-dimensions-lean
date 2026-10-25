import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Format

/-! Quantitative sign format for a finite lookup depending on one floor bin. -/

namespace Submission.Obl.k4_scalar_true_atlas_terminal_lists

open Set MvPolynomial

/-- Each floor branch adds its two boundary tests and its own finite family.
The Boolean choice of branches has no further complexity cost. -/
theorem Format.floor_piecewise {n m k D d : ℕ} {R B a : ℝ}
    {A : Set (Fin n → ℝ)} (hA : Format n R D A) (hB : 1 ≤ B)
    (hcount : R + (m : ℝ) * (2 + k) ≤ B) (ha : 0 < a)
    (f : MvPolynomial (Fin n) ℝ) (hf : f.totalDegree ≤ d)
    (b : Fin m → ℤ) (Q : Fin m → Fin k → MvPolynomial (Fin n) ℝ)
    (hQ : ∀ i j, (Q i j).totalDegree ≤ d) (S : Fin m → Set (Fin k → SignType)) :
    Format n B (max D d) {x | x ∈ A ∧ ∃ i,
      ⌊eval x f / a⌋ = b i ∧ (fun j => SignType.sign (eval x (Q i j))) ∈ S i} := by
  classical
  obtain ⟨l, hl, p, hp, U, rfl⟩ := hA
  let F : Fin m → Fin 2 → MvPolynomial (Fin n) ℝ := fun i =>
    ![f - C (a * (b i : ℝ)), C (a * ((b i : ℝ) + 1)) - f]
  let tests : Fin l ⊕ (Fin m × (Fin 2 ⊕ Fin k)) → MvPolynomial (Fin n) ℝ :=
    Sum.elim p (fun ij => Sum.elim (F ij.1) (Q ij.1) ij.2)
  let V : Set ((Fin l ⊕ (Fin m × (Fin 2 ⊕ Fin k))) → SignType) :=
    {s | (fun i => s (Sum.inl i)) ∈ U ∧ ∃ i,
      0 ≤ s (Sum.inr (i, Sum.inl 0)) ∧ s (Sum.inr (i, Sum.inl 1)) = 1 ∧
        (fun j => s (Sum.inr (i, Sum.inr j))) ∈ S i}
  have htestdeg (i : Fin l ⊕ (Fin m × (Fin 2 ⊕ Fin k))) :
      (tests i).totalDegree ≤ max D d := by
    cases i with
    | inl i => exact (hp i).1.trans (le_max_left _ _)
    | inr ij =>
      rcases ij with ⟨i, j⟩
      cases j with
      | inl j =>
        have hF : (F i j).totalDegree ≤ d := by
          fin_cases j
          · change (f - C (a * (b i : ℝ))).totalDegree ≤ d
            exact (totalDegree_sub _ _).trans (max_le hf (by rw [totalDegree_C]; omega))
          · change (C (a * ((b i : ℝ) + 1)) - f).totalDegree ≤ d
            exact (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_C]; omega) hf)
        exact hF.trans (le_max_right _ _)
      | inr j => exact (hQ i j).trans (le_max_right _ _)
  have htestcount : (Fintype.card (Fin l ⊕ (Fin m × (Fin 2 ⊕ Fin k))) : ℝ) ≤ B := by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat]
    linarith
  have hformat := Format.of_family hB htestcount tests htestdeg V
  convert hformat using 1
  ext x
  change (x ∈ {x | (fun j => SignType.sign (eval x (p j))) ∈ U} ∧ _) ↔ _
  simp only [V, tests, F, mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr, eval_sub, eval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    sign_nonneg_iff, sign_eq_one_iff]
  apply and_congr_right
  intro hx
  apply exists_congr
  intro i
  have hfloor : ⌊eval x f / a⌋ = b i ↔
      0 ≤ eval x f - a * (b i : ℝ) ∧ 0 < a * ((b i : ℝ) + 1) - eval x f := by
    rw [Int.floor_eq_iff]
    constructor
    · rintro ⟨hlo, hhi⟩
      constructor
      · have := (le_div_iff₀ ha).mp hlo
        nlinarith
      · have := (div_lt_iff₀ ha).mp hhi
        nlinarith
    · rintro ⟨hlo, hhi⟩
      constructor
      · apply (le_div_iff₀ ha).mpr
        nlinarith
      · apply (div_lt_iff₀ ha).mpr
        nlinarith
  rw [hfloor]
  tauto

end Submission.Obl.k4_scalar_true_atlas_terminal_lists
