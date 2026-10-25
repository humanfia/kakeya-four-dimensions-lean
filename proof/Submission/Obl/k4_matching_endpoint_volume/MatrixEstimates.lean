import Mathlib

/- Developed in this workspace by x0047 for o015 and its endpoint-volume child. -/

/-!
# Polynomial norm bounds for finite matrices

These estimates deliberately use loose dimension-dependent constants. They
are enough to turn a subpower determinant lower bound into a subpower inverse
bound in the endpoint-map argument.
-/

namespace Submission.Obl.k4_matching_endpoint_volume

open scoped BigOperators Matrix

lemma abs_det_le_factorial_mul_pow {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hA : ∀ i j : Fin m, |A i j| ≤ B) :
    |A.det| ≤ (m.factorial : ℝ) * B ^ m := by
  rw [Matrix.det_apply']
  calc
    |∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A (σ i) i| ≤
        ∑ σ : Equiv.Perm (Fin m),
          |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin m), B ^ m := by
      apply Finset.sum_le_sum
      intro σ hσ
      rw [abs_mul, abs_unit_intCast, one_mul, Finset.abs_prod]
      calc
        (∏ i : Fin m, |A (σ i) i|) ≤ ∏ _i : Fin m, B :=
          Finset.prod_le_prod₀ (fun i hi => abs_nonneg _) (fun i hi => hA (σ i) i)
        _ = B ^ m := by simp
    _ = (m.factorial : ℝ) * B ^ m := by simp [Fintype.card_perm, nsmul_eq_mul]

lemma abs_adjugate_entry_le {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    {B : ℝ} (hB : 1 ≤ B) (hA : ∀ i j : Fin m, |A i j| ≤ B) (i j : Fin m) :
    |A.adjugate i j| ≤ (m.factorial : ℝ) * B ^ m := by
  rw [Matrix.adjugate_apply]
  apply abs_det_le_factorial_mul_pow _ (by linarith)
  intro a b
  by_cases ha : a = j
  · subst a
    simp only [Matrix.updateRow_self]
    by_cases hb : b = i
    · subst b
      simpa using hB
    · simpa [Pi.single_apply, hb, Ne.symm hb] using (show (0 : ℝ) ≤ B by linarith)
  · simpa [Matrix.updateRow_apply, ha] using hA a b

lemma norm_mulVec_le_card_mul_bound {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hA : ∀ i j : Fin m, |A i j| ≤ B) (v : Fin m → ℝ) :
    ‖A *ᵥ v‖ ≤ (m : ℝ) * B * ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change |∑ j : Fin m, A i j * v j| ≤ _
  calc
    |∑ j : Fin m, A i j * v j| ≤ ∑ j : Fin m, |A i j * v j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin m, B * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul (hA i j) (norm_le_pi_norm v j) (abs_nonneg _) hB
    _ = (m : ℝ) * B * ‖v‖ := by simp [nsmul_eq_mul, mul_assoc]

/-- A determinant lower bound supplies a lower norm bound using the adjugate.
No spectral theorem or singular-value decomposition is needed. -/
lemma det_mul_norm_le_mulVec_norm {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    {B : ℝ} (hB : 1 ≤ B) (hA : ∀ i j : Fin m, |A i j| ≤ B) (v : Fin m → ℝ) :
    |A.det| * ‖v‖ ≤ ((m : ℝ) * (m.factorial : ℝ) * B ^ m) * ‖A *ᵥ v‖ := by
  have h := norm_mulVec_le_card_mul_bound A.adjugate
    (show 0 ≤ (m.factorial : ℝ) * B ^ m by positivity)
    (abs_adjugate_entry_le A hB hA) (A *ᵥ v)
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
    norm_smul, Real.norm_eq_abs] at h
  simpa only [mul_assoc] using h

end Submission.Obl.k4_matching_endpoint_volume
