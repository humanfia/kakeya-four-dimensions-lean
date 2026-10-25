import Submission.Obl.k4_scalar_noisy_block_packets.DirectAngular

namespace Submission.Obl.k4_scalar_noisy_block_packets

open MeasureTheory Set Filter MvPolynomial
open scoped ENNReal

/-- The index set of sign tests can be any finite type. -/
theorem format_family {n D : ℕ} {B : ℝ} {ι : Type*} [Fintype ι]
    (p : ι → MvPolynomial (Fin n) ℝ) (S : Set (ι → SignType))
    (hc : (Fintype.card ι : ℝ) ≤ B)
    (hp : ∀ i, (p i).totalDegree ≤ D ∧ ∀ b, |(p i).coeff b| ≤ B) :
    Format n B D {x | (fun i => SignType.sign (eval x (p i))) ∈ S} := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, hc, p ∘ e, fun i => hp (e i),
    {v | (fun i => v (e.symm i)) ∈ S}, ?_⟩
  ext x
  simp only [mem_ofPred_eq, Function.comp_apply, Equiv.apply_symm_apply]

lemma linear_test_degree {n : ℕ} (e : Fin n) (a : ℝ) :
    (X e - C a : MvPolynomial (Fin n) ℝ).totalDegree ≤ 1 := by
  exact (totalDegree_sub_C_le _ _).trans_eq (totalDegree_X _)

lemma linear_test_coeff {n : ℕ} (e : Fin n) (a : ℝ) (b : Fin n →₀ ℕ) :
    |(X e - C a : MvPolynomial (Fin n) ℝ).coeff b| ≤ 1 + |a| := by
  classical
  rw [coeff_sub]
  apply (show |(X e : MvPolynomial (Fin n) ℝ).coeff b - (C a).coeff b| ≤
    |(X e : MvPolynomial (Fin n) ℝ).coeff b| + |(C a : MvPolynomial (Fin n) ℝ).coeff b| by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le ((X e : MvPolynomial (Fin n) ℝ).coeff b) (- (C a).coeff b)).trans
  apply add_le_add
  · rw [coeff_X]
    split_ifs <;> norm_num
  · rw [coeff_C]
    split_ifs <;> simp

/-- A coordinate box has affine sign format with two tests per coordinate. -/
theorem format_box {n : ℕ} (a b : Fin n → ℝ) (B : ℝ)
    (hc : (2 * n : ℕ) ≤ B) (ha : ∀ e, 1 + |a e| ≤ B) (hb : ∀ e, 1 + |b e| ≤ B) :
    Format n B 1 (Icc a b) := by
  classical
  let p : (Fin n ⊕ Fin n) → MvPolynomial (Fin n) ℝ :=
    Sum.elim (fun e => X e - C (a e)) (fun e => X e - C (b e))
  let S : Set ((Fin n ⊕ Fin n) → SignType) :=
    {v | ∀ e, 0 ≤ v (Sum.inl e) ∧ v (Sum.inr e) ≤ 0}
  have hf := format_family p S (by simpa [Fintype.card_sum, two_mul] using hc) (by
    intro i
    cases i with
    | inl e => exact ⟨linear_test_degree e _, fun c => (linear_test_coeff e _ c).trans (ha e)⟩
    | inr e => exact ⟨linear_test_degree e _, fun c => (linear_test_coeff e _ c).trans (hb e)⟩)
  convert hf using 1
  ext x
  simp only [S, p, mem_Icc, Pi.le_def, mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr,
    map_sub, eval_X, eval_C, sign_nonneg_iff, sign_nonpos_iff,
    sub_nonneg, sub_nonpos, forall_and]

/-- A union of selected intervals in one coordinate has polynomial sign format. -/
theorem format_interval_union {n J : ℕ} (e : Fin n) (a b : Fin J → ℝ)
    (choose : Fin J → Prop) (B : ℝ) (hc : (2 * J : ℕ) ≤ B)
    (ha : ∀ z, 1 + |a z| ≤ B) (hb : ∀ z, 1 + |b z| ≤ B) :
    Format n B 1 {x | ∃ z, choose z ∧ x e ∈ Ico (a z) (b z)} := by
  classical
  let p : (Fin J ⊕ Fin J) → MvPolynomial (Fin n) ℝ :=
    Sum.elim (fun z => X e - C (a z)) (fun z => X e - C (b z))
  let S : Set ((Fin J ⊕ Fin J) → SignType) :=
    {v | ∃ z, choose z ∧ 0 ≤ v (Sum.inl z) ∧ v (Sum.inr z) = -1}
  have hf := format_family p S (by simpa [Fintype.card_sum, two_mul] using hc) (by
    intro i
    cases i with
    | inl z => exact ⟨linear_test_degree e _, fun c => (linear_test_coeff e _ c).trans (ha z)⟩
    | inr z => exact ⟨linear_test_degree e _, fun c => (linear_test_coeff e _ c).trans (hb z)⟩)
  convert hf using 1
  ext x
  simp only [S, p, mem_Ico, mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr,
    map_sub, eval_X, eval_C, sign_nonneg_iff, sign_eq_neg_one_iff,
    sub_nonneg, sub_lt_zero]

end Submission.Obl.k4_scalar_noisy_block_packets
