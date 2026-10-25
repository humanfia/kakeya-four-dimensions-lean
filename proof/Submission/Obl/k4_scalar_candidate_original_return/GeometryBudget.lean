import Submission.Obl.k4_scalar_candidate_original_return.MergedFits
import Submission.Obl.k4_scalar_candidate_original_return.SelectedFormat

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

/-- The whole-block priority family has polynomial atom count even after
merging arbitrary sibling candidates. -/
lemma merged_fit_atom_budget {N : ℝ} (hN : 2 ≤ N) (M J : ℕ) {m : ℕ}
    (hm : (m : ℝ) ≤ N ^ J) :
    N ^ M + (m : ℝ) * (12 * ((m : ℝ) + 1)) ≤ N ^ (M + 2 * J + 8) := by
  have hN1 : 1 ≤ N := by linarith
  have hV : 1 ≤ N ^ J := one_le_pow₀ hN1
  have hpow : N ^ M ≤ N ^ (M + 2 * J) := pow_le_pow_right₀ hN1 (by omega)
  have hpow' : N ^ (2 * J) ≤ N ^ (M + 2 * J) := pow_le_pow_right₀ hN1 (by omega)
  have hterm : (m : ℝ) * (12 * ((m : ℝ) + 1)) ≤ 24 * N ^ (2 * J) := by
    calc
      _ ≤ N ^ J * (12 * (N ^ J + 1)) := by gcongr
      _ ≤ 24 * (N ^ J * N ^ J) := by nlinarith
      _ = _ := by rw [← pow_add, show J + J = 2 * J by omega]
  calc
    _ ≤ 25 * N ^ (M + 2 * J) := by nlinarith
    _ ≤ N ^ 8 * N ^ (M + 2 * J) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 8
      norm_num at hh
      linarith
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- Both the merged full-prior assignment and its fresh original selected
incidences have a uniform original format budget linear in M and J. -/
theorem merged_geometry_format {p : Code} (hp : Exact p) {k n M₀ J : ℕ}
    (a : Layer (W p k)) (e : ℝ) (m : Fin a.n → ℕ)
    (P : (i : Fin a.n) → Fin (m i) → Poly)
    (parent : Fin n → Fin a.n) (bin : (i : Fin a.n) → Fin (m i) → Fin n)
    (hparent : ∀ i h, parent (bin i h) = i)
    (hP : ∀ i h, (P i h).totalDegree ≤ 2)
    (hM : M p ≤ M₀) (hD : D p ≤ M₀)
    (hm : ∀ i, (m i : ℝ) ≤ N p k ^ J)
    (hA : ∀ i z, Format 5 (N p k ^ M₀) M₀ {v | (z, v) ∈ a.prior i}) :
    let A := mergedFitAssignment a e m P bin
    let B := M₀ + 2 * J + 10
    (∀ i z, Format 5 (N p k ^ B) B {v | (z, v) ∈ A i}) ∧
    (∀ i z, Format 6 (N p k ^ B) B
      {v | ((z, fun e : Fin 5 => v e.castSucc), v 5) ∈ geometricSelected a parent A i}) := by
  let n₀ := N p k
  have hN : 2 ≤ n₀ := hp.1.1 k
  have hN1 : 1 ≤ n₀ := by linarith
  let B₀ := M₀ + 2 * J + 8
  let B := M₀ + 2 * J + 10
  let A := mergedFitAssignment a e m P bin
  have hprior : ∀ i z, Format 5 (n₀ ^ B₀) B₀ {v | (z, v) ∈ A i} := by
    intro i z
    have hf := mergedFitAssignment_format a e m P parent bin hparent hP
      (one_le_pow₀ hN1) hA i z
    exact k4_scalar_true_atlas_terminal_lists.Format.mono hf
      (merged_fit_atom_budget hN M₀ J (hm (parent i))) (by dsimp [B₀]; omega)
  have hpow : n₀ ^ B₀ ≤ n₀ ^ B := pow_le_pow_right₀ hN1 (by dsimp [B₀, B]; omega)
  refine ⟨fun i z => k4_scalar_true_atlas_terminal_lists.Format.mono (hprior i z)
    hpow (by dsimp [B₀, B]; omega), ?_⟩
  intro i z
  have hf := geometricSelected_format hp a parent A (one_le_pow₀ hN1) hprior i z
  have hbudget : n₀ ^ (M p) + (n₀ ^ B₀ + 2) ≤ n₀ ^ B := by
    have hsmall : n₀ ^ (M p) ≤ n₀ ^ B₀ :=
      pow_le_pow_right₀ hN1 (by dsimp [B₀]; omega)
    have hone : 1 ≤ n₀ ^ B₀ := one_le_pow₀ hN1
    calc
      _ ≤ 4 * n₀ ^ B₀ := by linarith
      _ ≤ n₀ ^ 2 * n₀ ^ B₀ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith
      _ = _ := by rw [← pow_add]; congr 1; dsimp [B₀, B]; omega
  exact k4_scalar_true_atlas_terminal_lists.Format.mono hf
    (by simpa only [Real.rpow_natCast] using hbudget) (by dsimp [B₀, B]; omega)

end Submission.Obl.k4_scalar_candidate_original_return
