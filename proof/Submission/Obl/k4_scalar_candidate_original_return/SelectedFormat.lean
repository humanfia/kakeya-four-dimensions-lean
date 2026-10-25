import Submission.Obl.k4_scalar_candidate_original_return.SelectedAtlas
import Submission.Obl.k4_scalar_candidate_original_return.CoordinateFormat

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open Set MvPolynomial

/-- A fixed time interval needs only two normalized affine sign tests. -/
lemma time_interval_format (s e : ℝ) : Format 6 2 1 {w | w 5 ∈ Icc s e} := by
  let P : Fin 2 → MvPolynomial (Fin 6) ℝ := ![X 5 - C s, C e - X 5]
  let S : Set (Fin 2 → SignType) := {v | 0 ≤ v 0 ∧ 0 ≤ v 1}
  have h := k4_scalar_true_atlas_terminal_lists.Format.of_sign_family (D := 1)
    (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : ((2 : ℕ) : ℝ) ≤ 2) P
    (by
      intro i
      fin_cases i
      · exact (totalDegree_sub _ _).trans (max_le (by simp [P]) (by simp [P]))
      · exact (totalDegree_sub _ _).trans (max_le (by simp [P]) (by simp [P]))) S
  have heq : {w | (fun i => SignType.sign (eval w (P i))) ∈ S} =
      {w : Fin 6 → ℝ | w 5 ∈ Icc s e} := by
    ext w
    simp only [mem_ofPred_eq, S, P, Matrix.cons_val_zero, Matrix.cons_val_one,
      eval_sub, eval_X, eval_C, sign_nonneg_iff, mem_Icc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  rw [heq] at h
  exact h

/-- The full new geometric event keeps the original event predicate and a
whole assigned time block. -/
def geometricSelected {p : Code} {k m : ℕ} (a : Layer (W p k))
    (parent : Fin m → Fin a.n) (A : Fin m → Set Line) (i : Fin m) : Set Inc :=
  E p k (a.world (parent i)) ∩ (A i ×ˢ I a.T (a.time (parent i)))

lemma geometricSelected_format {p : Code} (hp : Exact p) {k m : ℕ}
    (a : Layer (W p k)) (parent : Fin m → Fin a.n) (A : Fin m → Set Line)
    {BA : ℝ} {DA : ℕ} (hBA : 1 ≤ BA)
    (hA : ∀ i z, Format 5 BA DA {v | (z, v) ∈ A i}) (i : Fin m) (z : ℕ) :
    Format 6 (N p k ^ (M p : ℝ) + (BA + 2)) (max (D p) (max DA 1))
      {w | ((z, fun e : Fin 5 => w e.castSucc), w 5) ∈ geometricSelected a parent A i} := by
  have hE := ((hp.2.1 k).2.2.2.1 (a.world (parent i))).2.2.2.2.2.2 z
  have hA' := prior_incidence_format hBA (hA i z)
  have hI := time_interval_format
    (((a.time (parent i) : ℕ) : ℝ) / (2 : ℝ) ^ a.T)
    ((((a.time (parent i) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ a.T)
  have hN : 1 ≤ N p k := (by norm_num : (1 : ℝ) ≤ 2).trans (hp.1.1 k)
  exact k4_scalar_true_atlas_terminal_lists.Format.inter hE
    (k4_scalar_true_atlas_terminal_lists.Format.inter hA' hI hBA (by norm_num))
    (Real.one_le_rpow hN (Nat.cast_nonneg _)) (by linarith)

/-- A finite observer selector adds exactly its own polynomial tests. -/
lemma selectedByLists_format {p : Code} {k m : ℕ}
    (γ : Fin m → Fin (W p k)) (C : Fin m → Set Inc)
    (L : Fin (W p k) → (Base × ℤ) → Finset (Fin m)) (δ : ℝ)
    {BC BL : ℝ} {DC DL : ℕ} (hBC : 1 ≤ BC) (hBL : 1 ≤ BL)
    (hC : ∀ i z, Format 6 BC DC
      {w | ((z, fun e : Fin 5 => w e.castSucc), w 5) ∈ C i})
    (hL : ∀ a i z, Format 6 BL DL
      {w | i ∈ L a (originalObservation δ ((z, fun e : Fin 5 => w e.castSucc), w 5))})
    (i : Fin m) (z : ℕ) : Format 6 (BC + BL) (max DC DL)
      {w | ((z, fun e : Fin 5 => w e.castSucc), w 5) ∈ selectedByLists γ C L δ i} :=
  k4_scalar_true_atlas_terminal_lists.Format.inter (hC i z) (hL (γ i) i z) hBC hBL

end Submission.Obl.k4_scalar_candidate_original_return
