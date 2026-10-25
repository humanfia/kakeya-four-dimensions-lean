import Submission.Obl.k4_quadratic_sheet_continuation.AffineRestriction
import Submission.Obl.k4_quadratic_sheet_continuation.DirectionalTransfer

/-! Affine-restriction glue adapted from session x0449, branch x0449,
commit 58b4584 of this LOT obligation. The calculus step is proved in
DirectionalTransfer, so only the scalar quadratic law is a hypothesis. -/

namespace Submission.Obl.k4_quadratic_sheet_continuation

set_option linter.unusedVariables false

theorem quadratic_sheet_continuation_of_scalar
    (hscalar_all : ∀ m D : ℕ, ∃ N : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 2 ≤ A → ∀ (P : Fin m → MvPolynomial (Fin 2) ℂ) (f : Fin m → ℂ → ℂ) (Q : MvPolynomial (Fin (1 + m)) ℂ), (fun U : Set ℂ => (fun G : ℂ → ℂ => (∀ i, P i ≠ 0 ∧ (P i).totalDegree ≤ 2 ∧ DifferentiableOn ℂ (f i) U ∧ ∀ t ∈ U, MvPolynomial.eval (Fin.snoc (fun _ : Fin 1 => t) (f i t)) (P i) = 0 ∧ MvPolynomial.eval (Fin.snoc (fun _ : Fin 1 => t) (f i t)) (MvPolynomial.pderiv (Fin.last 1) (P i)) ≠ 0) → Q.totalDegree ≤ D → ∀ V : ℝ, 0 ≤ V → (∀ j : ℕ, j ≤ N → ‖iteratedDeriv j G 0‖ ≤ V) → ‖G 1‖ ≤ A ^ K * V) (fun t : ℂ => MvPolynomial.eval (Fin.append (fun _ : Fin 1 => t) (fun i : Fin m => f i t)) Q)) (Metric.thickening (A⁻¹) (segment ℝ (0 : ℂ) 1))) :
    ∀ n m D s : ℕ, ∃ q : ℕ, ∃ C : ℝ, s ≤ q ∧ 0 < C ∧ ∀ A : ℝ, 2 ≤ A → ∀ a b c : EuclideanSpace ℂ (Fin n), ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 → ∀ (P : Fin m → MvPolynomial (Fin (n + 1)) ℂ) (f : Fin m → EuclideanSpace ℂ (Fin n) → ℂ) (Q : MvPolynomial (Fin (n + m)) ℂ), (fun U : Set (EuclideanSpace ℂ (Fin n)) => (fun H : EuclideanSpace ℂ (Fin n) → ℂ => (∀ i, P i ≠ 0 ∧ (P i).totalDegree ≤ 2 ∧ DifferentiableOn ℂ (f i) U ∧ ∀ z ∈ U, MvPolynomial.eval (Fin.snoc (fun j : Fin n => z j) (f i z)) (P i) = 0 ∧ MvPolynomial.eval (Fin.snoc (fun j : Fin n => z j) (f i z)) (MvPolynomial.pderiv (Fin.last n) (P i)) ≠ 0) → Q.totalDegree ≤ D → ∀ V : ℝ, 0 ≤ V → ((∀ z ∈ Metric.closedBall a ((8 * A)⁻¹), ‖H z‖ ≤ V) → (∀ z ∈ Metric.closedBall c ((8 * A)⁻¹), ‖H z‖ ≤ A ^ C * V) ∧ ∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℂ j H c‖ ≤ A ^ C * V) ∧ ((∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℂ j H c‖ ≤ V) → ∀ z ∈ Metric.closedBall a ((8 * A)⁻¹), ‖H z‖ ≤ A ^ C * V)) (fun z => MvPolynomial.eval (Fin.append (fun j : Fin n => z j) (fun i : Fin m => f i z)) Q)) (Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c)) := by
  intro n m D s
  obtain ⟨N, K, hK, hscalar⟩ := hscalar_all m D
  obtain ⟨q, L, hq, hL, hcalculus⟩ :=
    directional_jet_path_transfer n N s K hK
  refine ⟨q, L, (Nat.le_max_left s N).trans hq, hL, ?_⟩
  intro A hA a b c ha hb hc P f Q hsheet hQ
  let U := Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c)
  have hsmooth :
      ContDiffOn ℂ ((⊤ : ENat) : WithTop ENat) (evaluation f Q) U :=
    contDiffOn_sheet_evaluation Metric.isOpen_thickening P f
      (fun i => (hsheet i).2.2.1.continuousOn)
      (fun i z hz => ((hsheet i).2.2.2 z hz).1)
      (fun i z hz => ((hsheet i).2.2.2 z hz).2) Q _
  apply hcalculus A hA a b c ha hb hc (evaluation f Q) hsmooth
  intro p v hmap V hV hjet
  let P' : Fin m → MvPolynomial (Fin 2) ℂ := fun i => restrictLine p v (P i)
  let f' : Fin m → ℂ → ℂ := fun i t => f i (p + t • v)
  let Q' : MvPolynomial (Fin (1 + m)) ℂ := restrictLine p v Q
  let W := Metric.thickening ((8 * A)⁻¹) (segment ℝ (0 : ℂ) 1)
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hzero : (0 : ℂ) ∈ W := by
    apply Metric.mem_thickening_iff.mpr
    exact ⟨0, left_mem_segment ℝ 0 1, by simp; positivity⟩
  have hp : p ∈ U := by simpa only [zero_smul, add_zero] using hmap 0 hzero
  have heval :
      (fun t : ℂ => MvPolynomial.eval
        (Fin.append (fun _ : Fin 1 => t) (fun i : Fin m => f' i t)) Q') =
      (fun t : ℂ => evaluation f Q (p + t • v)) := by
    funext t
    exact eval_restrictLine p v Q t (fun i => f i (p + t • v))
  have hP' : ∀ i, P' i ≠ 0 ∧ (P' i).totalDegree ≤ 2 ∧
      DifferentiableOn ℂ (f' i) W ∧ ∀ t ∈ W,
        MvPolynomial.eval (Fin.snoc (fun _ : Fin 1 => t) (f' i t)) (P' i) = 0 ∧
        MvPolynomial.eval (Fin.snoc (fun _ : Fin 1 => t) (f' i t))
          (MvPolynomial.pderiv (Fin.last 1) (P' i)) ≠ 0 := by
    intro i
    refine ⟨restrictLine_ne_zero_of_simple p v (P i) (f i p)
      (((hsheet i).2.2.2 p hp).2),
      (totalDegree_restrictLine_le p v (P i)).trans (hsheet i).2.1,
      (hsheet i).2.2.1.comp (by fun_prop) hmap, ?_⟩
    intro t ht
    have hroot := (hsheet i).2.2.2 (p + t • v) (hmap t ht)
    constructor
    · simpa only [P', f', eval_restrictLine_snoc] using hroot.1
    · simpa only [P', f', eval_pderiv_restrictLine_snoc] using hroot.2
  have hQ' : Q'.totalDegree ≤ D :=
    (totalDegree_restrictLine_le p v Q).trans hQ
  have hjet' : ∀ j : ℕ, j ≤ N → ‖iteratedDeriv j
      (fun t : ℂ => MvPolynomial.eval
        (Fin.append (fun _ : Fin 1 => t) (fun i : Fin m => f' i t)) Q') 0‖ ≤ V := by
    simpa only [heval] using hjet
  have h := hscalar (8 * A) (by linarith) P' f' Q' hP' hQ' V hV hjet'
  rw [heval] at h
  simpa only [one_smul] using h

end Submission.Obl.k4_quadratic_sheet_continuation
