-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.NativeRowFit, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/NativeRowFit.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/NativeRowFit.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/NativeRowFit.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 4986346c. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface

set_option autoImplicit false

/-!
# From a jet fit of the zoomed row to a native fit of the graph row (paper `tex-06`, l. 843–856)

Paper, proof of Prop. `a05:qualification`: the higher jets fit the time-only row `F` (hence the
tangential components `G_y` of the graph row) by polynomials; the velocity-graph estimate
`G₀ = X' − G_y · V + O(err)` then fits `G₀` too.  For one original indexed line with coefficients
`c` (`x = c₀ + c₁ t + c₂ t²`, velocity `(1, c₄, c₆)`), a jet fit `P` of `F` gives the native
three-row polynomial
`Q₀ = c₁ + 2 c₂ X − c₄ P₀ − c₆ P₁`, `Q₁ = P₀`, `Q₂ = P₁`,
with coefficients `≤ 3B + (1 + 2B) C_jet` and error `graphError + (1 + 2B)(rowError + δ)` at every
witness time of the jet fit, on the same line and in the same dyadic block.

* `nativeRowPoly`: the polynomials `Q`;
* `native_row_fit_of_jetFit`: the fit (for o106's frozen packets: `c = p.scalarCoefficients`,
  `c₁ + 2 c₂ t = (p.signal l).derivative.eval t`, `p.velocity l = ![1, c 4, c 6]`).
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open MeasureTheory Set Polynomial

noncomputable section

/-- The native three-row polynomial of a line with coefficients `c` from a jet fit `P` of the
tangential row. -/
def nativeRowPoly (c : Fin 7 → ℝ) (P : Fin 2 → Polynomial ℝ) : Fin 3 → Polynomial ℝ :=
  ![C (c 1) + C (2 * c 2) * X - (C (c 4) * P 0 + C (c 6) * P 1), P 0, P 1]

theorem nativeRowPoly_eval_zero (c : Fin 7 → ℝ) (P : Fin 2 → Polynomial ℝ) (t : ℝ) :
    (nativeRowPoly c P 0).eval t = c 1 + 2 * c 2 * t - (c 4 * (P 0).eval t + c 6 * (P 1).eval t) := by
  simp [nativeRowPoly]

theorem nativeRowPoly_eval_succ (c : Fin 7 → ℝ) (P : Fin 2 → Polynomial ℝ) (i : Fin 2) (t : ℝ) :
    (nativeRowPoly c P i.succ).eval t = (P i).eval t := by
  fin_cases i <;> rfl

/-- The pointwise error of the native fit. -/
theorem native_row_error {c : Fin 7 → ℝ} {P : Fin 2 → Polynomial ℝ} {G : Fin 3 → ℝ}
    {Ft : Fin 2 → ℝ} {t B δ graphError rowError : ℝ} (hB : 0 ≤ B)
    (hV : |c 4| ≤ B ∧ |c 6| ≤ B)
    (hgraph : |c 1 + 2 * c 2 * t - (G 0 + G 1 * c 4 + G 2 * c 6)| ≤ graphError)
    (hrow : ∀ i : Fin 2, |G i.succ - Ft i| ≤ rowError)
    (hP : ∀ i : Fin 2, |Ft i - (P i).eval t| ≤ δ) :
    ∀ j, |G j - (nativeRowPoly c P j).eval t| ≤ graphError + (1 + 2 * B) * (rowError + δ) := by
  have hrd : ∀ i : Fin 2, |G i.succ - (P i).eval t| ≤ rowError + δ := by
    intro i
    calc |G i.succ - (P i).eval t| = |(G i.succ - Ft i) + (Ft i - (P i).eval t)| := by ring_nf
      _ ≤ |G i.succ - Ft i| + |Ft i - (P i).eval t| := abs_add_le _ _
      _ ≤ rowError + δ := add_le_add (hrow i) (hP i)
  have hrd0 : 0 ≤ rowError + δ := le_trans (abs_nonneg _) (hrd 0)
  have hg0 : 0 ≤ graphError := le_trans (abs_nonneg _) hgraph
  intro j
  fin_cases j
  · -- the first row, through the velocity graph
    show |G 0 - (nativeRowPoly c P 0).eval t| ≤ _
    rw [nativeRowPoly_eval_zero]
    have he : G 0 - (c 1 + 2 * c 2 * t - (c 4 * (P 0).eval t + c 6 * (P 1).eval t)) =
        -(c 1 + 2 * c 2 * t - (G 0 + G 1 * c 4 + G 2 * c 6)) +
          (c 4 * ((P 0).eval t - G 1) + c 6 * ((P 1).eval t - G 2)) := by ring
    rw [he]
    have e1 : |c 4 * ((P 0).eval t - G 1)| ≤ B * (rowError + δ) := by
      rw [abs_mul, abs_sub_comm]
      exact mul_le_mul hV.1 (hrd 0) (abs_nonneg _) hB
    have e2 : |c 6 * ((P 1).eval t - G 2)| ≤ B * (rowError + δ) := by
      rw [abs_mul, abs_sub_comm]
      exact mul_le_mul hV.2 (hrd 1) (abs_nonneg _) hB
    calc _ ≤ |-(c 1 + 2 * c 2 * t - (G 0 + G 1 * c 4 + G 2 * c 6))| +
          (|c 4 * ((P 0).eval t - G 1)| + |c 6 * ((P 1).eval t - G 2)|) :=
          (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
      _ ≤ graphError + (B * (rowError + δ) + B * (rowError + δ)) := by
          rw [abs_neg]; exact add_le_add hgraph (add_le_add e1 e2)
      _ ≤ graphError + (1 + 2 * B) * (rowError + δ) := by nlinarith
  · show |G (Fin.succ 0) - (nativeRowPoly c P (Fin.succ 0)).eval t| ≤ _
    rw [nativeRowPoly_eval_succ]
    nlinarith [hrd 0]
  · show |G (Fin.succ 1) - (nativeRowPoly c P (Fin.succ 1)).eval t| ≤ _
    rw [nativeRowPoly_eval_succ]
    nlinarith [hrd 1]

/-- The degrees of the native fit. -/
theorem natDegree_nativeRowPoly_le {c : Fin 7 → ℝ} {P : Fin 2 → Polynomial ℝ} {M : ℕ}
    (hM : 1 ≤ M) (hP : ∀ i, (P i).natDegree ≤ M) : ∀ j, (nativeRowPoly c P j).natDegree ≤ M := by
  intro j
  fin_cases j
  · show (C (c 1) + C (2 * c 2) * X - (C (c 4) * P 0 + C (c 6) * P 1)).natDegree ≤ M
    have h1 : (C (c 1) + C (2 * c 2) * X).natDegree ≤ M :=
      (natDegree_add_le _ _).trans (max_le (by simp)
        (((natDegree_C_mul_le _ _).trans natDegree_X_le).trans hM))
    have h2 : (C (c 4) * P 0 + C (c 6) * P 1).natDegree ≤ M :=
      (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans (hP 0))
        ((natDegree_C_mul_le _ _).trans (hP 1)))
    exact (natDegree_sub_le _ _).trans (max_le h1 h2)
  · exact hP 0
  · exact hP 1

/-- The coefficients of the native fit. -/
theorem abs_coeff_nativeRowPoly_le {c : Fin 7 → ℝ} {P : Fin 2 → Polynomial ℝ} {B Cj : ℝ}
    (hB : 0 ≤ B) (hCj : 0 ≤ Cj) (hc : |c 1| ≤ B ∧ |c 2| ≤ B ∧ |c 4| ≤ B ∧ |c 6| ≤ B)
    (hP : ∀ i k, |(P i).coeff k| ≤ Cj) :
    ∀ j k, |(nativeRowPoly c P j).coeff k| ≤ 3 * B + (1 + 2 * B) * Cj := by
  intro j k
  fin_cases j
  · show |(C (c 1) + C (2 * c 2) * X - (C (c 4) * P 0 + C (c 6) * P 1)).coeff k| ≤ _
    rw [coeff_sub, coeff_add (C (c 4) * P 0), coeff_C_mul, coeff_C_mul]
    have hA : |(C (c 1) + C (2 * c 2) * X).coeff k| ≤ 3 * B := by
      rcases Nat.lt_trichotomy k 1 with hk | hk | hk
      · have hk0 : k = 0 := by omega
        subst hk0
        simp only [coeff_add, coeff_C_zero, coeff_C_mul, coeff_X_zero, mul_zero, add_zero]
        linarith [hc.1]
      · subst hk
        simp only [coeff_add, coeff_C_mul, coeff_X_one, mul_one, coeff_C, one_ne_zero,
          ↓reduceIte, zero_add]
        rw [abs_mul, abs_two]; linarith [hc.2.1]
      · have h0 : k ≠ 0 := by omega
        have h1 : 1 ≠ k := by omega
        simp only [coeff_add, coeff_C, h0, ↓reduceIte, coeff_C_mul, coeff_X, h1, mul_zero,
          add_zero, abs_zero]
        positivity
    have hP0 := hP 0 k
    have hP1 := hP 1 k
    have hB2 : |c 4 * (P 0).coeff k + c 6 * (P 1).coeff k| ≤ 2 * B * Cj := by
      calc _ ≤ |c 4 * (P 0).coeff k| + |c 6 * (P 1).coeff k| := abs_add_le _ _
        _ = |c 4| * |(P 0).coeff k| + |c 6| * |(P 1).coeff k| := by rw [abs_mul, abs_mul]
        _ ≤ B * Cj + B * Cj := add_le_add (mul_le_mul hc.2.2.1 hP0 (abs_nonneg _) hB)
            (mul_le_mul hc.2.2.2 hP1 (abs_nonneg _) hB)
        _ = 2 * B * Cj := by ring
    calc _ ≤ |(C (c 1) + C (2 * c 2) * X).coeff k| +
          |c 4 * (P 0).coeff k + c 6 * (P 1).coeff k| := abs_sub _ _
      _ ≤ 3 * B + 2 * B * Cj := add_le_add hA hB2
      _ ≤ 3 * B + (1 + 2 * B) * Cj := by nlinarith
  · show |(P 0).coeff k| ≤ _
    have := hP 0 k
    nlinarith [mul_nonneg hB hCj]
  · show |(P 1).coeff k| ≤ _
    have := hP 1 k
    nlinarith [mul_nonneg hB hCj]

/-- **The native three-row fit from a jet fit of the zoomed row.** All witness times stay labelled
on the same original line `z.1`, in the same dyadic block, including `z` itself. -/
theorem native_row_fit_of_jetFit {Λ : Type*} (c : Λ → Fin 7 → ℝ) {E : Set (Λ × ℝ)}
    {F : ℝ → Fin 2 → ℝ} (G : Λ × ℝ → Fin 3 → ℝ) {M T : ℕ} (hM : 2 ≤ M)
    {Cjet δ τ graphError rowError B : ℝ} (hB : 0 ≤ B) (hCjet : 0 ≤ Cjet)
    {z : Λ × ℝ} (hz : z ∈ E) (hcz : ∀ i, |c z.1 i| ≤ B)
    (hgraph : ∀ v, (z.1, v) ∈ E →
      |c z.1 1 + 2 * c z.1 2 * v - (G (z.1, v) 0 + G (z.1, v) 1 * c z.1 4 + G (z.1, v) 2 * c z.1 6)| ≤
        graphError)
    (hrow : ∀ v, (z.1, v) ∈ E → ∀ i : Fin 2, |G (z.1, v) i.succ - F v i| ≤ rowError)
    {P : Fin 2 → Polynomial ℝ} (hfit : JetFit E F M T Cjet δ τ z P) :
    ∃ Q : Fin 3 → Polynomial ℝ, (∀ j, (Q j).natDegree ≤ M) ∧
      (∀ j k, |(Q j).coeff k| ≤ 3 * B + (1 + 2 * B) * Cjet) ∧
      (∀ j, |G z j - (Q j).eval z.2| ≤ graphError + (1 + 2 * B) * (rowError + δ)) ∧
      ENNReal.ofReal τ ≤ volume {v | v ∈ dyadicBlock T z.2 ∧ (z.1, v) ∈ E ∧
        ∀ j, |G (z.1, v) j - (Q j).eval v| ≤ graphError + (1 + 2 * B) * (rowError + δ)} := by
  obtain ⟨hdeg, hcoef, hpt, hvol⟩ := hfit
  have hV : |c z.1 4| ≤ B ∧ |c z.1 6| ≤ B := ⟨hcz 4, hcz 6⟩
  refine ⟨nativeRowPoly (c z.1) P, natDegree_nativeRowPoly_le (by omega) hdeg,
    abs_coeff_nativeRowPoly_le hB hCjet ⟨hcz 1, hcz 2, hcz 4, hcz 6⟩ hcoef, ?_, ?_⟩
  · have hz' : (z.1, z.2) ∈ E := hz
    exact native_row_error hB hV (hgraph z.2 hz') (hrow z.2 hz') hpt
  · refine hvol.trans (measure_mono ?_)
    rintro v ⟨hvB, hvE, hvF⟩
    exact ⟨hvB, hvE, native_row_error hB hV (hgraph v hvE) (hrow v hvE) hvF⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
