/-
Adapted from: here:o062
Purpose: Shared scalar switching helper SwitchScaling.
Original owned source: x0511, commit c45941b, Submission/Obl/k4_scalar_mesh_projection/SwitchScaling.lean.
-/

/-
Local LOT source: session x0511, branch x0511, commit c45941b,
Submission/Obl/k4_scalar_mesh_projection/SwitchScaling.lean.
Reviewed and integrated by x0212 for o062.
-/

import Submission.Lib.K4ScalarSwitching.SwitchPathBounds

namespace Submission.Lib.K4ScalarSwitching.Switching

open Set MeasureTheory MvPolynomial
open scoped Pointwise
open Submission.Lib.K4ScalarSwitching.PolynomialDegree

noncomputable def dilatePolynomial (q : ℝ) :
    MvPolynomial (Fin 4) ℝ →ₐ[ℝ] MvPolynomial (Fin 4) ℝ :=
  aeval (fun i => C q * X i)

theorem eval_dilatePolynomial (q : ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (z : Fin 4 → ℝ) :
    eval z (dilatePolynomial q P) = eval (q • z) P := by
  rw [dilatePolynomial, eval_substitution]
  simp only [map_mul, eval_C, eval_X]
  rfl

theorem dilatePolynomial_degree (q : ℝ) (P : MvPolynomial (Fin 4) ℝ) :
    (dilatePolynomial q P).totalDegree ≤ P.totalDegree := by
  apply degree_aeval_le
  intro i
  exact (degree_C_mul_le _ _).trans (by simp)

theorem pderiv_dilatePolynomial (q : ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (i : Fin 4) :
    pderiv i (dilatePolynomial q P) = C q * dilatePolynomial q (pderiv i P) := by
  rw [dilatePolynomial, partial_aeval]
  simp [pderiv_X, Pi.single_apply, mul_comm]

theorem linear_coefficient_dilatePolynomial (q : ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (i : Fin 4) :
    (dilatePolynomial q P).coeff (Finsupp.single i 1) =
      q * P.coeff (Finsupp.single i 1) := by
  rw [← partial_eval_zero_eq_coeff, pderiv_dilatePolynomial, map_mul, eval_C,
    eval_dilatePolynomial, smul_zero, partial_eval_zero_eq_coeff]

theorem smul_mem_symmetric_cube {q : ℝ} (hq : 0 < q) (z : Fin 4 → ℝ) :
    q • z ∈ Icc (fun _ => -q) (fun _ => q) ↔
      z ∈ Icc (fun _ : Fin 4 => (-1 : ℝ)) (1 : Fin 4 → ℝ) := by
  simp only [mem_Icc, Pi.le_def, Pi.smul_apply, smul_eq_mul, Pi.one_apply]
  constructor
  · intro hz
    constructor <;> intro i
    · nlinarith [hz.1 i]
    · nlinarith [hz.2 i]
  · intro hz
    constructor <;> intro i
    · nlinarith [hz.1 i]
    · nlinarith [hz.2 i]

/-- Dilation of the increment box scales exceptional volume by q^4 and
every detected linear coefficient by q, with no other loss. -/
theorem dilated_sublevel_volume {q : ℝ} (hq : 0 < q)
    (P : MvPolynomial (Fin 4) ℝ) (E : ℝ) :
    volume {δ : Fin 4 → ℝ | δ ∈ Icc (fun _ => -q) (fun _ => q) ∧ |eval δ P| ≤ E} =
      ENNReal.ofReal (q ^ 4) *
        volume {z : Fin 4 → ℝ | z ∈ Icc (fun _ : Fin 4 => (-1 : ℝ)) (1 : Fin 4 → ℝ) ∧
          |eval z (dilatePolynomial q P)| ≤ E} := by
  let T : Set (Fin 4 → ℝ) :=
    {z | z ∈ Icc (fun _ : Fin 4 => (-1 : ℝ)) (1 : Fin 4 → ℝ) ∧ |eval z (dilatePolynomial q P)| ≤ E}
  have heq : {δ : Fin 4 → ℝ | δ ∈ Icc (fun _ => -q) (fun _ => q) ∧ |eval δ P| ≤ E} =
      q • T := by
    ext δ
    constructor
    · intro hδ
      refine ⟨q⁻¹ • δ, ?_, ?_⟩
      · have hcancel : q • (q⁻¹ • δ) = δ := by simp [smul_smul, hq.ne']
        refine ⟨(smul_mem_symmetric_cube hq _).mp (by simpa only [hcancel] using hδ.1), ?_⟩
        simpa only [eval_dilatePolynomial, hcancel] using hδ.2
      · simp [smul_smul, hq.ne']
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(smul_mem_symmetric_cube hq z).mpr hz.1,
        by simpa only [eval_dilatePolynomial] using hz.2⟩
  rw [heq, Measure.addHaar_smul]
  simp only [Module.finrank_pi, Fintype.card_fin,
    abs_of_nonneg (by positivity : 0 ≤ q ^ 4)]
  rfl

theorem scaled_sublevel_volume_lt {q η E : ℝ} (hq : 0 < q)
    (P : MvPolynomial (Fin 4) ℝ)
    (hsmall : volume {z : Fin 4 → ℝ |
      z ∈ Icc (fun _ : Fin 4 => (-1 : ℝ)) (1 : Fin 4 → ℝ) ∧
        |eval z (dilatePolynomial q P)| ≤ E} < ENNReal.ofReal η) :
    volume {δ : Fin 4 → ℝ | δ ∈ Icc (fun _ => -q) (fun _ => q) ∧ |eval δ P| ≤ E} <
      ENNReal.ofReal (q ^ 4 * η) := by
  rw [dilated_sublevel_volume hq, ENNReal.ofReal_mul (by positivity : 0 ≤ q ^ 4)]
  have hpos : ENNReal.ofReal (q ^ 4) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  simpa only [mul_comm] using
    ENNReal.mul_lt_mul_left hpos ENNReal.ofReal_ne_top hsmall

end Submission.Lib.K4ScalarSwitching.Switching
