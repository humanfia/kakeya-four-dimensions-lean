import Mathlib
import Submission.Lib.K4QuadraticSheetCore.SheetLines

/-! Adapted from: here:o223 (session x0777, branch x0777). -/

/-!
# Frame components of the projected second fundamental form

The six components of `M` in the moving horizontal frame `X = (1,0,-Z)`, `Zf = (0,1,t)`,
`Y = (0,0,1)` are base polynomials of total degree at most `4, 4, 4, 3, 3, 2`. We record their
evaluations and directional derivatives at the local data, the decomposition of a line's own
direction in the frame, and the recovery identities in polynomial form.
-/

namespace Submission.Lib.K4QuadraticSheetCore

open MvPolynomial Set

noncomputable section

/-- The horizontal frame as polynomial vector fields. -/
def frXP : Fin 3 → BasePoly := ![1, 0, -X 1]
def frZP : Fin 3 → BasePoly := ![0, 1, X 0]
def frYP : Fin 3 → BasePoly := ![0, 0, 1]

theorem evalVec_frXP (p : Fin 3 → ℝ) : evalVec p frXP = frX p := by
  funext i; fin_cases i <;> simp [evalVec, frXP, frX]

theorem evalVec_frZP (p : Fin 3 → ℝ) : evalVec p frZP = frZ p := by
  funext i; fin_cases i <;> simp [evalVec, frZP, frZ]

theorem evalVec_frYP (p : Fin 3 → ℝ) : evalVec p frYP = frY := by
  funext i; fin_cases i <;> simp [evalVec, frYP, frY]

theorem dirVec_frXP (W p : Fin 3 → ℝ) : dirVec W frXP p = dfrX W := by
  funext i; fin_cases i <;> simp [dirVec, dirD, frXP, dfrX, pderiv_X]

theorem dirVec_frZP (W p : Fin 3 → ℝ) : dirVec W frZP p = dfrZ W := by
  funext i; fin_cases i <;> simp [dirVec, dirD, frZP, dfrZ, pderiv_X]

theorem dirVec_frYP (W p : Fin 3 → ℝ) : dirVec W frYP p = ![0, 0, 0] := by
  funext i; fin_cases i <;> simp [dirVec, dirD, frYP]

theorem frXP_degree (i : Fin 3) : (frXP i).totalDegree ≤ 1 := by
  fin_cases i <;> simp [frXP, totalDegree_neg]

theorem frZP_degree (i : Fin 3) : (frZP i).totalDegree ≤ 1 := by
  fin_cases i <;> simp [frZP]

theorem frYP_degree (i : Fin 3) : (frYP i).totalDegree ≤ 0 := by
  fin_cases i <;> simp [frYP]

section Degree

variable (α : ℝ) (β γ : BasePoly)

theorem sffPoly_degree (hβ : β.totalDegree ≤ 1) (hγ : γ.totalDegree ≤ 2) (i j : Fin 3) :
    (sffPoly α β γ i j).totalDegree ≤ 2 := by
  have hbi : ∀ i : Fin 3, (pderiv i β).totalDegree ≤ 0 := fun i =>
    (Submission.Lib.K4HiddenQuadratic.totalDegree_pderiv_le_pred β i).trans (by omega)
  have hgi : ∀ i : Fin 3, (pderiv i γ).totalDegree ≤ 1 := fun i =>
    (Submission.Lib.K4HiddenQuadratic.totalDegree_pderiv_le_pred γ i).trans (by omega)
  have hgij : ∀ i j : Fin 3, (pderiv i (pderiv j γ)).totalDegree ≤ 0 := fun i j =>
    (Submission.Lib.K4HiddenQuadratic.totalDegree_pderiv_le_pred _ i).trans
      (by have := hgi j; omega)
  have hmul : ∀ (p q : BasePoly) (a b : ℕ), p.totalDegree ≤ a → q.totalDegree ≤ b →
      (p * q).totalDegree ≤ a + b := fun p q a b hp hq =>
    (totalDegree_mul p q).trans (add_le_add hp hq)
  have hadd : ∀ (p q : BasePoly) (a : ℕ), p.totalDegree ≤ a → q.totalDegree ≤ a →
      (p + q).totalDegree ≤ a := fun p q a hp hq => (totalDegree_add p q).trans (max_le hp hq)
  have hsub : ∀ (p q : BasePoly) (a : ℕ), p.totalDegree ≤ a → q.totalDegree ≤ a →
      (p - q).totalDegree ≤ a := fun p q a hp hq => (totalDegree_sub p q).trans (max_le hp hq)
  have hC : ∀ c : ℝ, (C c : BasePoly).totalDegree ≤ 0 := fun c => by simp
  unfold sffPoly
  apply hadd
  · apply hadd
    · apply hsub
      · exact hmul _ _ 2 0 (hmul _ _ 2 0 (hmul _ _ 0 2 (hC 2) hγ) (hbi i)) (hbi j)
      · exact hmul _ _ 1 1 hβ (hadd _ _ 1 (hmul _ _ 0 1 (hbi i) (hgi j))
          (hmul _ _ 1 0 (hgi i) (hbi j)))
    · exact hmul _ _ 1 1 (hmul _ _ 0 1 (hC _) (hgi i)) (hgi j)
  · apply hmul _ _ 2 0 _ (hgij i j)
    apply hsub
    · rw [pow_two]; exact hmul _ _ 1 1 hβ hβ
    · exact hmul _ _ 0 2 (hC _) hγ

theorem sffBP_degree (hβ : β.totalDegree ≤ 1) (hγ : γ.totalDegree ≤ 2)
    (U V : Fin 3 → BasePoly) (du dv : ℕ) (hU : ∀ i, (U i).totalDegree ≤ du)
    (hV : ∀ j, (V j).totalDegree ≤ dv) :
    (sffBP α β γ U V).totalDegree ≤ du + dv + 2 := by
  unfold sffBP
  apply totalDegree_finsetSum_le
  intro i _
  apply totalDegree_finsetSum_le
  intro j _
  exact (totalDegree_mul _ _).trans (add_le_add ((totalDegree_mul _ _).trans
    (add_le_add (hU i) (hV j))) (sffPoly_degree α β γ hβ hγ i j))

theorem discP_degree (hβ : β.totalDegree ≤ 1) (hγ : γ.totalDegree ≤ 2) :
    (discP α β γ).totalDegree ≤ 2 := by
  unfold discP
  apply (totalDegree_sub _ _).trans (max_le _ _)
  · rw [pow_two]; exact (totalDegree_mul _ _).trans (by omega)
  · exact (totalDegree_mul _ _).trans (by simp only [totalDegree_C]; omega)

end Degree

section Components

variable (α : ℝ) (β γ : BasePoly)

/-- The six frame components as base polynomials. -/
def cXX : BasePoly := sffBP α β γ frXP frXP
def cXZ : BasePoly := sffBP α β γ frXP frZP
def cZZ : BasePoly := sffBP α β γ frZP frZP
def cXY : BasePoly := sffBP α β γ frXP frYP
def cZY : BasePoly := sffBP α β γ frZP frYP
def cYY : BasePoly := sffBP α β γ frYP frYP

/-- Abbreviation for the projected form at the local data of `p`. -/
def sffAt (p : Fin 3 → ℝ) (U V : Fin 3 → ℝ) : ℝ :=
  sffB α (eval p γ) (eval p β) (gradAt γ p) (gradAt β p) (hessAt γ p) U V

def sffDAt (p : Fin 3 → ℝ) (W U V : Fin 3 → ℝ) : ℝ :=
  sffD α (eval p β) (gradAt γ p) (gradAt β p) (hessAt γ p) W U V

theorem sffB_comm (a g b : ℝ) (gr br : Fin 3 → ℝ) (H : Fin 3 → Fin 3 → ℝ) (hH : SymH H)
    (U V : Fin 3 → ℝ) : sffB a g b gr br H U V = sffB a g b gr br H V U := by
  obtain ⟨h10, h20, h21⟩ := hH
  simp only [sffB, dot3, bil3, h10, h20, h21]
  ring

theorem eval_cXX (p : Fin 3 → ℝ) : eval p (cXX α β γ) = sffAt α β γ p (frX p) (frX p) := by
  rw [cXX, eval_sffBP, evalVec_frXP]; rfl
theorem eval_cXZ (p : Fin 3 → ℝ) : eval p (cXZ α β γ) = sffAt α β γ p (frX p) (frZ p) := by
  rw [cXZ, eval_sffBP, evalVec_frXP, evalVec_frZP]; rfl
theorem eval_cZZ (p : Fin 3 → ℝ) : eval p (cZZ α β γ) = sffAt α β γ p (frZ p) (frZ p) := by
  rw [cZZ, eval_sffBP, evalVec_frZP]; rfl
theorem eval_cXY (p : Fin 3 → ℝ) : eval p (cXY α β γ) = sffAt α β γ p (frX p) frY := by
  rw [cXY, eval_sffBP, evalVec_frXP, evalVec_frYP]; rfl
theorem eval_cZY (p : Fin 3 → ℝ) : eval p (cZY α β γ) = sffAt α β γ p (frZ p) frY := by
  rw [cZY, eval_sffBP, evalVec_frZP, evalVec_frYP]; rfl
theorem eval_cYY (p : Fin 3 → ℝ) : eval p (cYY α β γ) = sffAt α β γ p frY frY := by
  rw [cYY, eval_sffBP, evalVec_frYP]; rfl

variable (hβ : β.totalDegree ≤ 1) (hγ : γ.totalDegree ≤ 2)
include hβ hγ

theorem dirD_cXX (W p : Fin 3 → ℝ) :
    dirD W (cXX α β γ) p =
      sffDAt α β γ p W (frX p) (frX p) + 2 * sffAt α β γ p (dfrX W) (frX p) := by
  rw [cXX, dirD_sffBP α β γ hβ hγ, evalVec_frXP, dirVec_frXP]
  simp only [sffDAt, sffAt]
  rw [sffB_comm _ _ _ _ _ _ (hessAt_symm γ p) (frX p) (dfrX W)]
  ring

theorem dirD_cXZ (W p : Fin 3 → ℝ) :
    dirD W (cXZ α β γ) p =
      sffDAt α β γ p W (frX p) (frZ p) + sffAt α β γ p (dfrX W) (frZ p) +
        sffAt α β γ p (frX p) (dfrZ W) := by
  rw [cXZ, dirD_sffBP α β γ hβ hγ, evalVec_frXP, evalVec_frZP, dirVec_frXP, dirVec_frZP]
  rfl

theorem dirD_cZZ (W p : Fin 3 → ℝ) :
    dirD W (cZZ α β γ) p =
      sffDAt α β γ p W (frZ p) (frZ p) + 2 * sffAt α β γ p (dfrZ W) (frZ p) := by
  rw [cZZ, dirD_sffBP α β γ hβ hγ, evalVec_frZP, dirVec_frZP]
  simp only [sffDAt, sffAt]
  rw [sffB_comm _ _ _ _ _ _ (hessAt_symm γ p) (frZ p) (dfrZ W)]
  ring

theorem dirD_cXY (W p : Fin 3 → ℝ) :
    dirD W (cXY α β γ) p =
      sffDAt α β γ p W (frX p) frY + sffAt α β γ p (dfrX W) frY := by
  rw [cXY, dirD_sffBP α β γ hβ hγ, evalVec_frXP, evalVec_frYP, dirVec_frXP, dirVec_frYP]
  simp only [sffDAt, sffAt, sffB, dot3, bil3, Matrix.cons_val]
  ring

theorem dirD_cZY (W p : Fin 3 → ℝ) :
    dirD W (cZY α β γ) p =
      sffDAt α β γ p W (frZ p) frY + sffAt α β γ p (dfrZ W) frY := by
  rw [cZY, dirD_sffBP α β γ hβ hγ, evalVec_frZP, evalVec_frYP, dirVec_frZP, dirVec_frYP]
  simp only [sffDAt, sffAt, sffB, dot3, bil3, Matrix.cons_val]
  ring

/-- Recovery identities in polynomial form, evaluated at a point. -/
theorem recover_cXY (p : Fin 3 → ℝ) :
    6 * eval p (discP α β γ) * eval p (cXY α β γ) =
      3 * (eval p (cXX α β γ) * dirD (frZ p) (discP α β γ) p -
          eval p (cXZ α β γ) * dirD (frX p) (discP α β γ) p) -
        2 * eval p (discP α β γ) *
          (dirD (frZ p) (cXX α β γ) p - dirD (frX p) (cXZ α β γ) p) := by
  rw [eval_discP, eval_cXY, eval_cXX, eval_cXZ, dirD_discP, dirD_discP,
    dirD_cXX α β γ hβ hγ, dirD_cXZ α β γ hβ hγ]
  have h := sff_recover_XY α (eval p γ) (eval p β) (gradAt γ p) (gradAt β p) (hessAt γ p) p
    (hessAt_symm γ p)
  simp only [sffAt, sffDAt]
  linarith

theorem recover_cZY (p : Fin 3 → ℝ) :
    6 * eval p (discP α β γ) * eval p (cZY α β γ) =
      2 * eval p (discP α β γ) *
          (dirD (frX p) (cZZ α β γ) p - dirD (frZ p) (cXZ α β γ) p) -
        3 * (eval p (cZZ α β γ) * dirD (frX p) (discP α β γ) p -
          eval p (cXZ α β γ) * dirD (frZ p) (discP α β γ) p) := by
  rw [eval_discP, eval_cZY, eval_cZZ, eval_cXZ, dirD_discP, dirD_discP,
    dirD_cZZ α β γ hβ hγ, dirD_cXZ α β γ hβ hγ]
  have h := sff_recover_YZ α (eval p γ) (eval p β) (gradAt γ p) (gradAt β p) (hessAt γ p) p
    (hessAt_symm γ p)
  rw [sffB_comm _ _ _ _ _ _ (hessAt_symm γ p) frY (frZ p)] at h
  simp only [sffAt, sffDAt]
  linarith

theorem recover_cYY (p : Fin 3 → ℝ) :
    4 * eval p (discP α β γ) * eval p (cYY α β γ) =
      3 * (eval p (cXY α β γ) * dirD (frZ p) (discP α β γ) p -
          eval p (cZY α β γ) * dirD (frX p) (discP α β γ) p) -
        2 * eval p (discP α β γ) *
          (dirD (frZ p) (cXY α β γ) p - dirD (frX p) (cZY α β γ) p) := by
  rw [eval_discP, eval_cYY, eval_cXY, eval_cZY, dirD_discP, dirD_discP,
    dirD_cXY α β γ hβ hγ, dirD_cZY α β γ hβ hγ]
  have h := sff_recover_YY α (eval p γ) (eval p β) (gradAt γ p) (gradAt β p) (hessAt γ p) p
    (hessAt_symm γ p)
  simp only [sffAt, sffDAt]
  linarith

end Components

/-- A line's own direction in the horizontal frame at its point. -/
theorem sffB_lineV (a g bb : ℝ) (gr br : Fin 3 → ℝ) (H : Fin 3 → Fin 3 → ℝ) (hH : SymH H)
    (b : Fin 6 → ℝ) (σ : ℝ) :
    sffB a g bb gr br H (lineV b) (lineV b) =
      (sffB a g bb gr br H (frX (lineP b σ)) (frX (lineP b σ)) +
        2 * b 3 * sffB a g bb gr br H (frX (lineP b σ)) (frZ (lineP b σ)) +
        b 3 ^ 2 * sffB a g bb gr br H (frZ (lineP b σ)) (frZ (lineP b σ))) +
      2 * (b 4 + b 0) * (sffB a g bb gr br H (frX (lineP b σ)) frY +
        b 3 * sffB a g bb gr br H (frZ (lineP b σ)) frY) +
      (b 4 + b 0) ^ 2 * sffB a g bb gr br H frY frY := by
  obtain ⟨h10, h20, h21⟩ := hH
  simp only [sffB, dot3, bil3, frX, frZ, frY, lineV, lineP, Matrix.cons_val, h10, h20, h21]
  ring

end

end Submission.Lib.K4QuadraticSheetCore
