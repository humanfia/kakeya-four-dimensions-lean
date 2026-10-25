import Submission.Obl.k4_general_wide_layer_offset_comparison.FinalHeight

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open Filter
open Submission.Obl.k4_contact_affine_residual_candidate_transfer

noncomputable section

def tableCoarseBudget (K J : ℝ) : ℝ := (4 * K + 5) * (6 * K + 5) * J

def tableOffsetBudget (K H d D : ℝ) : ℝ :=
  ((4 * K + 5) * (6 * K + 5) * (16800 * K ^ 2)) * D * (2 * H + 1) ^ d

def tableFineBudget (K H d D : ℝ) : ℝ := tableOffsetBudget K H d D * (3 * H) ^ d

def tableReverseBudget (K H d J D : ℝ) : ℝ := 16800 * K ^ 2 * (5 * H) ^ d * D * J

def tableReferenceBudget (K H d J D : ℝ) : ℝ :=
  tableCoarseBudget K J * tableReverseBudget K H d J D * (240 * H ^ 3)

def tableCountingHeight (K H d J D : ℝ) : ℝ :=
  3 * H + 10 * K + tableCoarseBudget K J + tableFineBudget K H d D +
    tableOffsetBudget K H d D + tableReverseBudget K H d J D

def finalTableHeight (K H d J D : ℝ) : ℝ :=
  comparisonHeight K (tableCountingHeight K H d J D) (4 * J) (tableReferenceBudget K H d J D)

/-- All finite-table counts and renewal costs fit one height chosen
before certifying the whole-fiber offsets. -/
theorem finalTableHeight_spec {K H d J D : ℝ}
    (hK : 1 ≤ K) (hH : 1 ≤ H) (hd : 0 ≤ d) (hJ : 1 ≤ J) (hD : 1 ≤ D) :
    let F := finalTableHeight K H d J D
    2 ≤ F ∧ K ≤ F ∧ H ≤ F ∧ 3 * H ≤ F ∧ 10 * K ≤ F ∧
      1 ≤ tableReferenceBudget K H d J D ∧
      4 * (4 * J) * tableReferenceBudget K H d J D ≤ F ∧
      tableCoarseBudget K J ≤ F ^ 4 ∧ tableFineBudget K H d D ≤ F ^ 4 ∧
      tableOffsetBudget K H d D ≤ F ^ 10 ∧ tableReverseBudget K H d J D ≤ F ^ 4 := by
  have hK0 : 0 ≤ K := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hA0 : 0 ≤ tableCoarseBudget K J := by unfold tableCoarseBudget; positivity
  have hO0 : 0 ≤ tableOffsetBudget K H d D := by unfold tableOffsetBudget; positivity
  have hF0 : 0 ≤ tableFineBudget K H d D := by unfold tableFineBudget; positivity
  have hRev0 : 0 ≤ tableReverseBudget K H d J D := by unfold tableReverseBudget; positivity
  have hA1 : 1 ≤ tableCoarseBudget K J := by
    unfold tableCoarseBudget
    calc
      (1 : ℝ) = 1 * 1 * 1 := by norm_num
      _ ≤ (4 * K + 5) * (6 * K + 5) * J := by gcongr <;> nlinarith
  have h5 : 1 ≤ (5 * H) ^ d := Real.one_le_rpow (by linarith) hd
  have hK2 : 1 ≤ K ^ 2 := one_le_pow₀ hK
  have hRev1 : 1 ≤ tableReverseBudget K H d J D := by
    unfold tableReverseBudget
    calc
      (1 : ℝ) = 1 * 1 * 1 * 1 * 1 := by norm_num
      _ ≤ 16800 * K ^ 2 * (5 * H) ^ d * D * J := by gcongr <;> nlinarith
  have hH3 : 1 ≤ H ^ 3 := one_le_pow₀ hH
  have hR1 : 1 ≤ tableReferenceBudget K H d J D := by
    unfold tableReferenceBudget
    calc
      (1 : ℝ) = 1 * 1 * 1 := by norm_num
      _ ≤ tableCoarseBudget K J * tableReverseBudget K H d J D * (240 * H ^ 3) := by
        gcongr <;> nlinarith
  have hB0 : 0 ≤ tableCountingHeight K H d J D := by unfold tableCountingHeight; positivity
  have hh := comparisonHeight_spec hK0 hB0 (by positivity : 0 ≤ 4 * J) (by linarith :
    0 ≤ tableReferenceBudget K H d J D)
  have hB : tableCountingHeight K H d J D ≤ finalTableHeight K H d J D := hh.2.2.1
  have h3 : 3 * H ≤ finalTableHeight K H d J D := by
    apply le_trans _ hB
    unfold tableCountingHeight
    linarith
  have h10 : 10 * K ≤ finalTableHeight K H d J D := by
    apply le_trans _ hB
    unfold tableCountingHeight
    linarith
  have h4 : finalTableHeight K H d J D ≤ (finalTableHeight K H d J D) ^ 4 :=
    le_self_pow₀ (by linarith [hh.1] : 1 ≤ finalTableHeight K H d J D) (by norm_num)
  have hten : finalTableHeight K H d J D ≤ (finalTableHeight K H d J D) ^ 10 :=
    le_self_pow₀ (by linarith [hh.1] : 1 ≤ finalTableHeight K H d J D) (by norm_num)
  refine ⟨hh.1, hh.2.1, (by linarith), h3, h10, hR1, hh.2.2.2, ?_, ?_, ?_, ?_⟩
  all_goals
    apply le_trans _ (hB.trans (by assumption))
    unfold tableCountingHeight
    linarith

/-- The explicit final height and original reference budget are subpower
whenever their four intrinsic input budgets are subpower. -/
theorem finalTableHeight_small {N K H J D : ℕ → ℝ} {d : ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop) (hd : 0 ≤ d)
    (hK : Small N K) (hH : Small N H) (hJ : Small N J) (hD : Small N D) :
    Small N (fun k => tableReferenceBudget (K k) (H k) d (J k) (D k)) ∧
      Small N (fun k => finalTableHeight (K k) (H k) d (J k) (D k)) := by
  have hN0 : ∀ k, 0 ≤ N k := fun k => zero_le_one.trans (hN k)
  have cn (a : ℝ) (ha : 0 ≤ a) : Small N (fun _ => a) := Small.const hNt ha
  have h4K5 := ((cn 4 (by norm_num)).mul hN0 hK).add hNt (cn 5 (by norm_num))
  have h6K5 := ((cn 6 (by norm_num)).mul hN0 hK).add hNt (cn 5 (by norm_num))
  have h168 := (cn 16800 (by norm_num)).mul hN0 (hK.pow hN0 hNt 2)
  have h2H1 := (((cn 2 (by norm_num)).mul hN0 hH).add hNt (cn 1 zero_le_one)).rpow hN hd
  have h3H := (cn 3 (by norm_num)).mul hN0 hH
  have h5H := ((cn 5 (by norm_num)).mul hN0 hH).rpow hN hd
  have hA : Small N (fun k => tableCoarseBudget (K k) (J k)) :=
    (h4K5.mul hN0 h6K5).mul hN0 hJ
  have hO : Small N (fun k => tableOffsetBudget (K k) (H k) d (D k)) :=
    (((h4K5.mul hN0 h6K5).mul hN0 h168).mul hN0 hD).mul hN0 h2H1
  have hF : Small N (fun k => tableFineBudget (K k) (H k) d (D k)) :=
    hO.mul hN0 (h3H.rpow hN hd)
  have hRev : Small N (fun k => tableReverseBudget (K k) (H k) d (J k) (D k)) :=
    ((h168.mul hN0 h5H).mul hN0 hD).mul hN0 hJ
  have hR : Small N (fun k => tableReferenceBudget (K k) (H k) d (J k) (D k)) :=
    (hA.mul hN0 hRev).mul hN0 ((cn 240 (by norm_num)).mul hN0 (hH.pow hN0 hNt 3))
  have hB : Small N (fun k => tableCountingHeight (K k) (H k) d (J k) (D k)) :=
    ((((h3H.add hNt ((cn 10 (by norm_num)).mul hN0 hK)).add hNt hA).add hNt hF).add hNt hO).add hNt hRev
  have h4J := (cn 4 (by norm_num)).mul hN0 hJ
  have hFinal := (((cn 2 (by norm_num)).add hNt hK).add hNt hB).add hNt
    (((cn 4 (by norm_num)).mul hN0 h4J).mul hN0 hR)
  exact ⟨hR, hFinal⟩

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
