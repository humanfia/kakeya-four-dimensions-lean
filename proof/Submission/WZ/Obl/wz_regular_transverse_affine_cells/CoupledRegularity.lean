-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.CoupledRegularity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.CoupledPruning
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.BallTests

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open MeasureTheory Set Metric
open scoped ENNReal

/-- Simultaneous local regularity and pointwise transversality. The remainder has
only nontransverse incident pairs and is physically disjoint from the regular core. -/
lemma regular_broad_core {n : ℕ} (Rel : Fin n → Fin n → Prop)
    (P Y : Fin n → Set E) (hPm : ∀ i, MeasurableSet (P i))
    (hPc : ∀ i, Convex ℝ (P i)) (hYm : ∀ i, MeasurableSet (Y i)) (hYP : ∀ i, Y i ⊆ P i)
    {R a h : ℝ} (hPbound : ∀ i, P i ⊆ closedBall 0 R) (ha : 0 < a) (hh : 0 ≤ h)
    {K : ℕ} (hK : (1 / 2 : ℝ) ^ K < 2 * a) :
    ∃ H B : Fin n → Set E,
      (∀ i, MeasurableSet (H i)) ∧ (∀ i, MeasurableSet (B i)) ∧
      (∀ i, H i ⊆ Y i) ∧ (∀ i, B i ⊆ Y i) ∧
      Disjoint (⋃ i, H i) (⋃ i, B i) ∧
      (∀ p, (∃ i, p ∈ H i) → ∃ i j, p ∈ H i ∧ p ∈ H j ∧ Rel i j) ∧
      (∀ p i j, p ∈ B i → p ∈ B j → ¬Rel i j) ∧
      (∑ i, volume (Y i)) ≤ (∑ i, volume (H i)) + (∑ i, volume (B i)) +
        ENNReal.ofReal (512 * h) * (1 + 1000 * (K + 1 : ℕ) : ℝ≥0∞) * ∑ i, volume (P i) ∧
      (∀ i, (H i).Nonempty → ENNReal.ofReal h * volume (P i) ≤ volume (H i)) ∧
      (∀ i p, p ∈ H i → ∀ r : ℝ, a ≤ r → r ≤ 1 →
        ENNReal.ofReal h * volume (P i ∩ ball p r) ≤ volume (H i ∩ ball p r)) := by
  classical
  let τ : ℝ≥0∞ := ENNReal.ofReal (512 * h)
  let T := insert none ((Grid.tests K R).image some)
  let F : Finset (Fin n × Option Grid.TestIndex) := Finset.univ.product T
  let V : Option Grid.TestIndex → Set E := fun z => z.elim Set.univ Grid.testBall
  let cost : Fin n × Option Grid.TestIndex → ℝ≥0∞ := fun z => τ * volume (P z.1 ∩ V z.2)
  have hVm : ∀ z, MeasurableSet (V z) := by
    intro z
    cases z with
    | none => exact MeasurableSet.univ
    | some z => exact Grid.testBall_measurable z
  obtain ⟨H, B, hHm, hBm, hHY, hBY, hHB, hHbr, hBnar, hmass, hreg⟩ :=
    coupled_density_pruning Rel Prod.fst (fun z => V z.2) cost F
      (fun z _ => hVm z.2) Y hYm
  have hcost : (∑ z ∈ F, cost z) ≤ τ * (1 + 1000 * (K + 1 : ℕ) : ℝ≥0∞) *
      ∑ i, volume (P i) := by
    dsimp [F]
    rw [Finset.sum_product, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    dsimp [T, cost]
    rw [Finset.sum_insert (by simp), Finset.sum_image (by
      intro z _ z' _ hzz'
      exact Option.some.inj hzz')]
    simp only [V, Option.elim_none, Option.elim_some, inter_univ]
    rw [← Finset.mul_sum]
    have hs := Grid.sum_tests_inter_le K R (P i) (hPm i)
    calc τ * volume (P i) + τ * ∑ z ∈ Grid.tests K R, volume (P i ∩ Grid.testBall z)
        ≤ τ * volume (P i) + τ * ((1000 * (K + 1 : ℕ) : ℝ≥0∞) * volume (P i)) :=
          add_le_add le_rfl (mul_le_mul_right hs τ)
      _ = _ := by ring
  have hmember_none (i : Fin n) : (i, none) ∈ F := by simp [F, T]
  have hmember_some (i : Fin n) (z : Grid.TestIndex) (hz : z ∈ Grid.tests K R) :
      (i, some z) ∈ F := by simp [F, T, hz]
  have hτ : ENNReal.ofReal h ≤ τ := ENNReal.ofReal_le_ofReal (by nlinarith)
  refine ⟨H, B, hHm, hBm, hHY, hBY, hHB, hHbr, hBnar,
    hmass.trans (add_le_add le_rfl hcost), ?_, ?_⟩
  · intro i hHi
    have hg := hreg (i, none) (hmember_none i) (by simpa only [V, Option.elim_none, inter_univ] using hHi)
    simp only [cost, V, Option.elim_none, inter_univ] at hg
    exact (mul_le_mul_left hτ _).trans hg
  · intro i p hp r har hr1
    obtain ⟨z, hz, hpz, hsub, hcompare⟩ := Grid.exists_comparison_test (hPc i) (hPbound i)
      ha hK (hYP i (hHY i hp)) har hr1
    have hg := hreg (i, some z) (hmember_some i z hz) ⟨p, hp, hpz⟩
    have hc : τ * ENNReal.ofReal (1 / 512 : ℝ) = ENNReal.ofReal h := by
      dsimp [τ]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    calc ENNReal.ofReal h * volume (P i ∩ ball p r)
        = τ * (ENNReal.ofReal (1 / 512 : ℝ) * volume (P i ∩ ball p r)) := by rw [← mul_assoc, hc]
      _ ≤ τ * volume (P i ∩ Grid.testBall z) := mul_le_mul_right hcompare τ
      _ ≤ volume (H i ∩ Grid.testBall z) := hg
      _ ≤ volume (H i ∩ ball p r) := measure_mono (inter_subset_inter_right _ hsub)

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
