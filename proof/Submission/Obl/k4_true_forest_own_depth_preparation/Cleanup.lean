import Submission.Obl.k4_true_forest_own_depth_preparation.CommonCut
import Submission.Obl.k4_true_forest_own_depth_preparation.ForestPruning
import Submission.Obl.k4_true_forest_own_depth_preparation.LayerSums
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.MassBounds

namespace Submission.Obl.k4_true_forest_own_depth_preparation

open MeasureTheory Set Classical

/-- A common cutoff followed by ancestor-closed label removal preserves all
layers up to the single stated error budget. -/
theorem common_cut_forest_cleanup {X : Type*} [MeasurableSpace X] {C W m : ℕ}
    (μ : Fin W → Measure X) (ω : Fin W → ENNReal)
    (lev : Fin C → ℕ) (par : Fin C → Fin C) (γ : Fin C → Fin W)
    (F H : Fin C → Set X) (sat : Fin C → Prop) [DecidablePred sat]
    (hFm : ∀ b, MeasurableSet (F b)) (hHm : ∀ b, MeasurableSet (H b))
    (hFfin : ∀ b, μ (γ b) (F b) ≠ ⊤) (hlev : ∀ b, lev b < m)
    (hpar : ∀ b, 0 < lev b → lev (par b) + 1 = lev b)
    (hbudget : ∀ a, (∑ b, if 0 < lev b ∧ par b = a then
      ω (γ b) * μ (γ b) (F b) else 0) ≤ ω (γ a) * μ (γ a) (F a))
    (hmult : ∀ i, i < m → ∀ w p,
      (∑ b ∈ Finset.univ.filter (fun b => lev b = i ∧ γ b = w),
        (F b).indicator (1 : X → ENNReal) p) ≤ 2)
    (cutLoss heavyLoss : ENNReal)
    (hcut : (∑ b, ω (γ b) * μ (γ b) (F b \ H b)) ≤ cutLoss)
    (hheavy : (∑ b, if ¬sat b then ω (γ b) * μ (γ b) (F b) else 0) ≤ heavyLoss) :
    let G := fun b => F b ∩ commonGood γ F H (γ b)
    let good := fun b => sat b ∧ μ (γ b) (F b) ≤ 2 * μ (γ b) (G b)
    ∀ i, i < m →
      (∑ b, if lev b = i then ω (γ b) * μ (γ b) (F b) else 0) ≤
        (∑ b, if lev b = i ∧ Kept lev par good b then ω (γ b) * μ (γ b) (G b) else 0) +
          ((2 + 4 * (m : ENNReal)) * cutLoss + heavyLoss) := by
  dsimp only
  let G₀ := commonGood γ F H
  let G := fun b => F b ∩ G₀ (γ b)
  let good := fun b => sat b ∧ μ (γ b) (F b) ≤ 2 * μ (γ b) (G b)
  let mass := fun b => ω (γ b) * μ (γ b) (F b)
  let trim := fun b => ω (γ b) * μ (γ b) (F b \ G₀ (γ b))
  have hGm (w) : MeasurableSet (G₀ w) := measurableSet_commonGood γ F H hFm hHm w
  have hworld : (∑ w, ω w * μ w (G₀ w)ᶜ) ≤ cutLoss :=
    (commonGood_loss_le μ ω γ F H).trans hcut
  have htrim (i) (hi : i < m) : (∑ b, if lev b = i then trim b else 0) ≤ 2 * cutLoss := by
    let Fᵢ : Fin C → Set X := fun b => if lev b = i then F b else ∅
    have hFᵢ (b) : MeasurableSet (Fᵢ b) := by
      dsimp only [Fᵢ]
      split_ifs
      · exact hFm b
      · exact MeasurableSet.empty
    have hm (w) (p) : (∑ b ∈ Finset.univ.filter (fun b => γ b = w),
        (Fᵢ b).indicator (1 : X → ENNReal) p) ≤ 2 := by
      have heq : (∑ b ∈ Finset.univ.filter (fun b => γ b = w),
          (Fᵢ b).indicator (1 : X → ENNReal) p) =
          ∑ b ∈ Finset.univ.filter (fun b => lev b = i ∧ γ b = w),
            (F b).indicator (1 : X → ENNReal) p := by
        simp only [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro b _
        by_cases hb : lev b = i <;> simp [Fᵢ, hb]
      rw [heq]
      exact hmult i hi w p
    have h := (weighted_common_cut_loss μ ω γ Fᵢ G₀ hFᵢ hGm hm).trans
      (mul_le_mul_right hworld 2)
    apply le_trans _ h
    apply Finset.sum_le_sum
    intro b _
    by_cases hb : lev b = i <;> simp [Fᵢ, trim, hb]
  have halltrim : (∑ b, trim b) ≤ 2 * (m : ENNReal) * cutLoss := by
    have h := sum_le_depth_mul lev hlev trim (2 * cutLoss) htrim
    exact h.trans_eq (by ring)
  have hbadhalf (b) (hb : ¬ μ (γ b) (F b) ≤ 2 * μ (γ b) (G b)) :
      mass b ≤ 2 * trim b := by
    have hGfin : μ (γ b) (G b) ≠ ⊤ :=
      ne_top_of_le_ne_top (hFfin b) (measure_mono inter_subset_left)
    have hμ := Submission.Obl.k4_scalar_terminal_chart_packet_extraction.le_two_mul_inter_of_diff_le
      (μ (γ b)) (P := F b) (X := (G₀ (γ b))ᶜ) hGfin
      (by simpa only [sdiff_compl] using (le_rfl : μ (γ b) (G b) ≤ μ (γ b) (G b)))
      (lt_of_not_ge hb).le
    have hμ' : μ (γ b) (F b) ≤ 2 * μ (γ b) (F b \ G₀ (γ b)) := by
      simpa only [Set.sdiff_eq] using hμ
    have h := mul_le_mul_right hμ' (ω (γ b))
    dsimp only [mass, trim]
    exact h.trans_eq (by ring)
  have hbad : (∑ b, if ¬good b then mass b else 0) ≤
      heavyLoss + 4 * (m : ENNReal) * cutLoss := by
    have hs : (∑ b, if ¬good b then mass b else 0) ≤
        (∑ b, if ¬sat b then mass b else 0) + 2 * ∑ b, trim b := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro b _
      by_cases hs : sat b
      · by_cases hh : μ (γ b) (F b) ≤ 2 * μ (γ b) (G b)
        · simp [good, hs, hh]
        · simpa only [good, hs, hh, true_and, not_false_eq_true, not_true_eq_false,
            ite_true, ite_false, zero_add] using hbadhalf b hh
      · simp only [good, hs, false_and, not_false_eq_true, ite_true]
        exact le_self_add
    apply hs.trans
    apply (add_le_add hheavy (mul_le_mul_right halltrim 2)).trans_eq
    ring
  intro i hi
  have hremove := (forest_removed_mass_le lev par mass good hpar hbudget i).trans hbad
  have hcover : (∑ b, if lev b = i then mass b else 0) ≤
      (∑ b, if lev b = i ∧ Kept lev par good b then ω (γ b) * μ (γ b) (G b) else 0) +
      (∑ b, if lev b = i ∧ ¬Kept lev par good b then mass b else 0) +
      ∑ b, if lev b = i then trim b else 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro b _
    by_cases hb : lev b = i
    · by_cases hk : Kept lev par good b
      · simp only [hb, hk, and_self, not_true_eq_false, and_false, ite_true, ite_false, add_zero]
        have hμ : μ (γ b) (F b) ≤ μ (γ b) (G b) + μ (γ b) (F b \ G₀ (γ b)) := by
          calc
            _ = μ (γ b) ((F b ∩ G₀ (γ b)) ∪ (F b \ G₀ (γ b))) := by rw [inter_union_sdiff]
            _ ≤ _ := measure_union_le _ _
        simpa only [mass, trim, mul_add] using mul_le_mul_right hμ (ω (γ b))
      · simp only [hb, hk, false_and, and_false, not_false_eq_true, and_self,
          ite_true, ite_false, zero_add]
        exact le_self_add
    · simp [hb]
  apply hcover.trans
  apply (add_le_add (add_le_add le_rfl hremove) (htrim i hi)).trans_eq
  ring

end Submission.Obl.k4_true_forest_own_depth_preparation
