-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_parameter_weak_strong_reduction.Measure.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

noncomputable section

namespace WangZahlLot.Obl.wz_parameter_weak_strong_reduction

open MeasureTheory Set
open Classical
open scoped ENNReal

def strip (δ : ℝ) (g : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ∈ Icc (-1) 1 ∧ |p.1 - g p.2| ≤ δ}

def multiplicity {n : ℕ} (δ : ℝ) (g : Fin n → ℝ → ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ∑ i, (strip δ (g i)).indicator (fun _ => 1) p

theorem measurableSet_strip (δ : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    MeasurableSet (strip δ g) := by
  exact ((isClosed_Icc.preimage continuous_snd).inter
    (isClosed_le (continuous_fst.sub (hg.comp continuous_snd)).abs continuous_const)).measurableSet

theorem measurable_multiplicity {n : ℕ} (δ : ℝ) {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, Continuous (g i)) : Measurable (multiplicity δ g) := by
  exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator (measurableSet_strip δ (hg i)))

theorem multiplicity_eq_card {n : ℕ} (δ : ℝ) (g : Fin n → ℝ → ℝ) (p : ℝ × ℝ) :
    multiplicity δ g p = ((Finset.univ.filter (fun i => p ∈ strip δ (g i))).card : ℝ≥0∞) := by
  classical
  simp [multiplicity, Set.indicator_apply, Finset.sum_boole]

theorem multiplicity_le_card {n : ℕ} (δ : ℝ) (g : Fin n → ℝ → ℝ) (p : ℝ × ℝ) :
    multiplicity δ g p ≤ (n : ℝ≥0∞) := by
  classical
  rw [multiplicity_eq_card]
  have h := (Finset.card_filter_le (s := (Finset.univ : Finset (Fin n)))
    (p := fun i => p ∈ strip δ (g i)))
  simp only [Finset.card_univ, Fintype.card_fin] at h
  exact_mod_cast h

theorem multiplicity_zero_or_one_le {n : ℕ} (δ : ℝ) (g : Fin n → ℝ → ℝ)
    (p : ℝ × ℝ) : multiplicity δ g p = 0 ∨ 1 ≤ multiplicity δ g p := by
  classical
  rw [multiplicity_eq_card]
  by_cases h : (Finset.univ.filter (fun i => p ∈ strip δ (g i))).card = 0
  · simp [h]
  · right
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h)

end WangZahlLot.Obl.wz_parameter_weak_strong_reduction
