-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_finite_shading_second_moment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_transverse_brush_selection.Moments
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_finite_shading_second_moment`

A finite family of measurable shadings with a lower volume bound and an upper
overlap-row bound satisfies a second-moment lower bound for its containing set.
The indicator and Cauchy–Schwarz lemmas come from accepted obligation o021.
-/

namespace WangZahlLot.Obl.wz_finite_shading_second_moment

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_transverse_brush_selection
open scoped ENNReal

/-- The second moment of a finite multiplicity function is the sum of all overlaps. -/
theorem integral_multiplicity_square {ι : Type*} (Z : ι → Set Space) (F : Finset ι)
    (hZ : ∀ i ∈ F, MeasurableSet (Z i)) (hfin : ∀ i ∈ F, volume (Z i) ≠ ⊤) :
    (∫ p, multiplicity Z F p ^ 2) =
      ∑ i ∈ F, ∑ j ∈ F, (volume (Z i ∩ Z j)).toReal := by
  classical
  have hpair : ∀ i ∈ F, ∀ j ∈ F, Integrable (oneOn (Z i ∩ Z j)) := by
    intro i hi j hj
    exact integrable_oneOn ((hZ i hi).inter (hZ j hj))
      (ne_top_of_le_ne_top (hfin i hi) (measure_mono inter_subset_left))
  have heq : (fun p => multiplicity Z F p ^ 2) =
      (fun p => ∑ i ∈ F, ∑ j ∈ F, oneOn (Z i ∩ Z j) p) := by
    funext p
    simp only [WangZahlLot.Obl.wz_transverse_brush_selection.multiplicity, pow_two, Finset.sum_mul, Finset.mul_sum, oneOn_mul]
    rw [Finset.sum_comm]
  rw [heq, integral_finsetSum F
    (fun i hi => integrable_finsetSum F (fun j hj => hpair i hi j hj))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum F (fun j hj => hpair i hi j hj)]
  exact Finset.sum_congr rfl (fun j hj => integral_oneOn ((hZ i hi).inter (hZ j hj)))

end WangZahlLot.Obl.wz_finite_shading_second_moment

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_transverse_brush_selection
open WangZahlLot.Obl.wz_finite_shading_second_moment
open scoped ENNReal

theorem WangZahlLot.wz_finite_shading_second_moment : ∀ (n : ℕ) (F : Finset (Fin n)) (Z : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) (E : Set LeanEval.Analysis.WangZahlKakeya.Space) (u A : ℝ), MeasurableSet E → MeasureTheory.volume E ≠ ⊤ → (∀ i : Fin n, i ∈ F → MeasurableSet (Z i)) → (∀ i : Fin n, i ∈ F → Z i ⊆ E) → 0 ≤ u → 0 < A → (∀ i : Fin n, i ∈ F → u ≤ (MeasureTheory.volume (Z i)).toReal) → (∀ i : Fin n, i ∈ F → Finset.sum F (fun j : Fin n => (MeasureTheory.volume (Z i ∩ Z j)).toReal) ≤ A) → u ^ 2 * (F.card : ℝ) ≤ A * (MeasureTheory.volume E).toReal := by
  classical
  intro n F Z E u A hE hfin hZ hsub hu hA hlu hrow
  by_cases hF : F = ∅
  · simp only [hF, Finset.card_empty, Nat.cast_zero, mul_zero]
    exact mul_nonneg hA.le ENNReal.toReal_nonneg
  by_cases hu0 : u = 0
  · simp only [hu0, zero_pow (by decide : 2 ≠ 0), zero_mul]
    exact mul_nonneg hA.le ENNReal.toReal_nonneg
  have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  have hFpos : 0 < (F.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hF)
  have hZfin : ∀ i ∈ F, volume (Z i) ≠ ⊤ := fun i hi =>
    ne_top_of_le_ne_top hfin (measure_mono (hsub i hi))
  have hq : 0 < (volume E).toReal := by
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hF
    exact hupos.trans_le ((hlu i hi).trans
      (ENNReal.toReal_mono hfin (measure_mono (hsub i hi))))
  have hsupp : ∀ p, p ∉ E → multiplicity Z F p = 0 := by
    intro p hp
    apply Finset.sum_eq_zero
    intro i hi
    exact oneOn_of_notMem (fun hpi => hp (hsub i hi hpi))
  have hcs := integral_sq_bound hE hfin hq
    (integrable_multiplicity Z F hZ hZfin)
    (integrable_multiplicity_sq Z F hZ hZfin) hsupp
  rw [integral_multiplicity Z F hZ hZfin,
    integral_multiplicity_square Z F hZ hZfin] at hcs
  have hmass : u * (F.card : ℝ) ≤ ∑ i ∈ F, (volume (Z i)).toReal := by
    simpa [mul_comm] using Finset.sum_le_sum hlu
  have henergy : (∑ i ∈ F, ∑ j ∈ F, (volume (Z i ∩ Z j)).toReal) ≤
      A * (F.card : ℝ) := by
    simpa [mul_comm] using Finset.sum_le_sum hrow
  have hmass_sq : (u * (F.card : ℝ)) ^ 2 ≤
      (∑ i ∈ F, (volume (Z i)).toReal) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hu hFpos.le) hmass 2
  have htotal := hmass_sq.trans (hcs.trans
    (mul_le_mul_of_nonneg_left henergy hq.le))
  apply (mul_le_mul_iff_left₀ hFpos).mp
  nlinarith only [htotal]
