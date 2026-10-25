-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.UniformMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Types

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open MeasureTheory Set
open scoped ENNReal

lemma ofReal_mul_card_sum {ι : Type*} (I : Finset ι) {c : ℝ} (hc : 0 ≤ c) :
    ENNReal.ofReal (c * (I.card : ℝ)) = ∑ _i ∈ I, ENNReal.ofReal c := by
  rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul hc, ENNReal.ofReal_natCast]
  ring

lemma sum_le_uniform_mass {ι : Type*} (I : Finset ι) (f : ι → ℝ≥0∞)
    {c : ℝ} (hc : 0 ≤ c) (hf : ∀ i ∈ I, f i ≤ ENNReal.ofReal c) :
    ∑ i ∈ I, f i ≤ ENNReal.ofReal (c * (I.card : ℝ)) := by
  rw [ofReal_mul_card_sum I hc]
  exact Finset.sum_le_sum hf

lemma uniform_mass_le_sum {ι : Type*} (I : Finset ι) (f : ι → ℝ≥0∞)
    {c : ℝ} (hc : 0 ≤ c) (hf : ∀ i ∈ I, ENNReal.ofReal c ≤ f i) :
    ENNReal.ofReal (c * (I.card : ℝ)) ≤ ∑ i ∈ I, f i := by
  rw [ofReal_mul_card_sum I hc]
  exact Finset.sum_le_sum hf

lemma volume_bounds_of_toReal {U : Set E} (hfin : volume U ≠ ∞) {a b : ℝ}
    (ha : a ≤ (volume U).toReal) (hb : (volume U).toReal ≤ b) :
    ENNReal.ofReal a ≤ volume U ∧ volume U ≤ ENNReal.ofReal b := by
  rw [← ENNReal.ofReal_toReal hfin]
  exact ⟨ENNReal.ofReal_le_ofReal ha, ENNReal.ofReal_le_ofReal hb⟩

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
