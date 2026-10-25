-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_transverse_pair_moment.Measure.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_jet_transverse_pair_moment

open MeasureTheory

/-- The vertical strip used in the frozen statement. -/
def strip (δ : ℝ) (g : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ∈ Set.Icc (-1 : ℝ) 1 ∧ |p.1 - g p.2| ≤ δ}

theorem measurableSet_strip {δ : ℝ} {g : ℝ → ℝ} (hg : Continuous g) :
    MeasurableSet (strip δ g) :=
  (measurableSet_Icc.preimage continuous_snd.measurable).inter
    (isClosed_le ((continuous_fst.sub (hg.comp continuous_snd)).abs)
      continuous_const).measurableSet

theorem strip_fiber {δ : ℝ} {g : ℝ → ℝ} {z : ℝ}
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    (fun x : ℝ => (x, z)) ⁻¹' strip δ g = Set.Icc (g z - δ) (g z + δ) := by
  ext x
  change (z ∈ Set.Icc (-1 : ℝ) 1 ∧ |x - g z| ≤ δ) ↔ _
  rw [and_iff_right hz, abs_le]
  change (-δ ≤ x - g z ∧ x - g z ≤ δ) ↔ (g z - δ ≤ x ∧ x ≤ g z + δ)
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

end WangZahlLot.Obl.wz_jet_transverse_pair_moment
