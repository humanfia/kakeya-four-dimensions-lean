-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.UniformVolumeRetention.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.LocalMultiplicity

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- Comparable multiplicity converts mass retention to union-volume retention,
without assuming the retained shading has a lower multiplicity bound. -/
theorem uniform_volume_retention {n : ℕ} {Y Z : Fin n → Set Space}
    (hY : ∀ i, MeasurableSet (Y i)) (hZ : ∀ i, MeasurableSet (Z i))
    {M C D : ENNReal} (hM0 : M ≠ 0) (hMtop : M ≠ ⊤)
    (hlower : ∀ p ∈ ⋃ i, Y i, M ≤ multiplicity Y p)
    (hupper : ∀ p, multiplicity Z p ≤ C * M)
    (hmass : (∑ i, volume (Y i)) ≤ D * ∑ i, volume (Z i)) :
    volume (⋃ i, Y i) ≤ (D * C) * volume (⋃ i, Z i) := by
  apply (ENNReal.mul_le_mul_iff_right hM0 hMtop).mp
  calc
    M * volume (⋃ i, Y i) ≤ ∑ i, volume (Y i) :=
      multiplicity_mul_volume_le_mass hY hlower
    _ ≤ D * ∑ i, volume (Z i) := hmass
    _ ≤ D * ((C * M) * volume (⋃ i, Z i)) :=
      mul_le_mul_right (mass_le_multiplicity_mul_volume hZ hupper) D
    _ = M * ((D * C) * volume (⋃ i, Z i)) := by ac_rfl

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
