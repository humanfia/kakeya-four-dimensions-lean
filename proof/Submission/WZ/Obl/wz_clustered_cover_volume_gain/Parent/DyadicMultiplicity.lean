-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.DyadicMultiplicity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.DyadicPower
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.Multiplicity

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set
open scoped Classical

/-- A common dyadic multiplicity level, expressed in the indicator-sum API. -/
theorem dyadic_refinement_multiplicity {D ν : ℝ} (hD : 0 < D) (hν : 0 < ν) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      ∀ (n : ℕ), (n : ℝ) ≤ δ ^ (-D) → ∀ Y : Fin n → Set Space,
      (∀ i, MeasurableSet (Y i)) →
      ∃ (M : ℝ) (Z : Fin n → Set Space), 0 < M ∧
        (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
        ENNReal.ofReal (δ ^ ν) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) ∧
        (∀ p ∈ ⋃ i, Z i, ENNReal.ofReal M ≤ multiplicity Z p) ∧
        (∀ p, multiplicity Z p ≤ ENNReal.ofReal (2 * M)) := by
  obtain ⟨d, hd, hrefine⟩ := dyadic_shading_refinement_power hD hν
  refine ⟨d, hd, ?_⟩
  intro δ hδ hδd n hn Y hY
  obtain ⟨k, Z, hZ, hmass, hlevel⟩ := hrefine δ hδ hδd n hn Y hY
  have hcount (p : Space) : multiplicity Z p =
      ENNReal.ofReal ((Finset.univ.filter fun i => p ∈ Z i).card : ℝ) := by
    rw [multiplicity_eq_ncard, ENNReal.ofReal_natCast]
    congr 1
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp
  refine ⟨((2 ^ k : ℕ) : ℝ), Z, by positivity, hZ, hmass, ?_, ?_⟩
  · intro p hp
    rw [hcount]
    apply ENNReal.ofReal_le_ofReal
    exact_mod_cast (hlevel p hp).1
  · intro p
    by_cases hp : p ∈ ⋃ i, Z i
    · rw [hcount]
      apply ENNReal.ofReal_le_ofReal
      have hh := (hlevel p hp).2.le
      rw [pow_succ, mul_comm] at hh
      exact_mod_cast hh
    · have hoff : ∀ i, p ∉ Z i := fun i hi => hp (Set.mem_iUnion.mpr ⟨i, hi⟩)
      simp [multiplicity, Set.indicator, hoff]

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
