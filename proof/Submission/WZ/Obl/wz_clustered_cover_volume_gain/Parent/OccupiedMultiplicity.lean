-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.OccupiedMultiplicity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.NeighborhoodMultiplicity

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open scoped Classical

/-- A pointwise lower level and upper/lower mass estimates imply a numerical
level bound. The common normalizing factor need only be positive. -/
theorem uniform_level_bound {n : ℕ} (Y : Fin n → Set Space)
    (hY : ∀ i, MeasurableSet (Y i)) {A c C s : ℝ}
    (hA : 0 ≤ A) (hc : 0 < c) (hC : 0 ≤ C) (hs : 0 < s)
    (hmult : ∀ p ∈ ⋃ i, Y i, ENNReal.ofReal A ≤ multiplicity Y p)
    (hvol : ENNReal.ofReal (c * s) ≤ volume (⋃ i, Y i))
    (hmass : (∑ i, volume (Y i)) ≤ ENNReal.ofReal (C * s)) :
    A ≤ C / c := by
  have hh : ENNReal.ofReal (A * (c * s)) ≤ ENNReal.ofReal (C * s) := by
    rw [ENNReal.ofReal_mul hA]
    exact (mul_le_mul_right hvol _).trans ((multiplicity_mul_volume_le_mass hY hmult).trans hmass)
  have hr := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC hs.le)).mp hh
  apply (le_div_iff₀ hc).mpr
  apply (mul_le_mul_iff_left₀ hs).mp
  simpa only [mul_assoc] using hr

/-- Empty members contribute nothing to the total mass estimate. -/
theorem sum_measure_le_occupied_card {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (Y : ι → Set X) {v : ENNReal} (hv : ∀ i, μ (Y i) ≤ v) :
    (∑ i, μ (Y i)) ≤ ((Finset.univ.filter fun i => (Y i).Nonempty).card : ENNReal) * v := by
  classical
  calc
    _ ≤ ∑ i, if (Y i).Nonempty then v else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : (Y i).Nonempty
      · simpa only [ite_eq_left hi] using hv i
      · simp only [Set.not_nonempty_iff_eq_empty.mp hi, measure_empty, Set.not_nonempty_empty,
          ite_false, le_refl]
    _ = _ := by rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- The occupied-packet count cancels from the coarse level estimate. -/
theorem occupied_coarse_level_bound {b c A : ℝ} (hb : 0 < b)
    (hb3 : b ≤ 1 / 3) (hc : 0 < c) (hA : 0 ≤ A) {N : ℕ}
    (Q : Fin N → Set Space) (z : Fin N → Space) (e : Fin N → Space ≃ₗᵢ[ℝ] Space)
    (hsub : ∀ j, thickening b (Q j) ⊆ factoringCarrier b (z j) (e j))
    (hoccupied : ∃ j, (thickening b (Q j)).Nonempty)
    (hmult : ∀ p ∈ ⋃ j, Q j, ENNReal.ofReal A ≤ multiplicity Q p)
    (hvol : ENNReal.ofReal (c *
        ((Finset.univ.filter fun j => (thickening b (Q j)).Nonempty).card * b ^ 2)) ≤
      volume (⋃ j, thickening b (Q j))) :
    A ≤ 360 / c := by
  classical
  let P := Finset.univ.filter fun j => (thickening b (Q j)).Nonempty
  have hP : P.Nonempty := by
    obtain ⟨j, hj⟩ := hoccupied
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  have hs : 0 < (P.card : ℝ) * b ^ 2 := mul_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr hP))
    (sq_pos_of_pos hb)
  apply uniform_level_bound (fun j => thickening b (Q j))
    (fun _ => isOpen_thickening.measurableSet) hA hc (by norm_num) hs
    (thickening_multiplicity_lower hmult b) hvol
  have hh := sum_measure_le_occupied_card volume (fun j => thickening b (Q j))
    (fun j => (measure_mono (hsub j)).trans (factoringCarrier_volume_upper hb hb3 (z j) (e j)))
  convert hh using 1
  rw [← ENNReal.ofReal_natCast P.card, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  ring

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
