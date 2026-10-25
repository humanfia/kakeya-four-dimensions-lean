-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_scales_gain.CellSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CellRegularization

namespace WangZahlLot.Obl.wz_separated_scales_gain

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement

/-- Density selection in any finite collection of grid cells. The collection need not
be centered at the origin, which lets the same grid serve every level of a tube cover. -/
theorem bounded_cell_selection {b θ H V : ℝ} (hb : 0 < b) (hθ : 0 < θ)
    {K : ℕ} (hK : 0 < K) (s₀ : Finset (Fin 3 → ℤ))
    {n : ℕ} (Y : Fin n → Set Space) (hYm : ∀ i, MeasurableSet (Y i))
    (hcover : ∀ i, Y i ⊆ gridUnion b s₀)
    (hvolume : volume.real (gridUnion b s₀) ≤ V)
    (hmass : H ≤ ∑ i, volume.real (Y i))
    (hcut : (n : ℝ) * θ ^ K * V ≤ H / 2) :
    ∃ (s : Finset (Fin 3 → ℤ)) (t : ℝ), s ⊆ s₀ ∧ 0 < t ∧
      H / (2 * K) ≤ ∑ i, volume.real (Y i ∩ gridUnion b s) ∧
      (∀ z ∈ s, t * b ^ 3 ≤ volume.real ((⋃ i, Y i) ∩ gridCell b z)) ∧
      θ * volume.real ((⋃ i, Y i) ∩ gridUnion b s) ≤ t * V := by
  classical
  let S := ⋃ i, Y i
  let d := fun z => volume.real (S ∩ gridCell b z) / b ^ 3
  let w := fun z => ∑ i, volume.real (Y i ∩ gridCell b z)
  have hS : MeasurableSet S := MeasurableSet.iUnion hYm
  have hfin (z : Fin 3 → ℤ) : volume (S ∩ gridCell b z) ≠ ⊤ :=
    ne_top_of_le_ne_top (gridCell_volume_ne_top hb z) (measure_mono inter_subset_right)
  have hd (z : Fin 3 → ℤ) : d z ≤ 1 := by
    apply (div_le_one (pow_pos hb 3)).mpr
    exact (measureReal_mono inter_subset_right (gridCell_volume_ne_top hb z)).trans
      (gridCell_volumeReal hb z).le
  have hsum : H ≤ ∑ z ∈ s₀, w z := by
    dsimp [w]
    rw [Finset.sum_comm]
    have he (i : Fin n) : (∑ z ∈ s₀, volume.real (Y i ∩ gridCell b z)) = volume.real (Y i) := by
      rw [← volumeReal_inter_gridUnion hb s₀ (hYm i), inter_eq_left.mpr (hcover i)]
    simpa only [he] using hmass
  have hweight (z : Fin 3 → ℤ) : w z ≤ n * volume.real (S ∩ gridCell b z) := by
    calc
      _ ≤ ∑ _i : Fin n, volume.real (S ∩ gridCell b z) := Finset.sum_le_sum fun i _ =>
        measureReal_mono (inter_subset_inter_left _ (subset_iUnion Y i)) (hfin z)
      _ = _ := by simp
  have hsubvolume {s : Finset (Fin 3 → ℤ)} (hs : s ⊆ s₀) :
      (s.card : ℝ) * b ^ 3 ≤ V := by
    have hc : (s.card : ℝ) ≤ s₀.card := Nat.cast_le.mpr (Finset.card_le_card hs)
    have he : volume.real (gridUnion b s₀) = s₀.card * b ^ 3 := by
      rw [measureReal_def, gridUnion_volume hb, ENNReal.toReal_ofReal (by positivity)]
    rw [he] at hvolume
    exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans hvolume
  have hlow : (∑ z ∈ s₀.filter (fun z => d z < θ ^ K), w z) ≤ H / 2 := by
    let bad := s₀.filter (fun z => d z < θ ^ K)
    calc
      _ ≤ ∑ _z ∈ bad, (n : ℝ) * (θ ^ K * b ^ 3) := by
        apply Finset.sum_le_sum
        intro z hz
        have hh : volume.real (S ∩ gridCell b z) ≤ θ ^ K * b ^ 3 :=
          ((div_lt_iff₀ (pow_pos hb 3)).mp (Finset.mem_filter.mp hz).2).le
        exact (hweight z).trans (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg n))
      _ = (n : ℝ) * θ ^ K * (bad.card * b ^ 3) := by simp; ring
      _ ≤ (n : ℝ) * θ ^ K * V :=
        mul_le_mul_of_nonneg_left (hsubvolume (Finset.filter_subset _ _)) (by positivity)
      _ ≤ _ := hcut
  obtain ⟨s, hss, hretain, t, ht, hbin⟩ :=
    density_selection s₀ d w hθ hK (fun z _ => hd z) hsum hlow
  have hlocal (z : Fin 3 → ℤ) (hz : z ∈ s) :
      t * b ^ 3 ≤ volume.real (S ∩ gridCell b z) ∧
      θ * volume.real (S ∩ gridCell b z) ≤ t * b ^ 3 := by
    refine ⟨(le_div_iff₀ (pow_pos hb 3)).mp (hbin z hz).1, ?_⟩
    apply (div_le_iff₀ (pow_pos hb 3)).mp
    simpa only [mul_div_assoc] using (hbin z hz).2
  refine ⟨s, t, hss, ht, ?_, fun z hz => (hlocal z hz).1, ?_⟩
  · calc
      _ ≤ ∑ z ∈ s, w z := hretain
      _ = ∑ i, ∑ z ∈ s, volume.real (Y i ∩ gridCell b z) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun i _ => (volumeReal_inter_gridUnion hb s (hYm i)).symm
  · rw [volumeReal_inter_gridUnion hb s hS, Finset.mul_sum]
    calc
      _ ≤ ∑ _z ∈ s, t * b ^ 3 := Finset.sum_le_sum fun z hz => (hlocal z hz).2
      _ = t * (s.card * b ^ 3) := by simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsubvolume hss) ht.le

end WangZahlLot.Obl.wz_separated_scales_gain
