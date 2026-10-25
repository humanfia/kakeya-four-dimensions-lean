-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.PrismRegularization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CellRegularization

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set Metric

/-- Regularization supplies dense coarse cells and an individually dense fine subfamily. -/
theorem prism_shading_regularization {a b δ lam ρ : ℝ}
    (hδ : 0 < δ) (hδb : δ ≤ b) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hlam : 0 < lam) (hρ : 0 < ρ) {K : ℕ} (hK : 0 < K)
    (hcut : 288 * ρ ^ K * b ^ 2 ≤ lam * δ ^ 2 / 2)
    (e : AffineIsometryEquiv ℝ Space Space) {n : ℕ} (hn : 0 < n)
    (x v : Fin n → Space) (Y : Fin n → Set Space)
    (hv : ∀ i, ‖v i‖ = 1) (hYm : ∀ i, MeasurableSet (Y i))
    (hYT : ∀ i, Y i ⊆ tube δ (x i) (v i)) (hYB : ∀ i, Y i ⊆ unitBall)
    (hYW : ∀ i, Y i ⊆ e '' standardPrism a b)
    (hden : ∀ i, ENNReal.ofReal (lam * δ ^ 2) ≤ volume (Y i)) :
    ∃ (s : Finset (Fin 3 → ℤ)) (t : ℝ) (N : ℕ) (j : Fin N → Fin n),
      s ⊆ gridKeys b ∧ (∀ z ∈ s, (e '' standardPrism a b ∩ gridCell b z).Nonempty) ∧
      0 < t ∧ 0 < N ∧ Function.Injective j ∧ lam / (224 * K) * n ≤ N ∧
      (∀ i, ENNReal.ofReal (lam / (4 * K) * δ ^ 2) ≤
        volume (Y (j i) ∩ gridUnion b s)) ∧
      ENNReal.ofReal (lam / (32 * K) * b ^ 2) ≤ volume (gridUnion b s) ∧
      (∀ z ∈ s, t * b ^ 3 ≤ volume.real ((⋃ i, Y i) ∩ gridCell b z)) ∧
      ρ * volume.real (⋃ i, Y (j i) ∩ gridUnion b s) ≤ t * (288 * b ^ 2) := by
  classical
  have hb : 0 < b := hδ.trans_le hδb
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hK' : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
  have hYfin (i : Fin n) : volume (Y i) ≠ ⊤ :=
    ne_top_of_le_ne_top (ne_of_lt measure_ball_lt_top) (measure_mono (hYB i))
  have hH : lam * n * δ ^ 2 ≤ ∑ i, volume.real (Y i) := by
    have hi (i : Fin n) : lam * δ ^ 2 ≤ volume.real (Y i) :=
      (ENNReal.ofReal_le_iff_le_toReal (hYfin i)).mp (hden i)
    calc
      _ = ∑ _i : Fin n, lam * δ ^ 2 := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hi i)
  have hlo : (n : ℝ) * ρ ^ K * (288 * b ^ 2) ≤ (lam * n * δ ^ 2) / 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hcut hn'.le]
  obtain ⟨s, t, hs, hmeet, ht, hmass, hlocal, htotal⟩ :=
    prism_cell_selection hb hab hb1 hρ hK e Y hYm hYB hYW hH hlo
  let f : Fin n → ℝ := fun i => volume.real (Y i ∩ gridUnion b s)
  let τ := lam / (4 * K) * δ ^ 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hRfin (i : Fin n) : volume (Y i ∩ gridUnion b s) ≠ ⊤ :=
    ne_top_of_le_ne_top (hYfin i) (measure_mono inter_subset_left)
  have hf (i : Fin n) : f i ≤ 56 * δ ^ 2 := by
    have hsub : Y i ∩ gridUnion b s ⊆ tube δ (x i) (v i) := inter_subset_left.trans (hYT i)
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((measure_mono hsub).trans
        (tube_volume_upper hδ.le (hδb.trans hb1) (x i) (v i) (hv i)))
    simpa only [f, measureReal_def, ENNReal.toReal_ofReal (by positivity : 0 ≤ 56 * δ ^ 2)] using hh
  have hmass' : 2 * n * τ ≤ ∑ i, f i := by
    convert hmass using 1
    dsimp [τ]
    field_simp
    ring
  obtain ⟨N, j, hN, hj, hsize, hInd⟩ := dense_index_subfamily hn f hτ
    (by positivity : 0 < 56 * δ ^ 2) hf hmass'
  have hcard : lam / (224 * K) * n ≤ N := by
    convert hsize using 1
    dsimp [τ]
    field_simp
    ring
  have hcMass : lam / (32 * K) * b ^ 2 ≤ volume.real (gridUnion b s) := by
    have hsum : (∑ i, f i) ≤ (n : ℝ) * (16 * δ ^ 2 / b ^ 2) *
        volume.real (gridUnion b s) := by
      calc
        _ ≤ ∑ _i : Fin n, 16 * δ ^ 2 / b ^ 2 * volume.real (gridUnion b s) := by
          apply Finset.sum_le_sum
          intro i _
          exact (measureReal_mono (Set.inter_subset_inter_left _ (hYT i))
            (ne_top_of_le_ne_top (gridUnion_volume_ne_top hb s)
              (measure_mono inter_subset_right))).trans
                (tube_gridUnion_volumeReal hb δ (x i) (v i) (hv i) s)
        _ = _ := by simp; ring
    have he : lam * n * δ ^ 2 / (2 * K) =
        ((n : ℝ) * (16 * δ ^ 2 / b ^ 2)) * (lam / (32 * K) * b ^ 2) := by
      field_simp
      ring
    rw [he] at hmass
    exact (mul_le_mul_iff_right₀ (by positivity : 0 < (n : ℝ) * (16 * δ ^ 2 / b ^ 2))).mp
      (hmass.trans hsum)
  refine ⟨s, t, N, j, hs, hmeet, ht, hN, hj, hcard, ?_, ?_, hlocal, ?_⟩
  · intro i
    exact (ENNReal.ofReal_le_iff_le_toReal (hRfin (j i))).mpr (hInd i)
  · exact (ENNReal.ofReal_le_iff_le_toReal (gridUnion_volume_ne_top hb s)).mpr hcMass
  · apply le_trans (mul_le_mul_of_nonneg_left ?_ hρ.le) htotal
    exact measureReal_mono (Set.iUnion_subset (fun i =>
      Set.inter_subset_inter_left _ (Set.subset_iUnion Y (j i))))
      (ne_top_of_le_ne_top (gridUnion_volume_ne_top hb s) (measure_mono inter_subset_right))

end WangZahlLot.Obl.wz_nonflat_factored_improvement
