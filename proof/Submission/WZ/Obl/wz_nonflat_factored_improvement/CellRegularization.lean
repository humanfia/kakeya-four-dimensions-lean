-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.CellRegularization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.GridUnion
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Selection

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set Metric

/-- A common density class retains a fixed fraction of all shading mass in one prism. -/
theorem prism_cell_selection {a b ρ H : ℝ} (hb : 0 < b) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hρ : 0 < ρ) {K : ℕ} (hK : 0 < K)
    (e : AffineIsometryEquiv ℝ Space Space) {n : ℕ} (Y : Fin n → Set Space)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYB : ∀ i, Y i ⊆ unitBall)
    (hYW : ∀ i, Y i ⊆ e '' standardPrism a b)
    (hH : H ≤ ∑ i, volume.real (Y i))
    (hlow : (n : ℝ) * ρ ^ K * (288 * b ^ 2) ≤ H / 2) :
    ∃ (s : Finset (Fin 3 → ℤ)) (t : ℝ),
      s ⊆ gridKeys b ∧ (∀ z ∈ s, (e '' standardPrism a b ∩ gridCell b z).Nonempty) ∧
      0 < t ∧ H / (2 * K) ≤ ∑ i, volume.real (Y i ∩ gridUnion b s) ∧
      (∀ z ∈ s, t * b ^ 3 ≤ volume.real ((⋃ i, Y i) ∩ gridCell b z)) ∧
      ρ * volume.real ((⋃ i, Y i) ∩ gridUnion b s) ≤ t * (288 * b ^ 2) := by
  classical
  let S := ⋃ i, Y i
  have hSm : MeasurableSet S := MeasurableSet.iUnion hYm
  let s₀ := (gridKeys b).filter (fun z => (e '' standardPrism a b ∩ gridCell b z).Nonempty)
  have hs₀ : ∀ z ∈ s₀, (e '' standardPrism a b ∩ gridCell b z).Nonempty := by
    intro z hz
    exact (Finset.mem_filter.mp hz).2
  have hcover (i : Fin n) : Y i ⊆ gridUnion b s₀ := by
    intro p hp
    refine Set.mem_iUnion.mpr ⟨gridKey b p, Set.mem_iUnion.mpr ⟨?_, mem_gridCell_key hb p⟩⟩
    exact Finset.mem_filter.mpr ⟨gridKey_mem hb hb1 (hYB i hp),
      ⟨p, hYW i hp, mem_gridCell_key hb p⟩⟩
  have hvol₀ : (s₀.card : ℝ) * b ^ 3 ≤ 288 * b ^ 2 := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (gridUnion_prism_volume hb hab hb1 s₀ e hs₀)
    simpa only [gridUnion_volume hb, ENNReal.toReal_ofReal (by positivity : 0 ≤ s₀.card * b ^ 3),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 288 * b ^ 2)] using hh
  let d := fun z => volume.real (S ∩ gridCell b z) / b ^ 3
  let w := fun z => ∑ i, volume.real (Y i ∩ gridCell b z)
  have hdn (z : Fin 3 → ℤ) : volume (S ∩ gridCell b z) ≠ ⊤ :=
    ne_top_of_le_ne_top (gridCell_volume_ne_top hb z) (measure_mono inter_subset_right)
  have hd (z : Fin 3 → ℤ) : d z ≤ 1 := by
    apply (div_le_one (pow_pos hb 3)).mpr
    exact (measureReal_mono inter_subset_right (gridCell_volume_ne_top hb z)).trans
      (gridCell_volumeReal hb z).le
  have hmass : H ≤ ∑ z ∈ s₀, w z := by
    dsimp [w]
    rw [Finset.sum_comm]
    have he (i : Fin n) : (∑ z ∈ s₀, volume.real (Y i ∩ gridCell b z)) =
        volume.real (Y i) := by
      rw [← volumeReal_inter_gridUnion hb s₀ (hYm i), Set.inter_eq_left.mpr (hcover i)]
    simpa only [he] using hH
  have hw (z : Fin 3 → ℤ) : w z ≤ (n : ℝ) * volume.real (S ∩ gridCell b z) := by
    calc
      _ ≤ ∑ _i : Fin n, volume.real (S ∩ gridCell b z) := Finset.sum_le_sum (fun i _ =>
        measureReal_mono (Set.inter_subset_inter_left _ (Set.subset_iUnion Y i)) (hdn z))
      _ = _ := by simp
  have hlo : (∑ z ∈ s₀.filter (fun z => d z < ρ ^ K), w z) ≤ H / 2 := by
    let l := s₀.filter (fun z => d z < ρ ^ K)
    have hlcard : (l.card : ℝ) * b ^ 3 ≤ 288 * b ^ 2 := by
      have hc : (l.card : ℝ) ≤ s₀.card := Nat.cast_le.mpr
        (Finset.card_le_card (Finset.filter_subset _ _))
      exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans hvol₀
    calc
      _ ≤ ∑ _z ∈ l, (n : ℝ) * (ρ ^ K * b ^ 3) := by
        apply Finset.sum_le_sum
        intro z hz
        have hdz : volume.real (S ∩ gridCell b z) ≤ ρ ^ K * b ^ 3 :=
          ((div_lt_iff₀ (pow_pos hb 3)).mp (Finset.mem_filter.mp hz).2).le
        exact (hw z).trans (mul_le_mul_of_nonneg_left hdz (Nat.cast_nonneg n))
      _ = (n : ℝ) * ρ ^ K * (l.card * b ^ 3) := by simp; ring
      _ ≤ (n : ℝ) * ρ ^ K * (288 * b ^ 2) := by gcongr
      _ ≤ H / 2 := hlow
  obtain ⟨s, hss, hsmas, t, ht, hdt⟩ := density_selection s₀ d w hρ hK
    (fun z _ => hd z) hmass hlo
  have hmeet : ∀ z ∈ s, (e '' standardPrism a b ∩ gridCell b z).Nonempty :=
    fun z hz => hs₀ z (hss hz)
  have hscard : (s.card : ℝ) * b ^ 3 ≤ 288 * b ^ 2 := by
    exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hss))
      (by positivity)).trans hvol₀
  have hlocal (z : Fin 3 → ℤ) (hz : z ∈ s) :
      t * b ^ 3 ≤ volume.real (S ∩ gridCell b z) ∧
      ρ * volume.real (S ∩ gridCell b z) ≤ t * b ^ 3 := by
    refine ⟨(le_div_iff₀ (pow_pos hb 3)).mp (hdt z hz).1, ?_⟩
    apply (div_le_iff₀ (pow_pos hb 3)).mp
    simpa only [mul_div_assoc] using (hdt z hz).2
  refine ⟨s, t, hss.trans (Finset.filter_subset _ _), hmeet, ht, ?_,
    fun z hz => (hlocal z hz).1, ?_⟩
  · calc
      _ ≤ ∑ z ∈ s, w z := hsmas
      _ = ∑ i, ∑ z ∈ s, volume.real (Y i ∩ gridCell b z) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl (fun i _ => (volumeReal_inter_gridUnion hb s (hYm i)).symm)
  · rw [volumeReal_inter_gridUnion hb s hSm, Finset.mul_sum]
    calc
      _ ≤ ∑ _z ∈ s, t * b ^ 3 := Finset.sum_le_sum (fun z hz => (hlocal z hz).2)
      _ = t * (s.card * b ^ 3) := by simp; ring
      _ ≤ t * (288 * b ^ 2) := mul_le_mul_of_nonneg_left hscard ht.le

end WangZahlLot.Obl.wz_nonflat_factored_improvement
