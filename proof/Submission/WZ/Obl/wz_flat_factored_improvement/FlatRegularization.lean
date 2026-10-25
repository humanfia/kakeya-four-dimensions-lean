-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.FlatRegularization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.PrismNeighborhood
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Selection

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement
  (gridCell gridUnion gridKeys gridKey gridKey_mem mem_gridCell_key
    gridCell_volume_ne_top gridCell_volumeReal volumeReal_inter_gridUnion
    gridUnion_volumeReal gridUnion_volume_ne_top gridUnion_measurable
    density_selection dense_index_subfamily)

theorem grid_density_selection {a ρ H V : ℝ} (ha : 0 < a) (hρ : 0 < ρ)
    {K : ℕ} (hK : 0 < K) (s₀ : Finset (Fin 3 → ℤ))
    {n : ℕ} (Y : Fin n → Set Space) (hYm : ∀ i, MeasurableSet (Y i))
    (hcover : ∀ i, Y i ⊆ gridUnion a s₀)
    (hcap : (s₀.card : ℝ) * a ^ 3 ≤ V)
    (hH : H ≤ ∑ i, volume.real (Y i))
    (hlow : (n : ℝ) * ρ ^ K * V ≤ H / 2) :
    ∃ (s : Finset (Fin 3 → ℤ)) (t : ℝ), s ⊆ s₀ ∧ 0 < t ∧
      H / (2 * K) ≤ ∑ i, volume.real (Y i ∩ gridUnion a s) ∧
      (∀ z ∈ s, t * a ^ 3 ≤ volume.real ((⋃ i, Y i) ∩ gridCell a z)) ∧
      ρ * volume.real ((⋃ i, Y i) ∩ gridUnion a s) ≤ t * V := by
  classical
  let S := ⋃ i, Y i
  let d := fun z => volume.real (S ∩ gridCell a z) / a ^ 3
  let w := fun z => ∑ i, volume.real (Y i ∩ gridCell a z)
  have hfin (z : Fin 3 → ℤ) : volume (S ∩ gridCell a z) ≠ ⊤ :=
    ne_top_of_le_ne_top (gridCell_volume_ne_top ha z) (measure_mono inter_subset_right)
  have hd (z : Fin 3 → ℤ) : d z ≤ 1 := by
    apply (div_le_one (pow_pos ha 3)).mpr
    exact (measureReal_mono inter_subset_right (gridCell_volume_ne_top ha z)).trans
      (gridCell_volumeReal ha z).le
  have hw (z : Fin 3 → ℤ) : w z ≤ (n : ℝ) * volume.real (S ∩ gridCell a z) := by
    calc
      _ ≤ ∑ _i : Fin n, volume.real (S ∩ gridCell a z) := by
        apply Finset.sum_le_sum
        intro i _
        exact measureReal_mono (inter_subset_inter_left _ (subset_iUnion Y i)) (hfin z)
      _ = _ := by simp
  have hmass : H ≤ ∑ z ∈ s₀, w z := by
    dsimp [w]
    rw [Finset.sum_comm]
    have he (i : Fin n) : (∑ z ∈ s₀, volume.real (Y i ∩ gridCell a z)) = volume.real (Y i) := by
      rw [← volumeReal_inter_gridUnion ha s₀ (hYm i), inter_eq_left.mpr (hcover i)]
    simpa only [he] using hH
  have hsmall : (∑ z ∈ s₀.filter (fun z => d z < ρ ^ K), w z) ≤ H / 2 := by
    calc
      _ ≤ ∑ _z ∈ s₀.filter (fun z => d z < ρ ^ K), (n : ℝ) * ρ ^ K * a ^ 3 := by
        apply Finset.sum_le_sum
        intro z hz
        have hz' := (div_lt_iff₀ (pow_pos ha 3)).mp (Finset.mem_filter.mp hz).2
        exact (hw z).trans (by nlinarith [mul_le_mul_of_nonneg_left hz'.le (Nat.cast_nonneg n)])
      _ ≤ ∑ _z ∈ s₀, (n : ℝ) * ρ ^ K * a ^ 3 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; positivity)
      _ = (n : ℝ) * ρ ^ K * ((s₀.card : ℝ) * a ^ 3) := by simp; ring
      _ ≤ (n : ℝ) * ρ ^ K * V := mul_le_mul_of_nonneg_left hcap (by positivity)
      _ ≤ _ := hlow
  obtain ⟨s, hs, hmass', t, ht, hclass⟩ := density_selection s₀ d w hρ hK
    (fun z _ => hd z) hmass hsmall
  have hloc (z : Fin 3 → ℤ) (hz : z ∈ s) :
      t * a ^ 3 ≤ volume.real (S ∩ gridCell a z) ∧
      ρ * volume.real (S ∩ gridCell a z) ≤ t * a ^ 3 := by
    refine ⟨(le_div_iff₀ (pow_pos ha 3)).mp (hclass z hz).1, ?_⟩
    apply (div_le_iff₀ (pow_pos ha 3)).mp
    simpa only [mul_div_assoc] using (hclass z hz).2
  refine ⟨s, t, hs, ht, ?_, fun z hz => (hloc z hz).1, ?_⟩
  · dsimp [w] at hmass'
    rw [Finset.sum_comm] at hmass'
    simpa only [← volumeReal_inter_gridUnion ha s (hYm _)] using hmass'
  · rw [volumeReal_inter_gridUnion ha s (MeasurableSet.iUnion hYm), Finset.mul_sum]
    calc
      _ ≤ ∑ _z ∈ s, t * a ^ 3 := Finset.sum_le_sum (fun z hz => (hloc z hz).2)
      _ = t * ((s.card : ℝ) * a ^ 3) := by simp; ring
      _ ≤ t * V := mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hs)) (by positivity)).trans hcap) ht.le

/-- A regular density class on cubes of the short prism scale. -/
theorem flat_prism_regularization {δ a b lam ρ : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a)
    (hab : a ≤ b) (hb2 : b ≤ 2) (ha1 : a ≤ 1) (hlam : 0 < lam) (hρ : 0 < ρ)
    {K : ℕ} (hK : 0 < K) (hcut : 432 * ρ ^ K * a * b ≤ lam * δ ^ 2 / 2)
    (e : AffineIsometryEquiv ℝ Space Space) {n : ℕ} (hn : 0 < n)
    (x v : Fin n → Space) (Y : Fin n → Set Space)
    (hv : ∀ i, ‖v i‖ = 1) (hYm : ∀ i, MeasurableSet (Y i))
    (hYT : ∀ i, Y i ⊆ Tube δ (x i) (v i)) (hYB : ∀ i, Y i ⊆ ball (0 : Space) 1)
    (hYW : ∀ i, Y i ⊆ e '' StandardPrism a b)
    (hden : ∀ i, ENNReal.ofReal (lam * δ ^ 2) ≤ volume (Y i)) :
    ∃ (s : Finset (Fin 3 → ℤ)) (t : ℝ) (N : ℕ) (j : Fin N → Fin n),
      s ⊆ gridKeys a ∧ (∀ z ∈ s, (e '' StandardPrism a b ∩ gridCell a z).Nonempty) ∧
      0 < t ∧ 0 < N ∧ Function.Injective j ∧ lam / (224 * K) * n ≤ N ∧
      (∀ i, ENNReal.ofReal (lam / (4 * K) * δ ^ 2) ≤ volume (Y (j i) ∩ gridUnion a s)) ∧
      (∀ z ∈ s, t * a ^ 3 ≤ volume.real ((⋃ i, Y i) ∩ gridCell a z)) ∧
      ρ * volume.real (⋃ i, Y (j i) ∩ gridUnion a s) ≤ t * (432 * a * b) := by
  classical
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  let s₀ := (gridKeys a).filter (fun z => (e '' StandardPrism a b ∩ gridCell a z).Nonempty)
  have hmeet : ∀ z ∈ s₀, (e '' StandardPrism a b ∩ gridCell a z).Nonempty :=
    fun z hz => (Finset.mem_filter.mp hz).2
  have hcover : ∀ i, Y i ⊆ gridUnion a s₀ := by
    intro i p hp
    refine mem_iUnion.mpr ⟨gridKey a p, mem_iUnion.mpr ⟨?_, mem_gridCell_key ha p⟩⟩
    exact Finset.mem_filter.mpr ⟨gridKey_mem ha ha1 (hYB i hp),
      ⟨p, hYW i hp, mem_gridCell_key ha p⟩⟩
  have hcap : (s₀.card : ℝ) * a ^ 3 ≤ 432 * a * b := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (gridUnion_flat_volume ha hab hb2 e s₀ hmeet)
    simpa only [← measureReal_def, gridUnion_volumeReal ha,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 432 * a * b)] using hh
  have hYfin (i : Fin n) : volume (Y i) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (hYB i))
  have hmass : lam * n * δ ^ 2 ≤ ∑ i, volume.real (Y i) := by
    calc
      _ = ∑ _i : Fin n, lam * δ ^ 2 := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ => (ENNReal.ofReal_le_iff_le_toReal (hYfin i)).mp (hden i))
  obtain ⟨s, t, hs, ht, hm, hloc, htotal⟩ := grid_density_selection ha hρ hK s₀ Y hYm hcover hcap hmass
    (by nlinarith [mul_le_mul_of_nonneg_left hcut hn'.le])
  let w := fun i => volume.real (Y i ∩ gridUnion a s)
  have hw : ∀ i, w i ≤ 56 * δ ^ 2 := by
    intro i
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((measure_mono ((show Y i ∩ gridUnion a s ⊆ Y i from inter_subset_left).trans (hYT i))).trans
        (WangZahlLot.Obl.wz_nonflat_factored_improvement.tube_volume_upper hδ.le (hδa.trans ha1) (x i) (v i) (hv i)))
    simpa only [w, measureReal_def, ENNReal.toReal_ofReal (by positivity : 0 ≤ 56 * δ ^ 2)] using hh
  obtain ⟨N, j, hN, hj, hNj, hind⟩ := dense_index_subfamily hn w
    (by positivity : 0 < lam / (4 * K) * δ ^ 2) (by positivity : 0 < 56 * δ ^ 2) hw
    (by convert hm using 1 <;> field_simp <;> ring)
  refine ⟨s, t, N, j, hs.trans (Finset.filter_subset _ _), fun z hz => hmeet z (hs hz),
    ht, hN, hj, ?_, ?_, hloc, ?_⟩
  · convert hNj using 1 <;> field_simp <;> ring
  · intro i
    exact (ENNReal.ofReal_le_iff_le_toReal
      (ne_top_of_le_ne_top (hYfin (j i)) (measure_mono inter_subset_left))).mpr (hind i)
  · apply le_trans (mul_le_mul_of_nonneg_left ?_ hρ.le) htotal
    exact measureReal_mono (iUnion_subset (fun i =>
      inter_subset_inter_left _ (subset_iUnion Y (j i))))
      (ne_top_of_le_ne_top (gridUnion_volume_ne_top ha s) (measure_mono inter_subset_right))

end WangZahlLot.Obl.wz_flat_factored_improvement
