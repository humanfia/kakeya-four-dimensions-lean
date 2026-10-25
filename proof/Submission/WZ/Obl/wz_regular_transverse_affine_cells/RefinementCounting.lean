-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.RefinementCounting.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.PrismRefinement

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open Module MeasureTheory Set
open scoped ENNReal

open Classical in
lemma sum_measure_le_nonempty_card {ι : Type*} (I : Finset ι) (Y : ι → Set E)
    {V : ℝ} (hV : 0 ≤ V) (hY : ∀ i ∈ I, volume (Y i) ≤ ENNReal.ofReal V) :
    ∑ i ∈ I, volume (Y i) ≤ ENNReal.ofReal (V * ((I.filter fun i => (Y i).Nonempty).card : ℝ)) := by
  classical
  have he : (∑ i ∈ I.filter (fun i => (Y i).Nonempty), volume (Y i)) = ∑ i ∈ I, volume (Y i) := by
    apply Finset.sum_filter_of_ne
    intro i hi h
    exact nonempty_of_measure_ne_zero h
  rw [← he]
  calc (∑ i ∈ I.filter (fun i => (Y i).Nonempty), volume (Y i))
      ≤ ∑ _i ∈ I.filter (fun i => (Y i).Nonempty), ENNReal.ofReal V :=
        Finset.sum_le_sum fun i hi => hY i (Finset.mem_filter.mp hi).1
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul hV, ENNReal.ofReal_natCast]; ring

open Classical in
lemma partition_measure_le_incidence_count {ι κ : Type*} (I : Finset ι) (F : Finset κ)
    (Y : ι → Set E) (B : κ → Set E) {V : ℝ} (hV : 0 ≤ V)
    (hY : ∀ i ∈ I, volume (Y i) ≤ ENNReal.ofReal V)
    (hcover : ∀ i ∈ I, Y i ⊆ ⋃ ℓ ∈ F, B ℓ) :
    ∑ i ∈ I, volume (Y i) ≤ ENNReal.ofReal
      (V * ∑ ℓ ∈ F, ((I.filter fun i => (Y i ∩ B ℓ).Nonempty).card : ℝ)) := by
  classical
  have he (i : ι) (hi : i ∈ I) : Y i = ⋃ ℓ ∈ F, Y i ∩ B ℓ := by
    rw [← inter_iUnion₂, inter_eq_left.mpr (hcover i hi)]
  calc (∑ i ∈ I, volume (Y i)) ≤ ∑ i ∈ I, ∑ ℓ ∈ F, volume (Y i ∩ B ℓ) := by
        apply Finset.sum_le_sum
        intro i hi
        nth_rw 1 [he i hi]
        exact measure_biUnion_finset_le F _
    _ = ∑ ℓ ∈ F, ∑ i ∈ I, volume (Y i ∩ B ℓ) := Finset.sum_comm
    _ ≤ ∑ ℓ ∈ F, ENNReal.ofReal (V * ((I.filter fun i => (Y i ∩ B ℓ).Nonempty).card : ℝ)) := by
      apply Finset.sum_le_sum
      intro ℓ _
      exact sum_measure_le_nonempty_card I _ hV
        (fun i hi => (measure_mono inter_subset_left).trans (hY i hi))
    _ = _ := by
      rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
      intro ℓ _
      positivity

open Classical in
/-- If the regular core has few indices, the narrow pieces necessarily carry many
incidences. This is the numerical dichotomy used by the physical recursion. -/
lemma PrismRefinement.count_dichotomy {ι : Type*} {I : Finset ι} {a b θ h : ℝ} {K : ℕ}
    {c : ι → E} {u : ι → OrthonormalBasis (Fin 3) ℝ E} {Y : ι → Set E}
    (R : PrismRefinement I a b θ h K c u Y)
    {d V : ℝ} (hd : 0 < d) (hV : 0 < V) (hh : 0 ≤ h) (hhd : 4 * h ≤ d)
    (hY : ∀ i ∈ I, volume (Y i) ≤ ENNReal.ofReal V)
    (hdense : ENNReal.ofReal (d * V * (I.card : ℝ)) ≤ ∑ i ∈ I, volume (Y i))
    (hcost : ENNReal.ofReal (1000000 * (K + 1 : ℕ) * h) *
      (∑ i ∈ I, volume (prism a b (c i) (u i))) ≤ ENNReal.ofReal (d * V * (I.card : ℝ) / 4)) :
    h * (I.card : ℝ) ≤ ((I.filter fun i => (R.core i).Nonempty).card : ℝ) ∨
    h * (I.card : ℝ) ≤ ∑ ℓ ∈ R.labels, ((I.filter fun i => (R.narrow i ∩ R.region ℓ).Nonempty).card : ℝ) := by
  classical
  by_cases hcore : h * (I.card : ℝ) ≤ ((I.filter fun i => (R.core i).Nonempty).card : ℝ)
  · exact Or.inl hcore
  right
  let Hcount : ℝ := ((I.filter fun i => (R.core i).Nonempty).card : ℝ)
  let Qcount : ℝ := ∑ ℓ ∈ R.labels, ((I.filter fun i => (R.narrow i ∩ R.region ℓ).Nonempty).card : ℝ)
  have hH := sum_measure_le_nonempty_card I R.core hV.le
    (fun i hi => (measure_mono (R.core_subset i hi)).trans (hY i hi))
  have hQ := partition_measure_le_incidence_count I R.labels R.narrow R.region hV.le
    (fun i hi => (measure_mono (R.narrow_subset i hi)).trans (hY i hi)) R.narrow_cover
  have hHnonneg : 0 ≤ Hcount := Nat.cast_nonneg _
  have hQnonneg : 0 ≤ Qcount := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hreal : d * V * (I.card : ℝ) ≤ V * Hcount + V * Qcount + d * V * (I.card : ℝ) / 4 := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    have hVH := mul_nonneg hV.le hHnonneg
    have hVQ := mul_nonneg hV.le hQnonneg
    rw [ENNReal.ofReal_add (add_nonneg hVH hVQ) (by positivity), ENNReal.ofReal_add hVH hVQ]
    exact hdense.trans (R.mass.trans (add_le_add (add_le_add hH hQ) hcost))
  have hcore' : Hcount ≤ h * (I.card : ℝ) := le_of_not_ge hcore
  have hfour : 4 * (h * (I.card : ℝ)) ≤ d * (I.card : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right hhd (Nat.cast_nonneg I.card)]
  have hbound : V * (h * (I.card : ℝ)) ≤ V * Qcount := by
    nlinarith [mul_le_mul_of_nonneg_left hcore' hV.le,
      mul_le_mul_of_nonneg_left hfour hV.le]
  exact (mul_le_mul_iff_right₀ hV).mp hbound

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
