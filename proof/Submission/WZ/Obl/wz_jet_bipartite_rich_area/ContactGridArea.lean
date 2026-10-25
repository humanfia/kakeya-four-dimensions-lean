-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.ContactGridArea.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactGridCover

noncomputable section

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set MeasureTheory

/-- A short time window costs its length in the first-moment estimate. -/
theorem volume_interval_strip_union_le {ι : Type*} (A : Finset ι)
    {g : ι → ℝ → ℝ} (hg : ∀ i ∈ A, Continuous (g i))
    {δ a b : ℝ} (hδ : 0 ≤ δ) {E : Set (ℝ × ℝ)}
    (hE : ∀ p ∈ E, p.2 ∈ Icc a b ∧ ∃ i ∈ A, |p.1 - g i p.2| ≤ δ) :
    volume E ≤ ENNReal.ofReal (2 * δ * (b - a) * A.card) := by
  have hsub : E ⊆ ⋃ i ∈ A, shearRect (g i) ((a + b) / 2) ((b - a) / 2) 0 0 δ := by
    intro p hp
    obtain ⟨ht, i, hi, hv⟩ := hE p hp
    apply mem_iUnion₂.mpr
    refine ⟨i, hi, ?_, ?_⟩
    · exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · simpa only [zero_mul, add_zero, sub_zero] using hv
  calc
    volume E ≤ volume (⋃ i ∈ A, shearRect (g i) ((a + b) / 2) ((b - a) / 2) 0 0 δ) :=
      measure_mono hsub
    _ ≤ ∑ i ∈ A, volume (shearRect (g i) ((a + b) / 2) ((b - a) / 2) 0 0 δ) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ A, ENNReal.ofReal (2 * δ * (b - a)) := by
      apply Finset.sum_le_sum
      intro i hi
      convert volume_shearRect_le (hg i hi) ((a + b) / 2) ((b - a) / 2) 0 0 δ hδ using 1
      congr 1
      ring
    _ = ENNReal.ofReal (2 * δ * (b - a) * A.card) := by
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      ring

/-- The square-root crowding loss exactly cancels the shorter patch length. -/
theorem contact_cell_area_arithmetic {δ D s ℓ N C M : ℝ}
    (hδ : 0 < δ) (hD : 0 < D) (hs : 0 < s) (hℓ : 0 ≤ ℓ)
    (hN : 0 ≤ N) (hC : 0 ≤ C) (hlin : s * ℓ ≤ δ)
    (hcount : M ≤ C * (s / Real.sqrt (δ * D) * N * Real.sqrt N +
      s ^ 2 / (δ * D) * N)) :
    600 * δ * ℓ * M ≤ 600 * C * δ *
      (Real.sqrt (δ / D) * N * Real.sqrt N + s / D * N) := by
  have hroot : 0 < Real.sqrt (δ * D) := Real.sqrt_pos.mpr (mul_pos hδ hD)
  have hrootid : Real.sqrt (δ / D) * Real.sqrt (δ * D) = δ := by
    rw [← Real.sqrt_mul (div_nonneg hδ.le hD.le)]
    have heq : δ / D * (δ * D) = δ ^ 2 := by field_simp
    rw [heq, Real.sqrt_sq_eq_abs, abs_of_pos hδ]
  have hid : δ / Real.sqrt (δ * D) = Real.sqrt (δ / D) :=
    (div_eq_iff hroot.ne').mpr hrootid.symm
  have hscale : ℓ ≤ δ / s := (le_div_iff₀ hs).mpr (by nlinarith [hlin])
  have hfactor : 0 ≤ C * (s / Real.sqrt (δ * D) * N * Real.sqrt N +
      s ^ 2 / (δ * D) * N) := by positivity
  calc
    _ ≤ (600 * δ * ℓ) *
        (C * (s / Real.sqrt (δ * D) * N * Real.sqrt N + s ^ 2 / (δ * D) * N)) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ ≤ (600 * δ * (δ / s)) *
        (C * (s / Real.sqrt (δ * D) * N * Real.sqrt N + s ^ 2 / (δ * D) * N)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale (by positivity)) hfactor
    _ = 600 * C * δ * (δ / Real.sqrt (δ * D) * N * Real.sqrt N + s / D * N) := by
      field_simp [hδ.ne', hD.ne', hs.ne', hroot.ne']
      <;> ring
    _ = _ := by rw [hid]

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
