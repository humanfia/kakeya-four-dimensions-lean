-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.GridParity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.GridAffine

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set MeasureTheory

/-- One parity of grid cells carries at least half of the measure of their
union. This needs no measurability of the sets and no disjointness. -/
theorem exists_nonadjacent_grid_selection {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (J : Finset ℤ) (D : ℤ → Set α) :
    ∃ K : Finset ℤ, K ⊆ J ∧ (∀ j ∈ K, j + 1 ∉ K) ∧
      μ (⋃ j ∈ J, D j) ≤ 2 * μ (⋃ j ∈ K, D j) := by
  classical
  let K₀ := J.filter (fun j => j % 2 = 0)
  let K₁ := J.filter (fun j => j % 2 ≠ 0)
  have hK₀ : K₀ ⊆ J := Finset.filter_subset _ _
  have hK₁ : K₁ ⊆ J := Finset.filter_subset _ _
  have hsep₀ : ∀ j ∈ K₀, j + 1 ∉ K₀ := by
    intro j hj hj'
    simp only [K₀, Finset.mem_filter] at hj hj'
    omega
  have hsep₁ : ∀ j ∈ K₁, j + 1 ∉ K₁ := by
    intro j hj hj'
    simp only [K₁, Finset.mem_filter] at hj hj'
    omega
  have hcover : (⋃ j ∈ J, D j) ⊆ (⋃ j ∈ K₀, D j) ∪ (⋃ j ∈ K₁, D j) := by
    intro p hp
    obtain ⟨j, hj, hp⟩ := mem_iUnion₂.mp hp
    by_cases h : j % 2 = 0
    · exact Or.inl (mem_iUnion₂.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, h⟩, hp⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, h⟩, hp⟩)
  have hmass : μ (⋃ j ∈ J, D j) ≤ μ (⋃ j ∈ K₀, D j) + μ (⋃ j ∈ K₁, D j) :=
    (measure_mono hcover).trans
      (measure_union_le (⋃ j ∈ K₀, D j) (⋃ j ∈ K₁, D j))
  rcases le_total (μ (⋃ j ∈ K₀, D j)) (μ (⋃ j ∈ K₁, D j)) with h | h
  · refine ⟨K₁, hK₁, hsep₁, ?_⟩
    calc
      μ (⋃ j ∈ J, D j) ≤ μ (⋃ j ∈ K₀, D j) + μ (⋃ j ∈ K₁, D j) := hmass
      _ ≤ μ (⋃ j ∈ K₁, D j) + μ (⋃ j ∈ K₁, D j) := add_le_add h le_rfl
      _ = 2 * μ (⋃ j ∈ K₁, D j) := (two_mul _).symm
  · refine ⟨K₀, hK₀, hsep₀, ?_⟩
    calc
      μ (⋃ j ∈ J, D j) ≤ μ (⋃ j ∈ K₀, D j) + μ (⋃ j ∈ K₁, D j) := hmass
      _ ≤ μ (⋃ j ∈ K₀, D j) + μ (⋃ j ∈ K₀, D j) := add_le_add le_rfl h
      _ = 2 * μ (⋃ j ∈ K₀, D j) := (two_mul _).symm

/-- Local affine fits on finitely many cells assemble after a fixed-factor
selection into a fit affine on the entire grid. -/
theorem select_and_extend_grid_fits (μ : Measure ℝ) {h ρ : ℝ} (hh : 0 < h)
    (f : ℝ → ℝ) (J : Finset ℤ) (D : ℤ → Set ℝ)
    (hc : ∀ j ∈ J, IsCompact (D j))
    (hcell : ∀ j ∈ J, D j ⊆ Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h))
    (hfit : ∀ j ∈ J, ∃ a b : ℝ, ∀ z ∈ D j, |f z - (a + b * z)| ≤ ρ) :
    ∃ (D' : Set ℝ) (L : ℝ → ℝ), IsCompact D' ∧ D' ⊆ ⋃ j ∈ J, D j ∧
      μ (⋃ j ∈ J, D j) ≤ 2 * μ D' ∧ AffineOnGrid h L ∧
      ∀ z ∈ D', |f z - L z| ≤ ρ := by
  classical
  obtain ⟨K, hK, hsep, hmass⟩ := exists_nonadjacent_grid_selection μ J D
  have hfits : ∀ j : ℤ, ∃ a b : ℝ, j ∈ J → ∀ z ∈ D j, |f z - (a + b * z)| ≤ ρ := by
    intro j
    by_cases hj : j ∈ J
    · obtain ⟨a, b, h⟩ := hfit j hj
      exact ⟨a, b, fun _ => h⟩
    · exact ⟨0, 0, fun h => (hj h).elim⟩
  choose a b hab using hfits
  obtain ⟨L, hgrid, hL⟩ := exists_affine_grid_extension hh (↑K : Set ℤ) a b hsep
  refine ⟨⋃ j ∈ K, D j, L, ?_, ?_, hmass, hgrid, ?_⟩
  · exact K.isCompact_biUnion fun j hj => hc j (hK hj)
  · exact iUnion₂_mono' fun j hj => ⟨j, hK hj, subset_rfl⟩
  · intro z hz
    obtain ⟨j, hj, hz⟩ := mem_iUnion₂.mp hz
    rw [hL j hj z (hcell j (hK hj) hz)]
    exact hab j (hK hj) z hz

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
