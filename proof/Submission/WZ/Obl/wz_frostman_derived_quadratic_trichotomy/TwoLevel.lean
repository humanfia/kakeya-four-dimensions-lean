-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.TwoLevel.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.StickyBranch

/-!
# Two nested exact covers (the cover clauses of the frozen `SB`)

For a canonical family without antipodal directions and radii `τ < ρ = m τ` (`m ≥ 2`), a set with
common residue classes at both radii has exact covers by unit `τ`-tubes `P j` and unit `ρ`-tubes
`R l` (both pairwise half-overlapping, built from cells). Every δ-tube lies in exactly one
`P j` and exactly one `R l`, every `P j` lies in exactly one `R l`, and every tube of either net
is used. These are the cover clauses of the frozen `SB` of o071/o070.
-/

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy

theorem two_level_cover {δ τ ρ : ℝ} (hδ : 0 < δ) (hδτ : 2 * δ ≤ τ) {m : ℕ} (hm : 2 ≤ m)
    (hρm : ρ = (m : ℝ) * τ) (hρ : ρ ≤ 1 / 10000)
    {n : ℕ} (x v : Fin n → Sp) (hv : ∀ i, ‖v i‖ = 1)
    (hT : ∀ i, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : Sp) 1)
    (hcan : ∀ i, x i = leftStart δ (x i) (v i)) (hanti : ∀ i j, 1 ≤ ‖v i + v j‖)
    (S : Finset (Fin n)) (hS : S.Nonempty)
    (hclsτ : ∀ i ∈ S, ∀ i' ∈ S, classKey 200000 τ (x i) (v i) = classKey 200000 τ (x i') (v i'))
    (hclsρ : ∀ i ∈ S, ∀ i' ∈ S, classKey 200000 ρ (x i) (v i) = classKey 200000 ρ (x i') (v i')) :
    ∃ (p : ℕ) (y u : Fin p → Sp) (q : ℕ) (z w : Fin q → Sp),
      (∀ j, ‖u j‖ = 1) ∧ (∀ l, ‖w l‖ = 1) ∧
      (∀ j j', j ≠ j' → MeasureTheory.volume
          (Metric.thickening τ (segment ℝ (y j) (y j + u j)) ∩
            Metric.thickening τ (segment ℝ (y j') (y j' + u j'))) ≤
          (1 / 2 : ENNReal) *
            MeasureTheory.volume (Metric.thickening τ (segment ℝ (y j) (y j + u j)))) ∧
      (∀ l l', l ≠ l' → MeasureTheory.volume
          (Metric.thickening ρ (segment ℝ (z l) (z l + w l)) ∩
            Metric.thickening ρ (segment ℝ (z l') (z l' + w l'))) ≤
          (1 / 2 : ENNReal) *
            MeasureTheory.volume (Metric.thickening ρ (segment ℝ (z l) (z l + w l)))) ∧
      (∀ i ∈ S, ∃! j, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
          Metric.thickening τ (segment ℝ (y j) (y j + u j))) ∧
      (∀ j, ∃ i ∈ S, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
          Metric.thickening τ (segment ℝ (y j) (y j + u j))) ∧
      (∀ j, ∃! l, Metric.thickening τ (segment ℝ (y j) (y j + u j)) ⊆
          Metric.thickening ρ (segment ℝ (z l) (z l + w l))) ∧
      (∀ l, ∃ j, Metric.thickening τ (segment ℝ (y j) (y j + u j)) ⊆
          Metric.thickening ρ (segment ℝ (z l) (z l + w l))) ∧
      (∀ i ∈ S, ∃! l, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
          Metric.thickening ρ (segment ℝ (z l) (z l + w l))) ∧
      (∀ j, ∃ i₀ ∈ S, y j = x i₀ ∧ u j = v i₀ ∧
          ∀ i ∈ S, (Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
            Metric.thickening τ (segment ℝ (y j) (y j + u j)) ↔
              lineCell (τ / 20) (x i) (v i) = lineCell (τ / 20) (x i₀) (v i₀))) ∧
      (∀ l, ∃ i₁ ∈ S, z l = x i₁ ∧ w l = v i₁ ∧
          ∀ i ∈ S, (Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
            Metric.thickening ρ (segment ℝ (z l) (z l + w l)) ↔
              lineCell (ρ / 20) (x i) (v i) = lineCell (ρ / 20) (x i₁) (v i₁))) := by
  have hτ0 : 0 < τ := by linarith
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hτρ : 2 * τ ≤ ρ := by rw [hρm]; nlinarith
  have hτsmall : τ ≤ 1 / 10000 := by linarith
  obtain ⟨p, -, y, u, hu, hovP, hexuP, husedP, hfibP⟩ :=
    cell_cover hδ hδτ hτsmall x v hv hT hcan hanti S hS hclsτ
  obtain ⟨q, -, z, w, hw, hovR, hexuR, husedR, hfibR⟩ :=
    cell_cover hδ (by linarith) hρ x v hv hT hcan hanti S hS hclsρ
  have hs : 0 < ρ / 20 := by linarith
  -- the τ-tube around a member lies in the ρ-tube around a member of the same ρ-cell
  have hPR : ∀ i₀ ∈ S, ∀ i₁ ∈ S, lineCell (ρ / 20) (x i₀) (v i₀) = lineCell (ρ / 20) (x i₁) (v i₁) →
      Metric.thickening τ (segment ℝ (x i₀) (x i₀ + v i₀)) ⊆
        Metric.thickening ρ (segment ℝ (x i₁) (x i₁ + v i₁)) := by
    intro i₀ _ i₁ _ hcell
    exact (thick_subset_of_same_cell hδ hs (hv i₀) (hv i₁) (hT i₀) (hT i₁) (hcan i₀) (hcan i₁)
      hcell).trans (Metric.thickening_mono (by linarith) _)
  -- nesting of the grids: `ρ/20 = m (τ/20)`
  have hnest : ∀ i i', lineCell (τ / 20) (x i) (v i) = lineCell (τ / 20) (x i') (v i') →
      lineCell (ρ / 20) (x i) (v i) = lineCell (ρ / 20) (x i') (v i') := by
    intro i i' h
    have e : ρ / 20 = (m : ℝ) * (τ / 20) := by rw [hρm]; ring
    rw [e]
    exact lineCell_nest (by positivity) (by omega) h
  refine ⟨p, y, u, q, z, w, hu, hw, hovP, hovR, hexuP, husedP, fun j => ?_, fun l => ?_, hexuR,
    hfibP, hfibR⟩
  · -- every τ-tube lies in exactly one ρ-tube
    obtain ⟨i₀, hi₀, hy, hu₀, -⟩ := hfibP j
    obtain ⟨l₀, hl₀, hl₀u⟩ := hexuR i₀ hi₀
    obtain ⟨i₁, hi₁, hz, hw₁, hiffR⟩ := hfibR l₀
    have hcell : lineCell (ρ / 20) (x i₀) (v i₀) = lineCell (ρ / 20) (x i₁) (v i₁) :=
      (hiffR i₀ hi₀).1 hl₀
    have hsub : Metric.thickening τ (segment ℝ (y j) (y j + u j)) ⊆
        Metric.thickening ρ (segment ℝ (z l₀) (z l₀ + w l₀)) := by
      rw [hy, hu₀, hz, hw₁]
      exact hPR i₀ hi₀ i₁ hi₁ hcell
    refine ⟨l₀, hsub, fun l hl => hl₀u l ?_⟩
    have hA : Metric.thickening δ (segment ℝ (x i₀) (x i₀ + v i₀)) ⊆
        Metric.thickening τ (segment ℝ (y j) (y j + u j)) := by
      rw [hy, hu₀]
      exact Metric.thickening_mono (by linarith) _
    exact hA.trans hl
  · -- every ρ-tube contains a τ-tube
    obtain ⟨i, hi, hiR⟩ := husedR l
    obtain ⟨j, hjP, -⟩ := hexuP i hi
    obtain ⟨i₀, hi₀, hy, hu₀, hiffP⟩ := hfibP j
    obtain ⟨i₁, hi₁, hz, hw₁, hiffR⟩ := hfibR l
    have hτcell : lineCell (τ / 20) (x i) (v i) = lineCell (τ / 20) (x i₀) (v i₀) :=
      (hiffP i hi).1 hjP
    have hρcell : lineCell (ρ / 20) (x i) (v i) = lineCell (ρ / 20) (x i₁) (v i₁) :=
      (hiffR i hi).1 hiR
    have hcell : lineCell (ρ / 20) (x i₀) (v i₀) = lineCell (ρ / 20) (x i₁) (v i₁) :=
      (hnest i i₀ hτcell).symm.trans hρcell
    refine ⟨j, ?_⟩
    rw [hy, hu₀, hz, hw₁]
    exact hPR i₀ hi₀ i₁ hi₁ hcell

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy
