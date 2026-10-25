import Submission.Obl.k4_scalar_tangent_isotropic_improvement.GridStateRestoration
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.GridWitnessTransfer
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.ConditionalPalette
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.VelocityBins

/-! Recover a quadratic from original incidence cells and a fixed original velocity palette. -/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

noncomputable section

open Set MeasureTheory
open scoped BigOperators Classical

attribute [-instance] Nat.decidableForallFin Fintype.decidableForallFintype

/-- The finite recovery core. Conditional angular ceilings produce the good
palette, coarse caps separate four fine-bin centers, and their actual incidence
witnesses transfer to entire base cells before Remez. -/
theorem quadratic_recovery_of_incidence_cells (D : ℕ) :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
    ∀ (Ω ι β : Type*) [MeasurableSpace Ω] [Fintype β]
      (μ : Measure Ω) [IsFiniteMeasure μ] (π : Measure ℝ) [IsProbabilityMeasure π]
      (z : Ω → Fin 2 → ℝ) (V : Ω → ℝ) (Cells : ι → Set Ω) (S : Finset ι)
      (m : ι → ℝ) (b : β → ℤ) (p : MvPolynomial (Fin 2) ℝ) (o : Fin 2 → ℝ)
      (ξ ξᵥ δ H K F M η E r : ℝ),
      p.totalDegree ≤ D → (∀ a, |p.coeff a| ≤ H) →
      0 < ξ → 0 < ξᵥ → 0 < δ → ξᵥ ≤ δ → 1 ≤ H → H ≤ K → K⁻¹ ≤ δ →
      0 < F → 0 ≤ M → 0 < η → η ≤ 1 → 0 ≤ E → 0 ≤ r → Function.Injective b →
      (∀ j, |ξᵥ * (b j : ℝ)| ≤ H) →
      (∀ i, 0 ≤ m i) → 0 < (∑ i ∈ S, m i) →
      (∀ i, MeasurableSet (Cells i)) → (Pairwise fun i j => Disjoint (Cells i) (Cells j)) →
      (∀ i ∈ S, ENNReal.ofReal (m i) ≤ μ (Cells i)) →
      (∀ i ∈ S, 0 < μ (Cells i)) →
      (∀ i ∈ S, μ (Cells i) ≤ ∑ j, μ (Cells i ∩ V ⁻¹' scalarVelocityBin ξᵥ (b j))) →
      (∀ i ∈ S, ∀ j, μ (Cells i ∩ V ⁻¹' scalarVelocityBin ξᵥ (b j)) ≤
        ENNReal.ofReal H * μ (Cells i) * π (scalarVelocityBin ξᵥ (b j))) →
      (∀ j : ℤ, π (scalarVelocityBin δ j) ≤ ENNReal.ofReal M) → 5 * M ≤ H⁻¹ / 8 →
      (∀ i ∈ S, ∀ ω ∈ Cells i, |V ω| ≤ H ∧ |cubicTest p (z ω) (V ω)| ≤ E) →
      (∀ i ∈ S, ∀ ω ∈ Cells i, ∀ ω' ∈ Cells i, dist (z ω) (z ω') ≤ r) →
      (∀ i ∈ S, ∀ ω ∈ Cells i,
        baseGridCell o ξ (baseGridTag o ξ (z ω)) ⊆ Set.Icc (0 : Fin 2 → ℝ) 1) →
      (∀ q : Fin 2 → ℤ, μ {ω | baseGridTag o ξ (z ω) = q} ≤
        ENNReal.ofReal F * ENNReal.ofReal (ξ ^ 2)) →
      F * η ≤ (H⁻¹ / 2) ^ 4 * (∑ i ∈ S, m i) →
      ∃ Q : MvPolynomial (Fin 2) ℝ, Q.totalDegree ≤ 2 ∧
        (∀ a, |Q.coeff a| ≤ |p.coeff a|) ∧
        ∀ x ∈ Set.Icc (0 : Fin 2 → ℝ) 1,
          |MvPolynomial.eval x p - MvPolynomial.eval x Q| ≤
            C₀ * K ^ 18 * (16 * ((D : ℝ) + 1) / η) ^ (2 * D) *
              (E + C₁ * H ^ (2 * D + 4) * (ξ + r + ξᵥ)) := by
  obtain ⟨C₀, hC₀, hrest⟩ := quadratic_restoration_from_gridded_states D
  obtain ⟨C₁, hC₁, htransfer⟩ := cubicTest_le_on_gridCell D
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro Ω ι β mΩ instβ μ instμ π instπ z V Cells S m b p o ξ ξᵥ δ H K F M η E r
    hp hc hξ hξᵥ hδ hξδ hH hHK hsep hF hM hη hη1 hE hr hb hv hm hS hCells hdisj hfloor
    hpos hcover hcond hcoarse hMsmall htests hdiam hbox hgrid hmass
  let w : β → ℝ := fun j => (π (scalarVelocityBin ξᵥ (b j))).toReal
  let v : β → ℝ := fun j => ξᵥ * (b j : ℝ)
  let Good : ι → β → Prop := fun i j => 0 < (μ (Cells i ∩ V ⁻¹' scalarVelocityBin ξᵥ (b j))).toReal
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hw1 : (∑ j, w j) ≤ 1 := by
    apply original_palette_weights_subprobability π (fun j => scalarVelocityBin ξᵥ (b j))
      (fun j => measurableSet_scalarVelocityBin ξᵥ (b j))
    intro i j hij
    exact scalarVelocityBin_disjoint ξᵥ (fun he => hij (hb he))
  have hgood (i : ι) (hi : i ∈ S) : H⁻¹ ≤ ∑ j, if Good i j then w j else 0 :=
    palette_support_mass_of_measure_caps μ π (Cells i) V (fun j => scalarVelocityBin ξᵥ (b j))
      hHpos (hpos i hi) (hcover i hi) (hcond i hi)
  have hnear (u : ℝ) : (∑ j, if |v j - u| < δ then w j else 0) ≤ H⁻¹ / 8 :=
    (fine_palette_neighborhood_cap π b hb hξᵥ hδ hξδ hM hcoarse u).trans hMsmall
  refine hrest Ω ι β μ z Cells S m w v Good p o ξ K F η
    (E + C₁ * H ^ (2 * D + 4) * (ξ + r + ξᵥ)) H⁻¹ δ hp hξ (hH.trans hHK) hF hη hη1
    (by positivity) (inv_pos.mpr hHpos) hsep (fun j => (hv j).trans hHK)
    (fun j => ENNReal.toReal_nonneg) hw1 hm hS hCells hdisj hfloor hbox hgood hnear ?_ hgrid hmass
  intro i hi j hgood ω hω x hx
  have hne : μ (Cells i ∩ V ⁻¹' scalarVelocityBin ξᵥ (b j)) ≠ 0 := by
    intro hz
    simp only [Good, hz, ENNReal.toReal_zero, lt_self_iff_false] at hgood
  have hex : (Cells i ∩ V ⁻¹' scalarVelocityBin ξᵥ (b j)).Nonempty := by
    by_contra he
    exact hne (by rw [Set.not_nonempty_iff_eq_empty.mp he, measure_empty])
  obtain ⟨ω', hω', hbin⟩ := hex
  have hcenter : |v j - V ω'| ≤ ξᵥ := by
    simpa only [v, abs_sub_comm] using scalarVelocityBin_center_error hξᵥ hbin
  have hu : ∀ e, |z ω' e| ≤ H := by
    have hu := hbox i hi ω' hω' ((mem_baseGridCell_iff o hξ _ _).mpr rfl)
    intro e
    rw [abs_of_nonneg (hu.1 e)]
    exact (hu.2 e).trans hH
  exact htransfer p o (z ω) (z ω') ξ H r ξᵥ E (v j) (V ω') hp hξ hH hc
    (hbox i hi ω hω) hu (hv j) (htests i hi ω' hω').1 (hdiam i hi ω hω ω' hω') hcenter
    (htests i hi ω' hω').2 x hx

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
