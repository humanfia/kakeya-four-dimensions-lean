import Submission.Obl.k4_scalar_tangent_isotropic_improvement.Restoration
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.PaletteSampling
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.GridCells

/-! Common-state recovery using finite grid-cell ceilings and polynomial cell thickening. -/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

noncomputable section

open Set MeasureTheory
open scoped BigOperators Classical

attribute [-instance] Nat.decidableForallFin Fintype.decidableForallFintype

/-- A gridded ceiling suffices for common-state recovery: after selecting four
velocities, thicken their occupied base cells. The resulting volume pays for
Remez without any assumption of absolute continuity of the original law. -/
theorem quadratic_restoration_from_gridded_states (M : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (Ω ι β : Type*) [MeasurableSpace Ω] [Fintype β]
      (μ : Measure Ω) (z : Ω → Fin 2 → ℝ) (Cells : ι → Set Ω)
      (S : Finset ι) (m : ι → ℝ) (w v : β → ℝ) (Good : ι → β → Prop)
      (p : MvPolynomial (Fin 2) ℝ) (o : Fin 2 → ℝ) (ξ K D η E q δ : ℝ),
      p.totalDegree ≤ M → 0 < ξ → 1 ≤ K → 0 < D → 0 < η → η ≤ 1 → 0 ≤ E → 0 < q →
      K⁻¹ ≤ δ → (∀ j, |v j| ≤ K) → (∀ j, 0 ≤ w j) → (∑ j, w j) ≤ 1 →
      (∀ i, 0 ≤ m i) → 0 < (∑ i ∈ S, m i) →
      (∀ i, MeasurableSet (Cells i)) → (Pairwise fun i j => Disjoint (Cells i) (Cells j)) →
      (∀ i ∈ S, ENNReal.ofReal (m i) ≤ μ (Cells i)) →
      (∀ i ∈ S, ∀ ω ∈ Cells i,
        baseGridCell o ξ (baseGridTag o ξ (z ω)) ⊆ Set.Icc (0 : Fin 2 → ℝ) 1) →
      (∀ i ∈ S, q ≤ ∑ j, if Good i j then w j else 0) →
      (∀ u : ℝ, (∑ j, if |v j - u| < δ then w j else 0) ≤ q / 8) →
      (∀ i ∈ S, ∀ j, Good i j → ∀ ω ∈ Cells i,
        ∀ x ∈ baseGridCell o ξ (baseGridTag o ξ (z ω)), |cubicTest p x (v j)| ≤ E) →
      (∀ b : Fin 2 → ℤ, μ {ω | baseGridTag o ξ (z ω) = b} ≤
        ENNReal.ofReal D * ENNReal.ofReal (ξ ^ 2)) →
      D * η ≤ (q / 2) ^ 4 * (∑ i ∈ S, m i) →
      ∃ Q : MvPolynomial (Fin 2) ℝ, Q.totalDegree ≤ 2 ∧
        (∀ b, |Q.coeff b| ≤ |p.coeff b|) ∧
        ∀ x ∈ Set.Icc (0 : Fin 2 → ℝ) 1,
          |MvPolynomial.eval x p - MvPolynomial.eval x Q| ≤
            C * K ^ 18 * (16 * ((M : ℝ) + 1) / η) ^ (2 * M) * E := by
  obtain ⟨C, hC, hrest⟩ := quadratic_restoration_of_witness_sets M
  refine ⟨C, hC, ?_⟩
  intro Ω ι β mΩ instβ μ z Cells S m w v Good p o ξ K D η E q δ
    hp hξ hK hD hη hη1 hE hq hδ hv hw hw1 hm hS hCells hdisj hfloor hbox hgood hcap htests hgrid hmass
  obtain ⟨a, hsep, hcommon⟩ := common_palette_four w v hw hw1 m hm S hS Good hq hgood hcap
  let J : Finset ι := S.filter (fun i => ∀ r, Good i (a r))
  let T : Set Ω := ⋃ i ∈ J, Cells i
  let B : Set (Fin 2 → ℝ) := Set.Icc (0 : Fin 2 → ℝ) 1 ∩
    ⋂ r : Fin 4, {x | |cubicTest p x (v (a r))| ≤ E}
  have hpointbox : ∀ ω ∈ T, z ω ∈ Set.Icc (0 : Fin 2 → ℝ) 1 := by
    intro ω hω
    obtain ⟨i, hi, hω⟩ := Set.mem_iUnion₂.mp hω
    apply hbox i (Finset.mem_filter.mp hi).1 ω hω
    exact (mem_baseGridCell_iff o hξ _ _).mpr rfl
  have hfinite : (baseGridTag o ξ '' (z '' T)).Finite := by
    apply baseGridTag_image_finite o hξ
    rintro x ⟨ω, hω, rfl⟩ e
    have hx := hpointbox ω hω
    have habs : |z ω e| ≤ 1 := by rw [abs_of_nonneg (hx.1 e)]; exact hx.2 e
    calc
      |z ω e - o e| ≤ |z ω e| + |o e| := abs_sub _ _
      _ ≤ 1 + ‖o‖ := add_le_add habs (norm_le_pi_norm o e)
  let Q : Finset (Fin 2 → ℤ) := hfinite.toFinset
  have hcover : ∀ ω ∈ T, baseGridTag o ξ (z ω) ∈ Q := by
    intro ω hω
    apply hfinite.mem_toFinset.mpr
    exact ⟨z ω, ⟨ω, hω, rfl⟩, rfl⟩
  have hthick : (⋃ b ∈ Q, baseGridCell o ξ b) ⊆ B := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨u, hu, hub⟩ := hfinite.mem_toFinset.mp hb
    obtain ⟨ω, hω, rfl⟩ := hu
    obtain ⟨i, hi, hω⟩ := Set.mem_iUnion₂.mp hω
    have hiS := (Finset.mem_filter.mp hi).1
    have hiGood := (Finset.mem_filter.mp hi).2
    have hxcell : x ∈ baseGridCell o ξ (baseGridTag o ξ (z ω)) := by rwa [hub]
    exact ⟨hbox i hiS ω hω hxcell,
      Set.mem_iInter.mpr (fun r => htests i hiS (a r) (hiGood r) ω hω x hxcell)⟩
  have hDJ : (↑J : Set ι).PairwiseDisjoint Cells := by
    intro i hi j hj hij
    exact hdisj hij
  have hmeasure : ENNReal.ofReal (D * η) ≤ ENNReal.ofReal D * volume B := by
    calc
      ENNReal.ofReal (D * η) ≤ ENNReal.ofReal ((q / 2) ^ 4 * (∑ i ∈ S, m i)) :=
        ENNReal.ofReal_le_ofReal hmass
      _ ≤ ENNReal.ofReal (∑ i ∈ J, m i) := ENNReal.ofReal_le_ofReal hcommon
      _ = ∑ i ∈ J, ENNReal.ofReal (m i) := ENNReal.ofReal_sum_of_nonneg (fun i hi => hm i)
      _ ≤ ∑ i ∈ J, μ (Cells i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hfloor i (Finset.mem_filter.mp hi).1
      _ = μ T := (measure_biUnion_finset hDJ (fun i hi => hCells i)).symm
      _ ≤ ENNReal.ofReal D * volume (⋃ b ∈ Q, baseGridCell o ξ b) :=
        measure_le_thickened_grid_volume μ z o hξ T Q D hcover (fun b hb => hgrid b)
      _ ≤ ENNReal.ofReal D * volume B := mul_le_mul_right (measure_mono hthick) _
  have hvolume : ENNReal.ofReal η ≤ volume B := by
    have hDne : ENNReal.ofReal D ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hD)
    have hdiv : ENNReal.ofReal (D * η) / ENNReal.ofReal D ≤ volume B :=
      (ENNReal.div_le_iff hDne ENNReal.ofReal_ne_top).mpr (by simpa only [mul_comm] using hmeasure)
    rw [← ENNReal.ofReal_div_of_pos hD] at hdiv
    have heq : D * η / D = η := by field_simp [hD.ne']
    simpa only [heq] using hdiv
  apply hrest p (fun r => v (a r)) (fun _ => B) K η E hp hK hη hη1 hE
    (fun r => hv (a r)) (fun r s hrs => hδ.trans (hsep r s hrs))
  intro r
  exact ⟨Set.inter_subset_left, hvolume, fun x hx => Set.mem_iInter.mp hx.2 r⟩

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
