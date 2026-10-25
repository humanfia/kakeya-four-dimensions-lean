import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit.SlicedPigeon

/-!
Moved from o217 (branch x0763, same author, session x0763 = x0931), namespace changed.
# The sliced fit: quadrants and occupied cells

`exists_heavy_quad` restricts the collisions to one quadrant of `a = (u - u₀, φ u₀ - φ u)`
(paper: "Retain a quadrant for `a` containing a fixed fraction of the pair mass");
`exists_occupied_cells` turns the collision mass into a count of occupied `(u, v, v')` cells
(paper: "Each `(u, v_l, v_l')`-cell therefore carries at most `K p^{3+2d}`").
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A quadrant for `a = (u - u₀, φ u₀ - φ u)`, with signs `s₁, s₂`. -/
def quadSet (D : SlicedData Ω) (u₀ s₁ s₂ : ℝ) : Set ((Ω × Ω) × ℝ) :=
  {x | 0 ≤ s₁ * (x.2 - u₀) ∧ 0 ≤ s₂ * (D.φ u₀ - D.φ x.2)}

theorem measurableSet_quadSet {D : SlicedData Ω} {p K d : ℝ} (H : SlicedHyp D p K d)
    (u₀ s₁ s₂ : ℝ) : MeasurableSet (quadSet D u₀ s₁ s₂) := by
  have h1 : Measurable (fun x : (Ω × Ω) × ℝ => s₁ * (x.2 - u₀)) :=
    measurable_const.mul (measurable_snd.sub measurable_const)
  have h2 : Measurable (fun x : (Ω × Ω) × ℝ => s₂ * (D.φ u₀ - D.φ x.2)) :=
    measurable_const.mul (measurable_const.sub (H.measφ.comp measurable_snd))
  exact (measurableSet_le measurable_const h1).inter (measurableSet_le measurable_const h2)

/-- One of the four quadrants carries a quarter of any mass. -/
theorem exists_heavy_quad {D : SlicedData Ω} (μ : Measure ((Ω × Ω) × ℝ)) (u₀ : ℝ)
    (S : Set ((Ω × Ω) × ℝ)) :
    ∃ s₁ s₂ : ℝ, (s₁ = 1 ∨ s₁ = -1) ∧ (s₂ = 1 ∨ s₂ = -1) ∧
      μ S ≤ 4 * μ (S ∩ quadSet D u₀ s₁ s₂) := by
  have hcov : S ⊆ (S ∩ quadSet D u₀ 1 1) ∪ (S ∩ quadSet D u₀ 1 (-1)) ∪
      (S ∩ quadSet D u₀ (-1) 1) ∪ (S ∩ quadSet D u₀ (-1) (-1)) := by
    intro x hx
    simp only [quadSet, mem_union, mem_inter_iff, mem_ofPred_eq, one_mul, neg_one_mul,
      neg_nonneg]
    rcases le_total 0 (x.2 - u₀) with h1 | h1 <;>
    rcases le_total 0 (D.φ u₀ - D.φ x.2) with h2 | h2 <;> tauto
  set m := fun s₁ s₂ => μ (S ∩ quadSet D u₀ s₁ s₂)
  have hsum : μ S ≤ m 1 1 + m 1 (-1) + m (-1) 1 + m (-1) (-1) :=
    (measure_mono hcov).trans ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
      (add_le_add (measure_union_le _ _) le_rfl)) le_rfl))
  set M := max (max (m 1 1) (m 1 (-1))) (max (m (-1) 1) (m (-1) (-1))) with hM
  have h4M : m 1 1 + m 1 (-1) + m (-1) 1 + m (-1) (-1) ≤ 4 * M := by
    have a1 : m 1 1 ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
    have a2 : m 1 (-1) ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
    have a3 : m (-1) 1 ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
    have a4 : m (-1) (-1) ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
    calc m 1 1 + m 1 (-1) + m (-1) 1 + m (-1) (-1) ≤ M + M + M + M := by gcongr
      _ = 4 * M := by ring
  have hS4 := hsum.trans h4M
  rw [hM] at hS4
  rcases max_choice (max (m 1 1) (m 1 (-1))) (max (m (-1) 1) (m (-1) (-1))) with h | h <;>
    rw [h] at hS4
  · rcases max_choice (m 1 1) (m 1 (-1)) with h' | h' <;> rw [h'] at hS4
    · exact ⟨1, 1, Or.inl rfl, Or.inl rfl, hS4⟩
    · exact ⟨1, -1, Or.inl rfl, Or.inr rfl, hS4⟩
  · rcases max_choice (m (-1) 1) (m (-1) (-1)) with h' | h' <;> rw [h'] at hS4
    · exact ⟨-1, 1, Or.inr rfl, Or.inl rfl, hS4⟩
    · exact ⟨-1, -1, Or.inr rfl, Or.inr rfl, hS4⟩


/-- **Occupied cells**: the collision mass of `S ⊆ Scol` is at most the number of occupied
`(u, v, v')` cells times the cell bound. -/
theorem exists_occupied_cells {D : SlicedData Ω} {p K d : ℝ} (H : SlicedHyp D p K d)
    (hp : 0 < p) (hK : 1 ≤ K) {u₀ : ℝ} (hu₀ : u₀ ∈ Icc (0:ℝ) 1) (β₀ : ℤ)
    (S : Set ((Ω × Ω) × ℝ)) (hSsub : S ⊆ Scol D p u₀ β₀) :
    ∃ Occ : Finset (ℤ × ℤ × ℤ),
      ((D.ν.prod D.ν).prod volume) S ≤ Occ.card * (ENNReal.ofReal p *
        (ENNReal.ofReal (K * p ^ (1 + d)) * ENNReal.ofReal ((36 * K ^ 2 + 3) * (K * p ^ (1 + d))))) ∧
      ∀ c ∈ Occ, (S ∩ cellSet D p c.1 c.2.1 c.2.2).Nonempty := by
  classical
  set CI : Finset (ℤ × ℤ × ℤ) := Finset.Icc 0 ⌊1 / p⌋ ×ˢ (vBins K p ×ˢ vBins K p) with hCI
  set Occ := CI.filter (fun c => (S ∩ cellSet D p c.1 c.2.1 c.2.2).Nonempty) with hOcc
  refine ⟨Occ, ?_, fun c hc => (Finset.mem_filter.1 hc).2⟩
  have hcov : S ⊆ ⋃ c ∈ Occ, S ∩ cellSet D p c.1 c.2.1 c.2.2 := by
    intro x hx
    have hxE : (x.1.1, x.2) ∈ D.E := (hSsub hx).1.1.1
    have hu := H.E01 _ hxE
    have hc : (⌊x.2 / p⌋, ⌊D.v x.1.1 / p⌋, ⌊D.v x.1.2 / p⌋) ∈ CI := by
      refine Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨?_, ?_⟩,
        Finset.mem_product.2 ⟨mem_vBins hp (H.vbound _), mem_vBins hp (H.vbound _)⟩⟩
      · exact Int.floor_nonneg.2 (div_nonneg hu.1 hp.le)
      · exact Int.floor_le_floor (div_le_div_of_nonneg_right hu.2 hp.le)
    have hmem : x ∈ S ∩ cellSet D p ⌊x.2 / p⌋ ⌊D.v x.1.1 / p⌋ ⌊D.v x.1.2 / p⌋ :=
      ⟨hx, rfl, rfl, rfl⟩
    exact mem_iUnion₂.2 ⟨_, Finset.mem_filter.2 ⟨hc, ⟨x, hmem⟩⟩, hmem⟩
  calc ((D.ν.prod D.ν).prod volume) S
      ≤ ∑ c ∈ Occ, ((D.ν.prod D.ν).prod volume) (S ∩ cellSet D p c.1 c.2.1 c.2.2) :=
        (measure_mono hcov).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _c ∈ Occ, (ENNReal.ofReal p * (ENNReal.ofReal (K * p ^ (1 + d)) *
          ENNReal.ofReal ((36 * K ^ 2 + 3) * (K * p ^ (1 + d))))) := by
        apply Finset.sum_le_sum
        intro c _
        exact (measure_mono (inter_subset_inter_left _ hSsub)).trans
          (cellMass_le H hp hK hu₀ β₀ c.1 c.2.1 c.2.2)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

end
