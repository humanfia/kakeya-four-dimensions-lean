import Submission.Obl.k4_scalar_grid_cartesian_field.PacketSelection

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory

/-- A finite original packet union is bounded by the sum of its original members. -/
theorem weighted_packet_union_mass {Ω G J : Type*}
    [MeasurableSpace Ω] [Fintype G] [Fintype J]
    (μ : G → Measure Ω) (weight : G → ENNReal) (world : J → G) (P : J → Set Ω) :
    (∑ g, weight g * μ g {x | ∃ i, world i = g ∧ x ∈ P i}) ≤
      ∑ i, weight (world i) * μ (world i) (P i) := by
  classical
  let Q : G → Finset J := fun g => Finset.univ.filter (fun i => world i = g)
  have hworld (g : G) : μ g {x | ∃ i, world i = g ∧ x ∈ P i} ≤ ∑ i ∈ Q g, μ g (P i) := by
    have heq : {x | ∃ i, world i = g ∧ x ∈ P i} = ⋃ i ∈ Q g, P i := by
      ext x
      simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and, mem_iUnion, mem_ofPred_eq]
      aesop
    rw [heq]
    exact measure_biUnion_finset_le _ _
  calc
    _ ≤ ∑ g, weight g * ∑ i ∈ Q g, μ g (P i) :=
      Finset.sum_le_sum fun g _ => mul_le_mul' le_rfl (hworld g)
    _ = ∑ i, weight (world i) * μ (world i) (P i) := by
      simp only [Q, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp

/-- The original finite packet cover also covers every retained incidence submeasure. -/
theorem weighted_packet_cover_mass {Ω G J : Type*}
    [MeasurableSpace Ω] [Fintype G] [Fintype J]
    (μ : G → Measure Ω) (weight : G → ENNReal) (world : J → G) (P : J → Set Ω)
    (hcover : ∀ g, μ g {p | ∃ i, world i = g ∧ p ∈ P i}ᶜ = 0) :
    (∑ g, weight g * μ g univ) ≤ ∑ i, weight (world i) * μ (world i) (P i) := by
  calc
    _ = ∑ g, weight g * μ g {x | ∃ i, world i = g ∧ x ∈ P i} := by
      apply Finset.sum_congr rfl
      intro g _
      congr 1
      simpa using (measure_inter_conull (hcover g) (s := univ)).symm
    _ ≤ _ := weighted_packet_union_mass μ weight world P

/-- A retained positive world mass selects an original packet relative to its full prior mass. -/
theorem exists_original_packet_with_retained_mass {Ω G J : Type*}
    [MeasurableSpace Ω] [Fintype G] [Fintype J]
    (μ : G → Measure Ω) (weight : G → ENNReal) (world : J → G)
    (P : J → Set Ω) (prior : J → ENNReal) (a : ENNReal)
    (hprior : ∑ i, weight (world i) * prior i ≤ 1)
    (hcover : ∀ g, μ g {p | ∃ i, world i = g ∧ p ∈ P i}ᶜ = 0)
    (hmass : a < ∑ g, weight g * μ g univ) :
    ∃ i, weight (world i) ≠ 0 ∧ a * prior i ≤ μ (world i) (P i) := by
  exact exists_packet_mass_ratio (fun i => weight (world i)) prior
    (fun i => μ (world i) (P i)) a hprior
    (hmass.trans_le (weighted_packet_cover_mass μ weight world P hcover))

end Submission.Obl.k4_scalar_grid_cartesian_field
