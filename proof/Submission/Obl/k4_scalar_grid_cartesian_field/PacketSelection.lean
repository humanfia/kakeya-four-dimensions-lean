import Mathlib

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory

/-- Select a packet against its full original prior budget, without normalizing its law. -/
theorem exists_packet_mass_ratio {ι : Type*} [Fintype ι]
    (weight prior mass : ι → ENNReal) (a : ENNReal)
    (hbudget : ∑ i, weight i * prior i ≤ 1)
    (hmass : a < ∑ i, weight i * mass i) :
    ∃ i, weight i ≠ 0 ∧ a * prior i ≤ mass i := by
  classical
  by_contra h
  have hbound : ∀ i, weight i * mass i ≤ a * (weight i * prior i) := by
    intro i
    by_cases hw : weight i = 0
    · simp [hw]
    · have hsmall : mass i < a * prior i := by
        by_contra hn
        exact h ⟨i, hw, le_of_not_gt hn⟩
      calc
        weight i * mass i ≤ weight i * (a * prior i) := mul_le_mul' le_rfl hsmall.le
        _ = a * (weight i * prior i) := by ac_rfl
  have htotal : ∑ i, weight i * mass i ≤ a := by
    calc
      _ ≤ ∑ i, a * (weight i * prior i) := Finset.sum_le_sum fun i _ => hbound i
      _ = a * ∑ i, weight i * prior i := (Finset.mul_sum _ _ _).symm
      _ ≤ a * 1 := mul_le_mul' le_rfl hbudget
      _ = a := mul_one _
  exact hmass.not_ge htotal

/-- The assignment budget for arbitrary measurable trajectory spaces.
This is the scalar-space generalization of accepted
`Submission.Lib.K4ChartLifting.ChartSystem.normZ_le_one`. -/
theorem packet_prior_budget {α : Type*} [MeasurableSpace α] {W n T : ℕ}
    (ω : Fin W → ℝ) (ν : Fin W → Measure α) [∀ g, IsProbabilityMeasure (ν g)]
    (γ : Fin n → Fin W) (j : Fin n → Fin (2 ^ T)) (A : Fin n → Set α)
    (hω : ∀ g, 0 ≤ ω g) (hωsum : ∑ g, ω g = 1)
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : ∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i')) :
    ∑ i, ENNReal.ofReal (ω (γ i)) *
      (ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ * ν (γ i) (A i)) ≤ 1 := by
  classical
  have hgroup : ∀ (g : Fin W) (b : Fin (2 ^ T)),
      ∑ i ∈ Finset.univ.filter (fun i => γ i = g ∧ j i = b), ν g (A i) ≤ 1 := by
    intro g b
    let I := Finset.univ.filter (fun i => γ i = g ∧ j i = b)
    have hp : (↑I : Set (Fin n)).PairwiseDisjoint A := by
      intro i hi i' hi' hne
      have h₁ := (Finset.mem_filter.mp hi).2
      have h₂ := (Finset.mem_filter.mp hi').2
      exact hdisj i i' hne (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)
    rw [← measure_biUnion_finset hp (fun i _ => hA i)]
    exact (measure_mono (subset_univ _)).trans_eq (measure_univ)
  calc
    _ = ∑ g, ∑ b : Fin (2 ^ T), ∑ i ∈ Finset.univ.filter
        (fun i => γ i = g ∧ j i = b), ENNReal.ofReal (ω (γ i)) *
          (ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ * ν (γ i) (A i)) := by
      simpa only [Fintype.sum_prod_type, Prod.mk.injEq] using
        (Finset.sum_fiberwise Finset.univ (fun i => (γ i, j i))
          (fun i => ENNReal.ofReal (ω (γ i)) *
            (ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ * ν (γ i) (A i)))).symm
    _ ≤ ∑ g, ∑ _b : Fin (2 ^ T),
        ENNReal.ofReal (ω g) * ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ := by
      apply Finset.sum_le_sum
      intro g _
      apply Finset.sum_le_sum
      intro b _
      calc
        _ = ENNReal.ofReal (ω g) * ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ *
            ∑ i ∈ Finset.univ.filter (fun i => γ i = g ∧ j i = b), ν g (A i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [(Finset.mem_filter.mp hi).2.1]
          ac_rfl
        _ ≤ ENNReal.ofReal (ω g) * ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ * 1 :=
          mul_le_mul' le_rfl (hgroup g b)
        _ = _ := mul_one _
    _ = ∑ g, ENNReal.ofReal (ω g) := by
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have htwo : ENNReal.ofReal ((2 : ℝ) ^ T) = ((2 ^ T : ℕ) : ENNReal) := by
        norm_cast
      rw [ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < 2 ^ T), htwo]
      have hn : ((2 ^ T : ℕ) : ENNReal) ≠ 0 := by simp
      have hfin : ((2 ^ T : ℕ) : ENNReal) ≠ ⊤ := by simp
      rw [mul_comm (ENNReal.ofReal (ω g)), ← mul_assoc, ENNReal.mul_inv_cancel hn hfin,
        one_mul]
    _ = 1 := by rw [← ENNReal.ofReal_sum_of_nonneg (fun g _ => hω g), hωsum]; simp

end Submission.Obl.k4_scalar_grid_cartesian_field
