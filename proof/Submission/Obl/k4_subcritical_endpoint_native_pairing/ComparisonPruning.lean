/- Adapted from this LOT tree, obligation o218, session x0764, commit e1e41f8e737fdc1974cfdf32d18bbf69838b3ce8,
   Submission/Obl/k4_horizontal_endpoint_wide_return/ComparisonPruning.lean.
   Original source attributions are retained below. -/
import Submission.Lib.K4FinalLawSelection

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing

open Set MeasureTheory

/-- Prune both comparison lists on every domain using their original reference
weights. Both lists cover the SAME final law, and surviving indices keep their
original domain tags. -/
theorem prune_comparison_lists {Ω ι₁ ι₂ Γ : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s₁ : Finset ι₁) (s₂ : Finset ι₂)
    (E₁ : ι₁ → Set Ω) (E₂ : ι₂ → Set Ω)
    (hE₁ : ∀ i, MeasurableSet (E₁ i)) (hE₂ : ∀ i, MeasurableSet (E₂ i))
    (domain₁ : ι₁ → Γ) (domain₂ : ι₂ → Γ) (reader : Ω → Γ)
    (T : Γ → ENNReal) (ε B : ENNReal)
    (hbudget : (∑ i ∈ s₁, T (domain₁ i)) + (∑ i ∈ s₂, T (domain₂ i)) ≤ B)
    (hsub₁ : ∀ i ∈ s₁, ∀ p ∈ E₁ i, reader p = domain₁ i)
    (hsub₂ : ∀ i ∈ s₂, ∀ p ∈ E₂ i, reader p = domain₂ i)
    (hcover₁ : ∀ᵐ p ∂μ, ∃ i ∈ s₁, p ∈ E₁ i)
    (hcover₂ : ∀ᵐ p ∂μ, ∃ i ∈ s₂, p ∈ E₂ i) :
    ∃ (ρ : Measure Ω) (S₁ : Finset ι₁) (S₂ : Finset ι₂),
      ρ ≤ μ ∧ μ univ ≤ ρ univ + ε * B ∧ S₁ ⊆ s₁ ∧ S₂ ⊆ s₂ ∧
      (∀ i ∈ S₁, ε * T (domain₁ i) ≤ ρ (E₁ i)) ∧
      (∀ i ∈ S₂, ε * T (domain₂ i) ≤ ρ (E₂ i)) ∧
      ∀ᵐ p ∂ρ, ∃ i ∈ S₁, ∃ j ∈ S₂,
        p ∈ E₁ i ∧ p ∈ E₂ j ∧ domain₁ i = reader p ∧ domain₂ j = reader p := by
  classical
  let E : ι₁ ⊕ ι₂ → Set Ω := Sum.elim E₁ E₂
  let w : ι₁ ⊕ ι₂ → ENNReal := Sum.elim (fun i => ε * T (domain₁ i)) (fun i => ε * T (domain₂ i))
  let layer : Bool → ι₁ ⊕ ι₂ → Prop := fun c i =>
    match i with
    | .inl _ => c = false
    | .inr _ => c = true
  have hE : ∀ i, MeasurableSet (E i) := by
    intro i
    cases i with
    | inl i => exact hE₁ i
    | inr i => exact hE₂ i
  have hcover : ∀ c, ∀ᵐ p ∂μ, ∃ i ∈ s₁.disjSum s₂, layer c i ∧ p ∈ E i := by
    intro c
    cases c
    · filter_upwards [hcover₁] with p hp
      obtain ⟨i, hi, hpi⟩ := hp
      exact ⟨.inl i, Finset.inl_mem_disjSum.mpr hi, rfl, hpi⟩
    · filter_upwards [hcover₂] with p hp
      obtain ⟨i, hi, hpi⟩ := hp
      exact ⟨.inr i, Finset.inr_mem_disjSum.mpr hi, rfl, hpi⟩
  obtain ⟨ρ, S, hρ, hloss, hS, hfloor, hc⟩ :=
    Submission.Lib.K4FinalLawSelection.simultaneous_floor_layers
      (s₁.disjSum s₂) E hE w μ layer hcover
  have hS₁ : S.toLeft ⊆ s₁ := by
    intro i hi
    exact Finset.inl_mem_disjSum.mp (hS (Finset.mem_toLeft.mp hi))
  have hS₂ : S.toRight ⊆ s₂ := by
    intro i hi
    exact Finset.inr_mem_disjSum.mp (hS (Finset.mem_toRight.mp hi))
  have hsum : (∑ i ∈ s₁.disjSum s₂, w i) ≤ ε * B := by
    rw [Finset.sum_disjSum]
    change (∑ i ∈ s₁, ε * T (domain₁ i)) + (∑ i ∈ s₂, ε * T (domain₂ i)) ≤ ε * B
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add]
    exact mul_le_mul' le_rfl hbudget
  refine ⟨ρ, S.toLeft, S.toRight, hρ, hloss.trans (add_le_add le_rfl hsum), hS₁, hS₂, ?_, ?_, ?_⟩
  · intro i hi
    exact hfloor (.inl i) (Finset.mem_toLeft.mp hi)
  · intro i hi
    exact hfloor (.inr i) (Finset.mem_toRight.mp hi)
  · filter_upwards [hc false, hc true] with p hp₁ hp₂
    obtain ⟨i, hi, hleft, hpi⟩ := hp₁
    obtain ⟨j, hj, hright, hpj⟩ := hp₂
    cases i with
    | inr i => simp [layer] at hleft
    | inl i =>
      cases j with
      | inl j => simp [layer] at hright
      | inr j =>
        have hi' : i ∈ S.toLeft := Finset.mem_toLeft.mpr hi
        have hj' : j ∈ S.toRight := Finset.mem_toRight.mpr hj
        exact ⟨i, hi', j, hj', hpi, hpj,
          (hsub₁ i (hS₁ hi') p hpi).symm, (hsub₂ j (hS₂ hj') p hpj).symm⟩

end Submission.Obl.k4_subcritical_endpoint_native_pairing
