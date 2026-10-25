import Submission.Obl.k4_tempered_grid_selection.SelectionSequence

namespace Submission.Obl.k4_marked_scalar_grid_selection

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- The countable type selection theorem applies when the atom spaces vary
with the scale. They embed measurably into their countable disjoint union. -/
theorem countable_type_selection_varying
    {Λ : ℕ → Type*} [∀ k, MeasurableSpace (Λ k)]
    [∀ k, Countable (Λ k)] [∀ k, MeasurableSingletonClass (Λ k)]
    (N : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (Λ k)) (f : (k : ℕ) → ℕ → Λ k → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ k j z, |f k j z| ≤ C) :
    ∃ (B : ℕ → ℕ) (T : (k : ℕ) → Set (Λ k))
      (a : ℕ → ℕ → ℝ) (δ : ℕ → ℝ),
      (∀ k, 0 < B k) ∧
      k4_tempered_grid_selection.Subpower N (fun k => (B k : ℝ)) ∧
      (∀ k j, |a k j| ≤ C) ∧
      (∀ k, 0 < δ k) ∧ Tendsto δ atTop (𝓝 0) ∧
      (∀ j, ∀ᶠ k in atTop, ∀ z ∈ T k, |f k j z - a k j| < δ k) ∧
      ∀ k, μ k univ ≤ (B k : ℝ≥0∞) * μ k (T k) := by
  classical
  letI : MeasurableSpace (Sigma Λ) := ⊤
  letI : MeasurableSingletonClass (Sigma Λ) := ⟨fun _ => trivial⟩
  let f' (k j : ℕ) (z : Sigma Λ) : ℝ :=
    if h : z.1 = k then f k j (h ▸ z.2) else 0
  have hf' (k j : ℕ) (z : Sigma Λ) : |f' k j z| ≤ C := by
    dsimp [f']
    split_ifs
    · exact hf _ _ _
    · simpa using hC
  obtain ⟨B, T', a, δ, hB, hBsub, ha, hδpos, hδ, hfit, hretain⟩ :=
    k4_tempered_grid_selection.countable_type_selection N hN hNt
      (fun k => (μ k).map (Sigma.mk k)) (fun _ z => z) f' C hC hf'
  let T (k : ℕ) : Set (Λ k) := Sigma.mk k ⁻¹' T' k
  refine ⟨B, T, a, δ, hB, hBsub, ha, hδpos, hδ, ?_, ?_⟩
  · intro j
    filter_upwards [hfit j] with k hk z hz
    have h := hk (Sigma.mk k z) hz
    simpa only [f', dif_pos rfl] using h
  · intro k
    have h := hretain k
    change (μ k).map (Sigma.mk k) univ ≤
      (B k : ℝ≥0∞) * (μ k).map (Sigma.mk k) (T' k) at h
    rw [Measure.map_apply (measurable_of_countable (Sigma.mk k)) MeasurableSet.univ,
      preimage_univ,
      Measure.map_apply (measurable_of_countable (Sigma.mk k)) (Set.to_countable (T' k)).measurableSet] at h
    exact h

end Submission.Obl.k4_marked_scalar_grid_selection
