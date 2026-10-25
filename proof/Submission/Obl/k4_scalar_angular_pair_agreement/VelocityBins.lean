import Submission.Lib.K4WeightedCellEnergy

namespace Submission.Obl.k4_scalar_angular_pair_agreement

open Set

/-- Without three separated velocities, two short intervals cover the velocity set. -/
theorem no_three_separated_cover_two (S : Set ℝ) {w : ℝ} (_hw : 0 < w)
    (hnot : ∀ s₀ ∈ S, ∀ s₁ ∈ S, ∀ s₂ ∈ S,
      w ≤ |s₀ - s₁| → w ≤ |s₀ - s₂| → w ≤ |s₁ - s₂| → False) :
    ∃ v₀ v₁ : ℝ, ∀ s ∈ S, |s - v₀| < w ∨ |s - v₁| < w := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨s₀, hs₀⟩ := hS
    by_cases hone : ∀ s ∈ S, |s - s₀| < w
    · exact ⟨s₀, s₀, fun s hs => Or.inl (hone s hs)⟩
    push Not at hone
    obtain ⟨s₁, hs₁, h01⟩ := hone
    refine ⟨s₀, s₁, ?_⟩
    intro s₂ hs₂
    by_contra h
    push Not at h
    apply hnot s₀ hs₀ s₁ hs₁ s₂ hs₂
    · simpa only [abs_sub_comm] using h01
    · simpa only [abs_sub_comm] using h.1
    · simpa only [abs_sub_comm] using h.2
  · exact ⟨0, 0, fun s hs => (hS ⟨s, hs⟩).elim⟩

/-- The same confinement gives at most six actual angular floor bins. -/
theorem no_three_separated_velocity_bins (S : Set ℝ) {w : ℝ} (hw : 0 < w)
    (hnot : ∀ s₀ ∈ S, ∀ s₁ ∈ S, ∀ s₂ ∈ S,
      w ≤ |s₀ - s₁| → w ≤ |s₀ - s₂| → w ≤ |s₁ - s₂| → False) :
    ∃ F : Finset ℤ, F.card ≤ 6 ∧ ∀ s ∈ S, ⌊s / w⌋ ∈ F := by
  classical
  obtain ⟨v₀, v₁, hcover⟩ := no_three_separated_cover_two S hw hnot
  let B : ℝ → Finset ℤ := fun v => {⌊v / w⌋ - 1, ⌊v / w⌋, ⌊v / w⌋ + 1}
  have hB (v : ℝ) : (B v).card ≤ 3 := by
    calc
      (B v).card ≤ ({⌊v / w⌋, ⌊v / w⌋ + 1} : Finset ℤ).card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ (({⌊v / w⌋ + 1} : Finset ℤ).card + 1) + 1 :=
        Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ = 3 := by simp only [Finset.card_singleton]
  have hmem (s v : ℝ) (hsv : |s - v| < w) : ⌊s / w⌋ ∈ B v := by
    have hnear := Submission.Lib.K4WeightedCellEnergy.floor_neighbor_of_dist_le hw hsv.le
    dsimp [B]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  refine ⟨B v₀ ∪ B v₁, ?_, ?_⟩
  · exact (Finset.card_union_le _ _).trans (by have := hB v₀; have := hB v₁; omega)
  · intro s hs
    rcases hcover s hs with h | h
    · exact Finset.mem_union.mpr (Or.inl (hmem s v₀ h))
    · exact Finset.mem_union.mpr (Or.inr (hmem s v₁ h))

end Submission.Obl.k4_scalar_angular_pair_agreement
