import Mathlib

namespace Submission.Obl.k4_scalar_capped_heavy_potential

noncomputable section

/-- Each occupied assigned base cell of a group has an actual joint
cell witness and one of finitely many rounding offsets. Lists at the
actual joint cells control the total number of group/base incidences. -/
theorem group_base_cell_budget {G B J O : Type*}
    [DecidableEq G] [DecidableEq B] [DecidableEq J] [DecidableEq O]
    (groups : Finset G) (base : G → Finset B) (joints : Finset J) (offsets : Finset O)
    (allowed : J → Finset G) (assigned : J → O → B) {D : ℝ}
    (hD : ∀ j ∈ joints, ((allowed j).card : ℝ) ≤ D)
    (hcover : ∀ g ∈ groups, ∀ b ∈ base g,
      ∃ j ∈ joints, ∃ o ∈ offsets, g ∈ allowed j ∧ b = assigned j o) :
    (∑ g ∈ groups, ((base g).card : ℝ)) ≤
      (joints.card : ℝ) * offsets.card * D := by
  classical
  let sources : Finset (G × B) := groups.biUnion fun g => (base g).image (Prod.mk g)
  let targets : Finset (G × B) := joints.biUnion fun j =>
    offsets.biUnion fun o => (allowed j).image (fun g => (g, assigned j o))
  have hcard : (sources.card : ℝ) = ∑ g ∈ groups, ((base g).card : ℝ) := by
    dsimp only [sources]
    rw [Finset.card_biUnion, Nat.cast_sum]
    · apply Finset.sum_congr rfl
      intro g hg
      rw [Finset.card_image_of_injective _ (by intro b b' h; exact (Prod.mk.inj h).2)]
    · intro g hg g' hg' hgg'
      apply Finset.disjoint_left.mpr
      intro p hp hp'
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨b', hb', heq⟩ := Finset.mem_image.mp hp'
      exact hgg' (Prod.mk.inj heq).1.symm
  have hsub : sources ⊆ targets := by
    intro p hp
    dsimp only [sources] at hp
    obtain ⟨g, hg, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, hj, o, ho, hgj, hbj⟩ := hcover g hg b hb
    apply Finset.mem_biUnion.mpr
    refine ⟨j, hj, Finset.mem_biUnion.mpr ⟨o, ho, ?_⟩⟩
    exact Finset.mem_image.mpr ⟨g, hgj, by simp [hbj]⟩
  have htarget : (targets.card : ℝ) ≤ (joints.card : ℝ) * offsets.card * D := by
    calc
      _ ≤ ∑ j ∈ joints, ((offsets.biUnion fun o =>
          (allowed j).image (fun g => (g, assigned j o))).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ j ∈ joints, ∑ _o ∈ offsets, ((allowed j).card : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          _ ≤ ∑ o ∈ offsets, (((allowed j).image (fun g => (g, assigned j o))).card : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
          _ ≤ _ := Finset.sum_le_sum fun o ho => Nat.cast_le.mpr Finset.card_image_le
      _ ≤ ∑ _j ∈ joints, ∑ _o ∈ offsets, D := by
        apply Finset.sum_le_sum
        intro j hj
        exact Finset.sum_le_sum fun o ho => hD j hj
      _ = _ := by simp; ring
  rw [← hcard]
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans htarget

end
end Submission.Obl.k4_scalar_capped_heavy_potential
