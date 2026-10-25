/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarHeavyGroups/GroupCounts.lean at aca48c1.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit af6b1867dfbb677a4a0e008effa5b557d8531e7f,
Submission/Obl/k4_scalar_mesh_projection/GroupCounts.lean.
-/

import Submission.Lib.K4IncidenceWitnesses

namespace Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching
open Set

/-- A common occupied-cell lower bound and a bounded overlap at each
original joint cell give a group count with no loss from group masses. -/
theorem group_count_of_row_floor_and_column_cap {I Z : Type*} [DecidableEq Z]
    (G : Finset I) (F : Finset Z) (T : I → Finset Z) (A L : ℝ)
    (hsub : ∀ i ∈ G, T i ⊆ F)
    (hrow : ∀ i ∈ G, A ≤ ((T i).card : ℝ))
    (hcol : ∀ z ∈ F, ((G.filter fun i => z ∈ T i).card : ℝ) ≤ L) :
    A * (G.card : ℝ) ≤ L * (F.card : ℝ) := by
  classical
  have hroweq (i : I) (hi : i ∈ G) :
      ∑ z ∈ F, (if z ∈ T i then (1 : ℝ) else 0) = ((T i).card : ℝ) := by
    have heq : F.filter (fun z => z ∈ T i) = T i := by
      ext z
      simp only [Finset.mem_filter]
      exact ⟨And.right, fun hz => ⟨hsub i hi hz, hz⟩⟩
    rw [← Finset.sum_filter, heq]
    simp
  calc
    _ = ∑ _i ∈ G, A := by simp [mul_comm]
    _ ≤ ∑ i ∈ G, ((T i).card : ℝ) := Finset.sum_le_sum hrow
    _ = ∑ i ∈ G, ∑ z ∈ F, (if z ∈ T i then (1 : ℝ) else 0) :=
      Finset.sum_congr rfl fun i hi => (hroweq i hi).symm
    _ = ∑ z ∈ F, ∑ i ∈ G, (if z ∈ T i then (1 : ℝ) else 0) := Finset.sum_comm
    _ = ∑ z ∈ F, ((G.filter fun i => z ∈ T i).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [← Finset.sum_filter]
      simp
    _ ≤ ∑ _z ∈ F, L := Finset.sum_le_sum hcol
    _ = L * (F.card : ℝ) := by simp [mul_comm]

/-- The accepted lattice packing lemma controls arbitrary finite integer
intercepts in a common real window. -/
theorem integer_intercepts_card_le (G : Finset ℤ) (a B : ℝ) (hB : 0 ≤ B)
    (hfit : ∀ C ∈ G, |(C : ℝ) - a| ≤ B) :
    (G.card : ℝ) ≤ 4 * B + 3 := by
  classical
  let f : ℤ → Fin 1 → ℤ := fun C _ => C
  have hinj : Function.Injective f := by
    intro i j hij
    exact congrFun hij 0
  have hdiam : ∀ p ∈ G.image f, ∀ q ∈ G.image f, ∀ j,
      |(p j : ℝ) - (q j : ℝ)| ≤ 2 * B := by
    intro p hp q hq j
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hq
    change |(i : ℝ) - (k : ℝ)| ≤ 2 * B
    have h := abs_sub_le (i : ℝ) a (k : ℝ)
    rw [abs_sub_comm a] at h
    linarith [hfit i hi, hfit k hk]
  have h := Submission.Lib.K4IncidenceWitnesses.card_pi_grid_of_diameter
    (G.image f) (by positivity : 0 ≤ 2 * B) hdiam
  have h' : (G.card : ℝ) ≤ 2 * (2 * B) + 3 := by
    simpa only [Finset.card_image_of_injective G hinj, Fintype.card_fin, pow_one] using h
  linarith

/-- One original joint cell can meet only boundedly many intercept groups.
The points witnessing different intercepts may all be different. -/
theorem intercept_groups_at_joint_cell_card_le {Z : Type*}
    (G : Finset ℤ) (P : Z → ℝ) (x₀ P₀ a E V : ℝ)
    (ha : 0 < a) (hE : 0 ≤ E) (hV : 0 ≤ V)
    (hwitness : ∀ C ∈ G, ∃ z : Z, ∃ x : ℝ,
      |x - x₀| ≤ a ∧ |P z - P₀| ≤ V * a ∧ |x - P z - a * (C : ℝ)| ≤ E * a) :
    (G.card : ℝ) ≤ 4 * E + 4 * V + 7 := by
  have hwindow : ∀ C ∈ G, |(C : ℝ) - (x₀ - P₀) / a| ≤ E + V + 1 := by
    intro C hC
    obtain ⟨z, x, hx, hP, hfit⟩ := hwitness C hC
    have hidentity : a * (C : ℝ) - (x₀ - P₀) =
        -(x - P z - a * (C : ℝ)) + (x - x₀) - (P z - P₀) := by ring
    have htri1 := abs_sub (-(x - P z - a * (C : ℝ)) + (x - x₀)) (P z - P₀)
    have htri2 := abs_add_le (-(x - P z - a * (C : ℝ))) (x - x₀)
    rw [← hidentity] at htri1
    rw [abs_neg] at htri2
    have hbound : |a * (C : ℝ) - (x₀ - P₀)| ≤ (E + V + 1) * a := by linarith
    have hid : (C : ℝ) - (x₀ - P₀) / a = (a * (C : ℝ) - (x₀ - P₀)) / a := by
      field_simp
    rw [hid, abs_div, abs_of_pos ha]
    exact (div_le_iff₀ ha).mpr hbound
  have h := integer_intercepts_card_le G ((x₀ - P₀) / a) (E + V + 1) (by positivity) hwindow
  linarith

end Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching
