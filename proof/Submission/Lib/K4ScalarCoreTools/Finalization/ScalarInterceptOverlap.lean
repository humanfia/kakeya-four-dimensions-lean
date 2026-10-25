/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarFinalization/ScalarInterceptOverlap.lean at 34bf057964440b5ed25e8d148b45315a2683e87d.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: o062/x0511,057175d1, ScalarInterceptOverlap.lean.
The inline equal-bin diameter step applies Mathlib Int.abs_sub_lt_one_of_floor_eq_floor directly.
-/

import Submission.Lib.K4ScalarCoreTools.Finalization.InterceptAssignments
import Submission.Lib.K4ScalarCoreTools.Simulation.PolynomialVariation
import Submission.Lib.K4ScalarCoreTools.HeavyGroups.GroupCounts

namespace Submission.Lib.K4ScalarCoreTools.Finalization

open Set MvPolynomial
open Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching
open Submission.Lib.K4ScalarCoreTools.Simulation.Switching

noncomputable section

/-- A fine base cell and an original hidden bin meet only `O(K)` final
intercept groups. The base cell radius may include a rounding error. -/
theorem exists_scalar_intercept_cell_overlap_constant :
    ∃ L : ℝ, 0 < L ∧ ∀ (U : Set (Fin 5 → ℝ)) (Q : MvPolynomial (Fin 2) ℝ),
      Q.totalDegree ≤ 2 → ∀ a h scale E K σ : ℝ,
      0 < h → 0 < scale → 1 ≤ K → 0 < σ → σ ≤ scale → 0 ≤ E → E ≤ K * scale →
      (∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z Q| ≤ K) →
      ∀ (center : Fin 2 → ℝ) (j : ℤ) (G : Finset ℤ),
      (∀ C ∈ G, ∃ b : Fin 5 → ℝ, ∃ t : ℝ,
        b ∈ interceptAssignment U Q a h scale E C ∧ t ∈ Icc a (a + h) ∧
        (![t, scalarY b t] : Fin 2 → ℝ) ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧
        (∀ d : Fin 2, |(![t, scalarY b t] : Fin 2 → ℝ) d - center d| ≤ σ) ∧
        ⌊scalarX b t / scale⌋ = j) →
      (G.card : ℝ) ≤ L * K := by
  classical
  obtain ⟨V, hV, hvariation⟩ := exists_symmetric_square_variation_constant 2
  refine ⟨41 + 16 * V, by positivity, ?_⟩
  intro U Q hQ a h scale E K σ hh hscale hK hσ hσscale hE hEK hnorm center j G hwitness
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  by_cases hG : G.Nonempty
  · obtain ⟨C₀, hC₀⟩ := hG
    obtain ⟨b₀, t₀, hb₀, ht₀, hz₀, hdist₀, hbin₀⟩ := hwitness C₀ hC₀
    let z₀ : Fin 2 → ℝ := ![t₀, scalarY b₀ t₀]
    have hcount : (G.card : ℝ) ≤ 4 * (8 * K + 1 / 2) + 4 * (4 * V * K) + 7 := by
      apply intercept_groups_at_joint_cell_card_le G
        (fun z : Fin 2 → ℝ => eval z Q) (scalarX b₀ t₀) (eval z₀ Q)
        scale (8 * K + 1 / 2) (4 * V * K) hscale (by positivity) (by positivity)
      intro C hC
      obtain ⟨b, t, hb, ht, hz, hdist, hbin⟩ := hwitness C hC
      let z : Fin 2 → ℝ := ![t, scalarY b t]
      have hpair (d : Fin 2) : |z d - z₀ d| ≤ 2 * σ := by
        calc
          _ ≤ |z d - center d| + |center d - z₀ d| := abs_sub_le _ _ _
          _ ≤ σ + σ := add_le_add (hdist d) (by simpa only [abs_sub_comm] using hdist₀ d)
          _ = 2 * σ := by ring
      have hpoly : |eval z Q - eval z₀ Q| ≤ (4 * V * K) * scale := by
        calc
          _ ≤ V * K * (|z 0 - z₀ 0| + |z 1 - z₀ 1|) :=
            hvariation Q hQ K hK0 hnorm z₀ hz₀ z hz
          _ ≤ V * K * (4 * σ) := mul_le_mul_of_nonneg_left
            (by linarith [hpair 0, hpair 1]) (by positivity)
          _ = (4 * V * K) * σ := by ring
          _ ≤ (4 * V * K) * scale := mul_le_mul_of_nonneg_left hσscale (by positivity)
      have hfit : |scalarX b t - eval z Q - interceptCenter scale C| ≤ 8 * E := by
        simpa [z, interceptPredictor, sub_add_eq_sub_sub] using
          interceptAssignment_fit U Q hQ hh C hb ht
      refine ⟨z, scalarX b t, ?_, hpoly, ?_⟩
      · have hd := Int.abs_sub_lt_one_of_floor_eq_floor (hbin.trans hbin₀.symm)
        rw [← sub_div, abs_div, abs_of_pos hscale] at hd
        exact ((div_lt_one hscale).mp hd).le
      · calc
          |scalarX b t - eval z Q - scale * (C : ℝ)| =
              |(scalarX b t - eval z Q - interceptCenter scale C) + scale / 2| := by
                congr 1
                dsimp [interceptCenter]
                ring
          _ ≤ |scalarX b t - eval z Q - interceptCenter scale C| + |scale / 2| :=
            abs_add_le _ _
          _ ≤ 8 * E + scale / 2 := add_le_add hfit (le_of_eq (abs_of_nonneg (by positivity)))
          _ ≤ (8 * K + 1 / 2) * scale := by nlinarith
    nlinarith
  · have hG' : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hG
    simpa [hG'] using (mul_nonneg (by positivity : 0 ≤ 41 + 16 * V) hK0)

/-- Original cell witnesses supply the column cap in the group-counting
argument; no separate bounded-overlap hypothesis is needed. -/
theorem exists_scalar_assignment_group_count_constant :
    ∃ L : ℝ, 0 < L ∧ ∀ (U : Set (Fin 5 → ℝ)) (Q : MvPolynomial (Fin 2) ℝ),
      Q.totalDegree ≤ 2 → ∀ a h scale E K σ : ℝ,
      0 < h → 0 < scale → 1 ≤ K → 0 < σ → σ ≤ scale → 0 ≤ E → E ≤ K * scale →
      (∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z Q| ≤ K) →
      ∀ (Z : Type*) [DecidableEq Z] (F : Finset Z) (G : Finset ℤ) (T : ℤ → Finset Z)
        (center : Z → Fin 2 → ℝ) (label : Z → ℤ) (A : ℝ),
      (∀ C ∈ G, T C ⊆ F) → (∀ C ∈ G, A ≤ ((T C).card : ℝ)) →
      (∀ C ∈ G, ∀ z ∈ T C, ∃ b : Fin 5 → ℝ, ∃ t : ℝ,
        b ∈ interceptAssignment U Q a h scale E C ∧ t ∈ Icc a (a + h) ∧
        (![t, scalarY b t] : Fin 2 → ℝ) ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧
        (∀ d : Fin 2, |(![t, scalarY b t] : Fin 2 → ℝ) d - center z d| ≤ σ) ∧
        ⌊scalarX b t / scale⌋ = label z) →
      A * (G.card : ℝ) ≤ L * K * (F.card : ℝ) := by
  classical
  obtain ⟨L, hL, hoverlap⟩ := exists_scalar_intercept_cell_overlap_constant
  refine ⟨L, hL, ?_⟩
  intro U Q hQ a h scale E K σ hh hscale hK hσ hσscale hE hEK hnorm
    Z _ F G T center label A hsub hrow hwitness
  apply group_count_of_row_floor_and_column_cap G F T A (L * K) hsub hrow
  intro z hz
  apply hoverlap U Q hQ a h scale E K σ hh hscale hK hσ hσscale hE hEK hnorm
    (center z) (label z) (G.filter fun C => z ∈ T C)
  intro C hC
  obtain ⟨hCG, hzT⟩ := Finset.mem_filter.mp hC
  exact hwitness C hCG z hzT

/-- The physical Kakeya area floor and the original support budget give
an explicit bound on the number of geometric intercept groups. Counting
joint cells retains the base-cell floor through its projection. -/
theorem exists_scalar_heavy_assignment_count_constant :
    ∃ L : ℝ, 0 < L ∧ ∀ (U : Set (Fin 5 → ℝ)) (Q : MvPolynomial (Fin 2) ℝ),
      Q.totalDegree ≤ 2 → ∀ a h scale E K σ Cmk budget : ℝ,
      0 < h → 0 < scale → 1 ≤ K → 0 < σ → σ ≤ scale → 0 ≤ E → E ≤ K * scale →
      0 < Cmk → (∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z Q| ≤ K) →
      ∀ (Z B : Type*) [DecidableEq Z] [DecidableEq B] (base : Z → B)
        (F : Finset Z) (G : Finset ℤ) (T : ℤ → Finset Z)
        (center : Z → Fin 2 → ℝ) (label : Z → ℤ),
      (∀ C ∈ G, T C ⊆ F) →
      (∀ C ∈ G, 1 / (65536 * Cmk * K ^ 8) ≤ ((T C).image base).card * σ ^ 2) →
      (F.card : ℝ) * σ ^ 2 ≤ K * budget →
      (∀ C ∈ G, ∀ z ∈ T C, ∃ b : Fin 5 → ℝ, ∃ t : ℝ,
        b ∈ interceptAssignment U Q a h scale E C ∧ t ∈ Icc a (a + h) ∧
        (![t, scalarY b t] : Fin 2 → ℝ) ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧
        (∀ d : Fin 2, |(![t, scalarY b t] : Fin 2 → ℝ) d - center z d| ≤ σ) ∧
        ⌊scalarX b t / scale⌋ = label z) →
      (G.card : ℝ) ≤ 65536 * Cmk * L * K ^ 10 * budget := by
  classical
  obtain ⟨L, hL, hgroups⟩ := exists_scalar_assignment_group_count_constant
  refine ⟨L, hL, ?_⟩
  intro U Q hQ a h scale E K σ Cmk budget hh hscale hK hσ hσscale hE hEK hCmk hnorm
    Z B _ _ base F G T center label hsub hrow hbudget hwitness
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hσsq : 0 < σ ^ 2 := sq_pos_of_pos hσ
  have hden : 0 < 65536 * Cmk * K ^ 8 * σ ^ 2 := by positivity
  have hrow' (C : ℤ) (hC : C ∈ G) :
      1 / (65536 * Cmk * K ^ 8 * σ ^ 2) ≤ ((T C).card : ℝ) := by
    have hc : (((T C).image base).card : ℝ) ≤ ((T C).card : ℝ) := by
      exact_mod_cast Finset.card_image_le (s := T C) (f := base)
    have hr := ((div_le_iff₀ hσsq).mpr (hrow C hC)).trans hc
    simpa only [div_div] using hr
  have hn := hgroups U Q hQ a h scale E K σ hh hscale hK hσ hσscale hE hEK hnorm
    Z F G T center label (1 / (65536 * Cmk * K ^ 8 * σ ^ 2)) hsub hrow' hwitness
  have hn' : (G.card : ℝ) / (65536 * Cmk * K ^ 8 * σ ^ 2) ≤ L * K * (F.card : ℝ) := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hn
  calc
    (G.card : ℝ) ≤ (L * K * (F.card : ℝ)) * (65536 * Cmk * K ^ 8 * σ ^ 2) :=
      (div_le_iff₀ hden).mp hn'
    _ = 65536 * Cmk * L * K ^ 9 * ((F.card : ℝ) * σ ^ 2) := by ring
    _ ≤ 65536 * Cmk * L * K ^ 9 * (K * budget) :=
      mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = 65536 * Cmk * L * K ^ 10 * budget := by ring

end

end Submission.Lib.K4ScalarCoreTools.Finalization
