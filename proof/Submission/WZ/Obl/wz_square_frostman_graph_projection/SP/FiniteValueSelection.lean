-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.FiniteValueSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped BigOperators

/-- A bounded nonnegative function with large sum has many values at
least half its average lower bound. -/
theorem finite_many_large_values {X : Type*} (S : Finset X) (f : X → ℝ)
    {M d : ℝ} (hM : 0 < M) (hd : 0 ≤ d)
    (hf : ∀ x ∈ S, 0 ≤ f x ∧ f x ≤ M)
    (hsum : d * M * (S.card : ℝ) ≤ ∑ x ∈ S, f x) :
    ∃ T : Finset X, T ⊆ S ∧ (d / 2) * (S.card : ℝ) ≤ (T.card : ℝ) ∧
      ∀ x ∈ T, (d / 2) * M ≤ f x := by
  classical
  let T := S.filter (fun x => (d / 2) * M ≤ f x)
  have hT : T ⊆ S := Finset.filter_subset _ _
  have hterm (x : X) (hx : x ∈ S) : f x ≤ (if x ∈ T then M else 0) + (d / 2) * M := by
    by_cases hxt : x ∈ T
    · rw [if_pos hxt]
      exact (hf x hx).2.trans (le_add_of_nonneg_right (by positivity))
    · rw [if_neg hxt, zero_add]
      exact le_of_lt (lt_of_not_ge (fun hh => hxt (Finset.mem_filter.mpr ⟨hx, hh⟩)))
  have hupper : (∑ x ∈ S, f x) ≤ (T.card : ℝ) * M + (S.card : ℝ) * ((d / 2) * M) := by
    have hh := Finset.sum_le_sum (fun x hx => hterm x hx)
    rw [Finset.sum_add_distrib, ← Finset.sum_filter] at hh
    have heq : S.filter (fun x => x ∈ T) = T := Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr hT)
    simpa only [heq, Finset.sum_const, nsmul_eq_mul] using hh
  refine ⟨T, hT, ?_, fun x hx => (Finset.mem_filter.mp hx).2⟩
  apply (mul_le_mul_iff_left₀ hM).mp
  nlinarith

/-- Markov's bound in a form with no divisions. -/
theorem finite_large_values_mass {X : Type*} (S : Finset X) (f : X → ℝ) (t : ℝ)
    (hf : ∀ x ∈ S, 0 ≤ f x) :
    t * ((S.filter (fun x => t ≤ f x)).card : ℝ) ≤ ∑ x ∈ S, f x := by
  classical
  let T := S.filter (fun x => t ≤ f x)
  calc
    t * (T.card : ℝ) = ∑ _x ∈ T, t := by simp; ring
    _ ≤ ∑ x ∈ T, f x := Finset.sum_le_sum (fun x hx => (Finset.mem_filter.mp hx).2)
    _ ≤ ∑ x ∈ S, f x := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x hx _ => hf x hx)

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
