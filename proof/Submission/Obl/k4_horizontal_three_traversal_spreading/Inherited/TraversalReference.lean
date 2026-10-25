-- Adapted from the same LOT tree, o201, session x0697, commit d395b4346c32c12a70c4bc86d657dea88e733fcd
-- Source: Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/TraversalReference.lean
-- Earlier source attribution is retained below.
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/TraversalReference.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited.FiniteTraversals

/-! Independent palette/time expansion of the finite traversal reference law. -/

namespace Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited

noncomputable section

open Finset Classical
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

variable {Pal Tc : Type*} [Fintype Pal] [DecidableEq Pal] [Fintype Tc] [DecidableEq Tc]

/-- The reference recursion is the independent product law on all records. -/
theorem finiteTraversalFree_eq_record_sum (π : Pal → ℝ) (a : ℝ)
    (F : List (Pal × Tc) → ℝ) :
    ∀ n l, finiteTraversalFree π a F n l =
      a ^ n * ∑ rs : Fin n → Pal × Tc, (∏ i, π (rs i).1) * F (l ++ List.ofFn rs) := by
  intro n
  induction n with
  | zero =>
    intro l
    simp [finiteTraversalFree]
  | succ n ih =>
    intro l
    have hpair (G : Pal × Tc → ℝ) :
        (∑ z, π z * ∑ t, G (z, t)) = ∑ r : Pal × Tc, π r.1 * G r := by
      simp only [Fintype.sum_prod_type, mul_sum]
    rw [finiteTraversalFree, hpair (fun r => finiteTraversalFree π a F n (l ++ [r]))]
    simp_rw [ih]
    conv_rhs => rw [sum_fin_succ_fun]
    conv_lhs => rw [mul_sum]
    conv_rhs => rw [mul_sum]
    apply sum_congr rfl
    intro r _
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, List.ofFn_succ,
      List.append_assoc, List.singleton_append]
    simp_rw [mul_sum]
    apply sum_congr rfl
    intro rs _
    rw [pow_succ]
    ring

/-- First choose the entire palette tuple, then sum over the time-cell tuple. -/
theorem finiteTraversalFree_eq_palette_sum (π : Pal → ℝ) (a : ℝ)
    (F : List (Pal × Tc) → ℝ) (n : ℕ) (l : List (Pal × Tc)) :
    finiteTraversalFree π a F n l =
      a ^ n * ∑ zs : Fin n → Pal, (∏ i, π (zs i)) *
        ∑ ts : Fin n → Tc, F (l ++ List.ofFn (fun i => (zs i, ts i))) := by
  rw [finiteTraversalFree_eq_record_sum]
  congr 1
  let e := Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Pal) (fun _ => Tc)
  have he := e.symm.sum_comp (fun rs : Fin n → Pal × Tc =>
    (∏ i, π (rs i).1) * F (l ++ List.ofFn rs))
  rw [← he]
  simp only [e, Equiv.arrowProdEquivProdArrow_symm_apply, Fintype.sum_prod_type, mul_sum]
  rfl

/-- A uniform bound for every fixed-control time count also bounds the
independent reference expectation. -/
theorem finiteTraversalFree_le_time_count
    (π : Pal → ℝ) (a : ℝ) (F : List (Pal × Tc) → ℝ)
    (hπ : ∀ z, 0 ≤ π z) (hπ1 : ∑ z, π z = 1) (ha : 0 ≤ a)
    (n : ℕ) (l : List (Pal × Tc)) (B : ℝ)
    (hcount : ∀ zs : Fin n → Pal,
      (∑ ts : Fin n → Tc, F (l ++ List.ofFn (fun i => (zs i, ts i)))) ≤ B) :
    finiteTraversalFree π a F n l ≤ a ^ n * B := by
  have hw : ∑ zs : Fin n → Pal, ∏ i, π (zs i) = 1 := by
    rw [← Fintype.sum_pow, hπ1, one_pow]
  rw [finiteTraversalFree_eq_palette_sum]
  calc
    _ ≤ a ^ n * ∑ zs : Fin n → Pal, (∏ i, π (zs i)) * B := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg ha n)
      apply sum_le_sum
      intro zs _
      exact mul_le_mul_of_nonneg_left (hcount zs) (prod_nonneg fun i _ => hπ _)
    _ = _ := by rw [← sum_mul, hw, one_mul]

/-- A finite collection of reference palette atoms may have mass below one;
there is no need to add an artificial atom for the omitted tail. -/
theorem finiteTraversalFree_le_time_count_subprob
    (π : Pal → ℝ) (a : ℝ) (F : List (Pal × Tc) → ℝ)
    (hπ : ∀ z, 0 ≤ π z) (hπ1 : ∑ z, π z ≤ 1) (ha : 0 ≤ a)
    (n : ℕ) (l : List (Pal × Tc)) (B : ℝ) (hB : 0 ≤ B)
    (hcount : ∀ zs : Fin n → Pal,
      (∑ ts : Fin n → Tc, F (l ++ List.ofFn (fun i => (zs i, ts i)))) ≤ B) :
    finiteTraversalFree π a F n l ≤ a ^ n * B := by
  have hw : ∑ zs : Fin n → Pal, ∏ i, π (zs i) ≤ 1 := by
    rw [← Fintype.sum_pow]
    exact pow_le_one₀ (sum_nonneg fun z _ => hπ z) hπ1
  rw [finiteTraversalFree_eq_palette_sum]
  calc
    _ ≤ a ^ n * ∑ zs : Fin n → Pal, (∏ i, π (zs i)) * B := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg ha n)
      apply sum_le_sum
      intro zs _
      exact mul_le_mul_of_nonneg_left (hcount zs) (prod_nonneg fun i _ => hπ _)
    _ = a ^ n * ((∑ zs : Fin n → Pal, ∏ i, π (zs i)) * B) := by rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hw hB) (pow_nonneg ha n)

end

end Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited
