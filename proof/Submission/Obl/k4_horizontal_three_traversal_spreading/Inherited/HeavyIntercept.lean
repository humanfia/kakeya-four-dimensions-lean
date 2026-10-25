-- Adapted from the same LOT tree, o201, session x0697, commit d395b4346c32c12a70c4bc86d657dea88e733fcd
-- Source: Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/HeavyIntercept.lean
-- Earlier source attribution is retained below.
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/HeavyIntercept.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Mathlib
import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation

/-! A heavy intercept from a pair-count budget and a conditional endpoint-cell cap. -/

namespace Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited

open Finset

/-- Sum the endpoint-cell cap over the actual occupied (intercept, cell) pairs.
All weights are kept in their original units. -/
theorem path_mass_le_occupied_pair_budget
    {Ω Bin Cell : Type*} [Fintype Ω] [DecidableEq Bin] [DecidableEq Cell]
    (P : Ω → ℝ) (W : Ω → Ω → ℝ) (bin : Ω → Bin) (cell : Ω → Cell)
    (F : Finset (Bin × Cell)) (p : ℝ) (hW : ∀ e e', 0 ≤ W e e')
    (hsupport : ∀ e e', 0 < W e e' → (bin e, cell e') ∈ F)
    (hcap : ∀ e t, (∑ e' ∈ univ.filter (fun e' => cell e' = t), W e e') ≤ p * P e) :
    (∑ e, ∑ e', W e e') ≤
      p * ∑ a ∈ F, ∑ e ∈ univ.filter (fun e => bin e = a.1), P e := by
  classical
  have hterm (e e' : Ω) : W e e' ≤
      ∑ a ∈ F, if bin e = a.1 ∧ cell e' = a.2 then W e e' else 0 := by
    by_cases hw : 0 < W e e'
    · have h := single_le_sum (f := fun a : Bin × Cell =>
          if bin e = a.1 ∧ cell e' = a.2 then W e e' else 0)
        (fun a ha => by split_ifs <;> positivity) (hsupport e e' hw)
      simpa using h
    · have hw0 : W e e' = 0 := le_antisymm (le_of_not_gt hw) (hW e e')
      simp [hw0]
  have hpair (a : Bin × Cell) :
      (∑ e, ∑ e', if bin e = a.1 ∧ cell e' = a.2 then W e e' else 0) ≤
        p * ∑ e ∈ univ.filter (fun e => bin e = a.1), P e := by
    calc
      _ = ∑ e, if bin e = a.1 then
          ∑ e' ∈ univ.filter (fun e' => cell e' = a.2), W e e' else 0 := by
        apply sum_congr rfl
        intro e _
        by_cases he : bin e = a.1 <;> simp [he, Finset.sum_filter]
      _ ≤ ∑ e, if bin e = a.1 then p * P e else 0 := by
        apply sum_le_sum
        intro e _
        split_ifs
        · exact hcap e a.2
        · exact le_rfl
      _ = _ := by
        rw [← sum_filter, mul_sum]
  calc
    _ ≤ ∑ e, ∑ e', ∑ a ∈ F,
        if bin e = a.1 ∧ cell e' = a.2 then W e e' else 0 :=
      sum_le_sum fun e _ => sum_le_sum fun e' _ => hterm e e'
    _ = ∑ a ∈ F, ∑ e, ∑ e',
        if bin e = a.1 ∧ cell e' = a.2 then W e e' else 0 := by
      simp only [sum_comm (s := univ) (t := F)]
    _ ≤ ∑ a ∈ F, p * ∑ e ∈ univ.filter (fun e => bin e = a.1), P e :=
      sum_le_sum fun a _ => hpair a
    _ = _ := by rw [mul_sum]

/-- Positive retained path mass and a finite occupied-pair budget force one
heavy original intercept bin. No probability normalization is required. -/
theorem exists_heavy_intercept_of_path_cell_cap
    {Ω Bin Cell : Type*} [Fintype Ω] [DecidableEq Bin] [DecidableEq Cell]
    (P : Ω → ℝ) (W : Ω → Ω → ℝ) (bin : Ω → Bin) (cell : Ω → Cell)
    (F : Finset (Bin × Cell)) (p B m : ℝ) (hp : 0 < p) (hB : 0 < B) (hm : 0 < m)
    (hW : ∀ e e', 0 ≤ W e e') (hcard : (F.card : ℝ) ≤ B)
    (hmass : m ≤ ∑ e, ∑ e', W e e')
    (hsupport : ∀ e e', 0 < W e e' → (bin e, cell e') ∈ F)
    (hcap : ∀ e t, (∑ e' ∈ univ.filter (fun e' => cell e' = t), W e e') ≤ p * P e) :
    ∃ b : Bin, m / (2 * p * B) ≤ ∑ e ∈ univ.filter (fun e => bin e = b), P e := by
  classical
  by_contra hno
  push Not at hno
  have hT : 0 ≤ m / (2 * p * B) := by positivity
  have hsum : (∑ a ∈ F, ∑ e ∈ univ.filter (fun e => bin e = a.1), P e) ≤
      B * (m / (2 * p * B)) := by
    calc
      _ ≤ ∑ _a ∈ F, m / (2 * p * B) := sum_le_sum fun a _ => (hno a.1).le
      _ = (F.card : ℝ) * (m / (2 * p * B)) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hT
  have hupper := (path_mass_le_occupied_pair_budget P W bin cell F p hW hsupport hcap).trans
    (mul_le_mul_of_nonneg_left hsum hp.le)
  have heq : p * (B * (m / (2 * p * B))) = m / 2 := by
    field_simp [hp.ne', hB.ne']
  rw [heq] at hupper
  linarith


/-- The midpoint bin of an affine signal gives a fit throughout the block. -/
theorem binned_affine_whole_block_fit
    (a E L t₀ u v : ℝ) (ha : 0 < a) (_hE : 0 ≤ E) (hL : 0 ≤ L) (hv : |v| ≤ E)
    (t : ℝ) (ht : t ∈ Set.Icc t₀ (t₀ + L)) :
    |u + t * v - a * (⌊(u + (t₀ + L / 2) * v) / a⌋ : ℝ)| ≤ E * L + a := by
  have hbin := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error ha
    (u + (t₀ + L / 2) * v)
  have htime : |t - (t₀ + L / 2)| ≤ L :=
    abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  calc
    _ = |(t - (t₀ + L / 2)) * v +
        (u + (t₀ + L / 2) * v - a * (⌊(u + (t₀ + L / 2) * v) / a⌋ : ℝ))| := by
      congr 1
      ring
    _ ≤ |(t - (t₀ + L / 2)) * v| +
        |u + (t₀ + L / 2) * v - a * (⌊(u + (t₀ + L / 2) * v) / a⌋ : ℝ)| :=
      abs_add_le _ _
    _ ≤ E * L + a := by
      apply add_le_add _ hbin
      rw [abs_mul, mul_comm E L]
      exact mul_le_mul htime hv (abs_nonneg _) hL

/-- The finite critical count produces one heavy affine offset, fitting on
whole trajectories in the selected block, in the original mass units. -/
theorem exists_heavy_whole_block_intercept
    {Ω Cell : Type*} [Fintype Ω] [DecidableEq Cell]
    (P : Ω → ℝ) (W : Ω → Ω → ℝ) (cell : Ω → Cell)
    (u v : Ω → ℝ) (a E L t₀ p B m : ℝ)
    (ha : 0 < a) (hE : 0 ≤ E) (hL : 0 ≤ L) (hp : 0 < p) (hB : 0 < B) (hm : 0 < m)
    (hv : ∀ e, |v e| ≤ E) (hW : ∀ e e', 0 ≤ W e e')
    (F : Finset (ℤ × Cell)) (hcard : (F.card : ℝ) ≤ B)
    (hmass : m ≤ ∑ e, ∑ e', W e e')
    (hsupport : ∀ e e', 0 < W e e' →
      (⌊(u e + (t₀ + L / 2) * v e) / a⌋, cell e') ∈ F)
    (hcap : ∀ e t, (∑ e' ∈ univ.filter (fun e' => cell e' = t), W e e') ≤ p * P e) :
    ∃ j : ℤ,
      m / (2 * p * B) ≤
        ∑ e ∈ univ.filter (fun e => ⌊(u e + (t₀ + L / 2) * v e) / a⌋ = j), P e ∧
      ∀ e, ⌊(u e + (t₀ + L / 2) * v e) / a⌋ = j →
        ∀ t ∈ Set.Icc t₀ (t₀ + L), |u e + t * v e - a * (j : ℝ)| ≤ E * L + a := by
  obtain ⟨j, hj⟩ := exists_heavy_intercept_of_path_cell_cap P W
    (fun e => ⌊(u e + (t₀ + L / 2) * v e) / a⌋) cell F p B m hp hB hm
    hW hcard hmass hsupport hcap
  refine ⟨j, hj, ?_⟩
  intro e he t ht
  simpa only [he] using binned_affine_whole_block_fit a E L t₀ (u e) (v e)
    ha hE hL (hv e) t ht

end Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited
