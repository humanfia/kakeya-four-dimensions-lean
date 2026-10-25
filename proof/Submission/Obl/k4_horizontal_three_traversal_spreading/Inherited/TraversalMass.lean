-- Adapted from the same LOT tree, o201, session x0697, commit d395b4346c32c12a70c4bc86d657dea88e733fcd
-- Source: Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/TraversalMass.lean
-- Earlier source attribution is retained below.
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/TraversalMass.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited.FiniteTraversals

/-! Linearity, positivity and intercept support of the unnormalized finite path law. -/

namespace Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited

noncomputable section

open Finset Classical
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

variable {Ω Sf Sc Ar Iv Pal Tc : Type*} [Fintype Ω] [DecidableEq Sf]
  [DecidableEq Sc] [DecidableEq Ar] [DecidableEq Iv] [Fintype Pal] [DecidableEq Pal]
  [Fintype Tc] [DecidableEq Tc]

/-- The retained path expectation is a linear functional of its terminal test. -/
def finiteTraversalTerminalForm (X : SwitchData Ω Sf Sc Ar Iv Pal Tc)
    (prior : Bool → Ar → ℝ) (lam : ℝ)
    (allowed : Ω → List (Pal × Tc) → Ω → Ω → Prop) :
    ℕ → Ω → List (Pal × Tc) → ((Ω → List (Pal × Tc) → ℝ) →ₗ[ℝ] ℝ)
  | 0, e, l =>
      (LinearMap.proj l : (List (Pal × Tc) → ℝ) →ₗ[ℝ] ℝ).comp
        (LinearMap.proj e : (Ω → List (Pal × Tc) → ℝ) →ₗ[ℝ] (List (Pal × Tc) → ℝ))
  | n + 1, e, l => ∑ er, condKey X.P X.fine e er •
      (if X.heavy prior lam er false then
        ∑ e', condKey X.P (X.armKey false) er e' •
          (if allowed e l er e' then
            finiteTraversalTerminalForm X prior lam allowed n e' (l ++ [(X.Z er, X.cell e')])
            else 0) else 0)

theorem finiteTraversalTerminalForm_apply
    (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (prior : Bool → Ar → ℝ) (lam : ℝ)
    (allowed : Ω → List (Pal × Tc) → Ω → Ω → Prop)
    (τ : Ω → List (Pal × Tc) → ℝ) (n : ℕ) (e : Ω) (l : List (Pal × Tc)) :
    finiteTraversalTerminalForm X prior lam allowed n e l τ =
      finiteTraversalValue X prior lam allowed τ n e l := by
  induction n generalizing e l with
  | zero => rfl
  | succ n ih =>
    simp [finiteTraversalTerminalForm, finiteTraversalValue, ih, apply_ite, ite_apply,
      Pi.smul_apply, Finset.sum_apply]

theorem finiteTraversalValue_finset_sum
    {β : Type*} (X : SwitchData Ω Sf Sc Ar Iv Pal Tc)
    (prior : Bool → Ar → ℝ) (lam : ℝ)
    (allowed : Ω → List (Pal × Tc) → Ω → Ω → Prop)
    (B : Finset β) (τ : β → Ω → List (Pal × Tc) → ℝ)
    (n : ℕ) (e : Ω) (l : List (Pal × Tc)) :
    finiteTraversalValue X prior lam allowed (fun x h => ∑ b ∈ B, τ b x h) n e l =
      ∑ b ∈ B, finiteTraversalValue X prior lam allowed (τ b) n e l := by
  calc
    _ = finiteTraversalTerminalForm X prior lam allowed n e l (∑ b ∈ B, τ b) := by
      have hsum : (fun x h => ∑ b ∈ B, τ b x h) = ∑ b ∈ B, τ b := by
        ext x h
        simp only [Finset.sum_apply]
      rw [hsum]
      exact (finiteTraversalTerminalForm_apply X prior lam allowed (∑ b ∈ B, τ b) n e l).symm
    _ = ∑ b ∈ B, finiteTraversalTerminalForm X prior lam allowed n e l (τ b) := map_sum _ _ _
    _ = _ := by
      apply sum_congr rfl
      intro b _
      exact finiteTraversalTerminalForm_apply X prior lam allowed (τ b) n e l

theorem finiteTraversalValue_nonneg
    (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (hP : ∀ e, 0 ≤ X.P e)
    (prior : Bool → Ar → ℝ) (lam : ℝ)
    (allowed : Ω → List (Pal × Tc) → Ω → Ω → Prop)
    (τ : Ω → List (Pal × Tc) → ℝ) (hτ : ∀ e l, 0 ≤ τ e l) :
    ∀ n e l, 0 ≤ finiteTraversalValue X prior lam allowed τ n e l := by
  intro n
  induction n with
  | zero => exact hτ
  | succ n ih =>
    intro e l
    apply sum_nonneg
    intro er _
    apply mul_nonneg (condKey_nonneg hP X.fine e er)
    split_ifs
    · apply sum_nonneg
      intro e' _
      apply mul_nonneg (condKey_nonneg hP (X.armKey false) er e')
      split_ifs
      · exact ih e' _
      · exact le_rfl
    · exact le_rfl

/-- A label that is determined by both the refresh state and the trajectory
key remains fixed through every retained path. -/
theorem finiteTraversalValue_zero_off_bin
    {Bin : Type*} (X : SwitchData Ω Sf Sc Ar Iv Pal Tc)
    (prior : Bool → Ar → ℝ) (lam : ℝ)
    (allowed : Ω → List (Pal × Tc) → Ω → Ω → Prop)
    (bin : Ω → Bin) (b : Bin)
    (hfine : ∀ e er, X.fine e = X.fine er → bin e = bin er)
    (hline : ∀ er e', X.armKey false er = X.armKey false e' → bin er = bin e')
    (τ : Ω → List (Pal × Tc) → ℝ)
    (hτ : ∀ e l, bin e ≠ b → τ e l = 0) :
    ∀ n e l, bin e ≠ b → finiteTraversalValue X prior lam allowed τ n e l = 0 := by
  intro n
  induction n with
  | zero => exact hτ
  | succ n ih =>
    intro e l hbe
    apply sum_eq_zero
    intro er _
    by_cases hf : condKey X.P X.fine e er = 0
    · simp [hf]
    have hber : bin er = bin e := hfine er e (condKey_key_eq X.fine hf)
    have hber' : bin er ≠ b := by rwa [hber]
    by_cases hh : X.heavy prior lam er false
    · rw [ite_eq_left hh]
      apply mul_eq_zero_of_right
      apply sum_eq_zero
      intro e' _
      by_cases hl : condKey X.P (X.armKey false) er e' = 0
      · simp [hl]
      have hbe' : bin e' = bin er := hline e' er (condKey_key_eq (X.armKey false) hl)
      have hbe'' : bin e' ≠ b := by rwa [hbe']
      split_ifs
      · rw [ih e' _ hbe'']
        exact mul_zero _
      · exact mul_zero _
    · simp [hh]


/-- Summing terminal atoms gives the terminal event, including its retained test. -/
theorem finiteTraversalValue_endpoint_sum
    (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (prior : Bool → Ar → ℝ) (lam : ℝ)
    (allowed : Ω → List (Pal × Tc) → Ω → Ω → Prop)
    (G : Ω → List (Pal × Tc) → ℝ) (B : Finset Ω)
    (n : ℕ) (e : Ω) (l : List (Pal × Tc)) :
    (∑ e' ∈ B, finiteTraversalValue X prior lam allowed
      (fun x h => if x = e' then G x h else 0) n e l) =
      finiteTraversalValue X prior lam allowed
        (fun x h => if x ∈ B then G x h else 0) n e l := by
  calc
    _ = finiteTraversalValue X prior lam allowed
        (fun x h => ∑ e' ∈ B, if x = e' then G x h else 0) n e l :=
      (finiteTraversalValue_finset_sum X prior lam allowed B
        (fun e' x h => if x = e' then G x h else 0) n e l).symm
    _ = _ := by
      congr 1
      funext x h
      simp

/-- Original starting weight times the retained conditional path law. -/
def finiteTraversalMatrix (X : SwitchData Ω Sf Sc Ar Iv Pal Tc)
    (prior : Bool → Ar → ℝ) (lam : ℝ)
    (allowed : Ω → List (Pal × Tc) → Ω → Ω → Prop)
    (G : Ω → List (Pal × Tc) → ℝ) (n : ℕ) (e e' : Ω) : ℝ :=
  X.P e * finiteTraversalValue X prior lam allowed
    (fun x h => if x = e' then G x h else 0) n e []

theorem finiteTraversalMatrix_cell_sum
    {Cell : Type*} [DecidableEq Cell]
    (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (prior : Bool → Ar → ℝ) (lam : ℝ)
    (allowed : Ω → List (Pal × Tc) → Ω → Ω → Prop)
    (G : Ω → List (Pal × Tc) → ℝ) (cell : Ω → Cell) (n : ℕ) (e : Ω) (t : Cell) :
    (∑ e' ∈ univ.filter (fun e' => cell e' = t),
      finiteTraversalMatrix X prior lam allowed G n e e') =
      X.P e * finiteTraversalValue X prior lam allowed
        (fun x h => if cell x = t then G x h else 0) n e [] := by
  simp only [finiteTraversalMatrix, ← mul_sum, finiteTraversalValue_endpoint_sum,
    mem_filter, mem_univ, true_and]

theorem finiteTraversalMatrix_total
    (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (prior : Bool → Ar → ℝ) (lam : ℝ)
    (allowed : Ω → List (Pal × Tc) → Ω → Ω → Prop)
    (G : Ω → List (Pal × Tc) → ℝ) (n : ℕ) :
    (∑ e, ∑ e', finiteTraversalMatrix X prior lam allowed G n e e') =
      ∑ e, X.P e * finiteTraversalValue X prior lam allowed G n e [] := by
  apply sum_congr rfl
  intro e _
  simp only [finiteTraversalMatrix, ← mul_sum, finiteTraversalValue_endpoint_sum,
    mem_univ, ite_true]

theorem finiteTraversalMatrix_nonneg
    (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (hP : ∀ e, 0 ≤ X.P e)
    (prior : Bool → Ar → ℝ) (lam : ℝ)
    (allowed : Ω → List (Pal × Tc) → Ω → Ω → Prop)
    (G : Ω → List (Pal × Tc) → ℝ) (hG : ∀ e l, 0 ≤ G e l)
    (n : ℕ) (e e' : Ω) : 0 ≤ finiteTraversalMatrix X prior lam allowed G n e e' := by
  apply mul_nonneg (hP e)
  apply finiteTraversalValue_nonneg X hP prior lam allowed _ _ n e []
  intro x h
  split_ifs
  · exact hG x h
  · exact le_rfl

theorem finiteTraversalMatrix_bin_eq_of_pos
    {Bin : Type*} (X : SwitchData Ω Sf Sc Ar Iv Pal Tc)
    (prior : Bool → Ar → ℝ) (lam : ℝ)
    (allowed : Ω → List (Pal × Tc) → Ω → Ω → Prop)
    (bin : Ω → Bin)
    (hfine : ∀ e er, X.fine e = X.fine er → bin e = bin er)
    (hline : ∀ er e', X.armKey false er = X.armKey false e' → bin er = bin e')
    (G : Ω → List (Pal × Tc) → ℝ) (n : ℕ) (e e' : Ω)
    (hpos : 0 < finiteTraversalMatrix X prior lam allowed G n e e') : bin e = bin e' := by
  by_contra hne
  have hτ : ∀ x l, bin x ≠ bin e' → (if x = e' then G x l else 0) = 0 := by
    intro x l hx
    by_cases he : x = e'
    · subst x
      exact (hx rfl).elim
    · simp [he]
  have hz := finiteTraversalValue_zero_off_bin X prior lam allowed bin (bin e') hfine hline
    (fun x h => if x = e' then G x h else 0) hτ n e [] hne
  simp only [finiteTraversalMatrix, hz, mul_zero, lt_self_iff_false] at hpos

end

end Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited
