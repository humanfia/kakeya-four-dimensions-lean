/-
Adapted from: here:o064
Original proofs by session x0217 in this workspace. Uses the accepted
K4OriginalLists and K4ModelReduction APIs for paper Lemma a03:actual-lists.
-/

import Submission.Lib.K4MeshListRecovery.CoarseLists

/-!
Turn a finite rectangular mesh table into an observable finite code, including
an overflow code.  Combined with the accepted averaging APIs this is the
original-law recovery step for any finite-dimensional base.
-/

namespace Submission.Lib.K4MeshListRecovery

open Finset MeasureTheory Set
open Submission.Lib.K4OriginalLists

/-- Keep a genuine finite table code, and use one overflow code off its finite support. -/
noncomputable def finiteObservedCode {X τ : Type*} (F : Finset τ) (tag : X → τ)
    (x : X) : Option F := by
  classical
  exact if h : tag x ∈ F then some ⟨tag x, h⟩ else none

theorem finiteObservedCode_eq_none {X τ : Type*} (F : Finset τ) (tag : X → τ) (x : X) :
    finiteObservedCode F tag x = none ↔ tag x ∉ F := by
  classical
  by_cases h : tag x ∈ F <;> simp [finiteObservedCode, h]

theorem finiteObservedCode_eq_some {X τ : Type*} (F : Finset τ) (tag : X → τ)
    (x : X) (c : F) : finiteObservedCode F tag x = some c ↔ tag x = c.val := by
  classical
  by_cases h : tag x ∈ F
  · simp [finiteObservedCode, h, Subtype.ext_iff]
  · have hne : tag x ≠ c.val := by
      intro heq
      apply h
      simpa only [heq] using c.property
    simp [finiteObservedCode, h, hne]

theorem measurableSet_finiteObservedCode {X τ : Type*} [MeasurableSpace X]
    (F : Finset τ) (tag : X → τ) (htag : ∀ c, MeasurableSet {x | tag x = c})
    (j : Option F) : MeasurableSet {x | finiteObservedCode F tag x = j} := by
  classical
  have hmem : MeasurableSet {x | tag x ∈ F} := by
    convert F.measurableSet_biUnion (fun c _ => htag c) using 1
    ext x
    simp
  cases j with
  | none => simpa only [finiteObservedCode_eq_none, Set.compl_ofPred] using hmem.compl
  | some c => simpa only [finiteObservedCode_eq_some] using htag c.val

/-- A sparse mesh representation is evaluation of one finite table at the observed code. -/
theorem sparse_table_at_observed_code {X τ : Type*} [DecidableEq τ]
    (F : Finset τ) (tag : X → τ) (v : τ → ℝ) (x : X) :
    (∑ c ∈ F, if tag x = c then v c else 0) =
      (finiteObservedCode F tag x).elim 0 (fun c => v c.val) := by
  classical
  by_cases h : tag x ∈ F <;> simp [finiteObservedCode, h]

/-- A finite sparse approximation yields a table retaining only base-cell and observed tags.
Neither the analytical mask nor the fine list rule enters the table's finite code. -/
theorem recover_original_sparse_table
    {X τ o β : Type*} [MeasurableSpace X] [DecidableEq τ] [Fintype o] [Fintype β]
    (μ : Measure X) (F : Finset τ) (tag : X → τ)
    (htag : ∀ c, MeasurableSet {x | tag x = c})
    (S : Set X) (hS : MeasurableSet S) (hSfinite : μ S < ⊤)
    (p mask g : o → X → β → ℝ) (v : τ → o → β → ℝ)
    (hp : ∀ b a, Integrable (fun x => p b x a) μ)
    (hmaskint : ∀ b a, Integrable (fun x => mask b x a) μ)
    (hmask : ∀ b x a, mask b x a ≤ p b x a)
    (hg : ∀ b x a, g b x a = ∑ c ∈ F, if tag x = c then v c b a else 0)
    (hgsupport : ∀ b x a, x ∉ S → g b x a = 0)
    (e mass : ℝ) (herror : (∑ b, ∫ x, ∑ a, |p b x a - g b x a| ∂μ) ≤ e)
    (allowed : Finset β) (D : ℕ) (L : o → X → Finset β)
    (hLmeas : ∀ b, MeasurableLists (L b))
    (hL : ∀ b x, L b x ⊆ allowed ∧ (L b x).card ≤ D)
    (hsuccess : mass ≤ ∑ b, ∫ x, ∑ a ∈ L b x, mask b x a ∂μ) :
    ∃ table : (Option F × o) → Finset β,
      (∀ c, table c ⊆ allowed ∧ (table c).card ≤ D) ∧
      mass - 2 * e ≤ ∑ b, ∫ x, ∑ a ∈ table (finiteObservedCode F tag x, b), p b x a ∂μ := by
  classical
  let code := finiteObservedCode F tag
  let ρ : X → ℝ := S.indicator (fun _ => 1)
  let w : (Option F × o) → β → ℝ :=
    fun c a => c.1.elim 0 (fun j => v j.val c.2 a)
  have hρint : Integrable ρ μ :=
    (integrable_indicator_iff hS).mpr (integrableOn_const hSfinite.ne)
  have hρ : ∀ x, 0 ≤ ρ x := by
    intro x
    by_cases hx : x ∈ S <;> simp [ρ, hx]
  have hfactor (b : o) (x : X) (a : β) : g b x a = ρ x * w (code x, b) a := by
    by_cases hx : x ∈ S
    · simp only [ρ, indicator_of_mem hx, one_mul]
      exact (hg b x a).trans (sparse_table_at_observed_code F tag (fun j => v j b a) x)
    · simp [hgsupport b x a hx, ρ, indicator_of_notMem hx]
  apply recover_original_coarse_list μ code (measurableSet_finiteObservedCode F tag htag)
    p mask ρ w hp hmaskint hρint hρ hmask e mass ?_ allowed D L hLmeas hL hsuccess
  simpa only [← hfactor] using herror

end Submission.Lib.K4MeshListRecovery
