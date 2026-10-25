/-
Adapted from: here:o064
Original proofs by session x0217 in this workspace. Uses the accepted
K4OriginalLists and K4ModelReduction APIs for paper Lemma a03:actual-lists.
-/

import Submission.Lib.K4OriginalLists

/-!
Original-law list recovery from a finite observable code on an arbitrary base.
This connects rectangular mesh tables to the accepted original-law recovery
theorem, retaining the actual observed tag and the unnormalized analytical mask.
-/

namespace Submission.Lib.K4MeshListRecovery

open Finset MeasureTheory Set
open Submission.Lib.K4OriginalLists

variable {X ι o β : Type*} [MeasurableSpace X] [Fintype ι] [Fintype o] [Fintype β]

omit [Fintype o] [Fintype β] in
/-- Split an integral according to a finite observable code. -/
theorem sum_integral_code_fibers (μ : Measure X) (code : X → ι)
    (hcode : ∀ j, MeasurableSet {x | code x = j}) (f : ι → X → ℝ)
    (hf : ∀ j, Integrable (f j) μ) :
    (∑ j, ∫ x, f j x ∂μ.restrict {x | code x = j}) = ∫ x, f (code x) x ∂μ := by
  classical
  calc
    _ = ∑ j, ∫ x, {x | code x = j}.indicator (f j) x ∂μ := by
      apply sum_congr rfl
      intro j _
      rw [integral_indicator (hcode j)]
    _ = ∫ x, ∑ j, {x | code x = j}.indicator (f j) x ∂μ :=
      (integral_finsetSum _ (fun j _ => (hf j).indicator (hcode j))).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by simp [Set.indicator_apply, eq_comm])

omit [Fintype β] in
/-- Retain an additional observed discrete tag when splitting by the base code. -/
theorem sum_integral_code_records (μ : Measure X) (code : X → ι)
    (hcode : ∀ j, MeasurableSet {x | code x = j}) (f : ι → o → X → ℝ)
    (hf : ∀ j b, Integrable (f j b) μ) :
    (∑ c : ι × o, ∫ x, f c.1 c.2 x ∂μ.restrict {x | code x = c.1}) =
      ∑ b, ∫ x, f (code x) b x ∂μ := by
  classical
  rw [Fintype.sum_prod_type, sum_comm]
  exact sum_congr rfl (fun b _ => sum_integral_code_fibers μ code hcode (fun j => f j b) (fun j => hf j b))

/-- A density approximation of the form `ρ(x) w(code(x), observed, label)` gives a
finite original-law table. Its complexity depends only on the finite code and labels. -/
theorem recover_original_coarse_list
    (μ : Measure X) (code : X → ι) (hcode : ∀ j, MeasurableSet {x | code x = j})
    (p mask : o → X → β → ℝ) (ρ : X → ℝ) (w : (ι × o) → β → ℝ)
    (hp : ∀ b a, Integrable (fun x => p b x a) μ)
    (hmaskint : ∀ b a, Integrable (fun x => mask b x a) μ)
    (hρint : Integrable ρ μ) (hρ : ∀ x, 0 ≤ ρ x)
    (hmask : ∀ b x a, mask b x a ≤ p b x a)
    (e mass : ℝ)
    (herror : (∑ b, ∫ x, ∑ a, |p b x a - ρ x * w (code x, b) a| ∂μ) ≤ e)
    (allowed : Finset β) (D : ℕ) (L : o → X → Finset β)
    (hLmeas : ∀ b, MeasurableLists (L b))
    (hL : ∀ b x, L b x ⊆ allowed ∧ (L b x).card ≤ D)
    (hsuccess : mass ≤ ∑ b, ∫ x, ∑ a ∈ L b x, mask b x a ∂μ) :
    ∃ table : (ι × o) → Finset β,
      (∀ c, table c ⊆ allowed ∧ (table c).card ≤ D) ∧
      mass - 2 * e ≤ ∑ b, ∫ x, ∑ a ∈ table (code x, b), p b x a ∂μ := by
  classical
  let ν : (ι × o) → Measure X := fun c => μ.restrict {x | code x = c.1}
  have hmaskL (b : o) : Integrable (fun x => ∑ a ∈ L b x, mask b x a) μ :=
    integrable_listDensity μ (mask b) (L b) (hmaskint b) (hLmeas b)
  have herrint (j : ι) (b : o) :
      Integrable (fun x => ∑ a, |p b x a - ρ x * w (j, b) a|) μ :=
    integrable_finsetSum _ (fun a _ => ((hp b a).sub (hρint.mul_const _)).abs)
  have herror' : (∑ c : ι × o, ∫ x, ∑ a, |p c.2 x a - ρ x * w c a| ∂ν c) ≤ e := by
    rw [show (∑ c : ι × o, ∫ x, ∑ a, |p c.2 x a - ρ x * w c a| ∂ν c) =
      ∑ b, ∫ x, ∑ a, |p b x a - ρ x * w (code x, b) a| ∂μ from
        sum_integral_code_records μ code hcode _ herrint]
    exact herror
  have hsuccess' : mass ≤ continuousListMass ν (fun c => mask c.2) (fun c => L c.2) := by
    unfold continuousListMass listDensity
    rw [sum_integral_code_records μ code hcode _ (fun j b => hmaskL b)]
    exact hsuccess
  obtain ⟨table, htable, htablemass⟩ := recover_original_continuous_list allowed D ν
    (fun c => p c.2) (fun c => mask c.2) (fun _ => ρ) w
    (fun c a => (hp c.2 a).restrict)
    (fun c a => (hmaskint c.2 a).restrict)
    (fun _ => hρint.restrict) (fun c => hmask c.2) (fun _ => hρ)
    e mass herror' (fun c => L c.2) (fun c => hLmeas c.2) (fun c => hL c.2) hsuccess'
  refine ⟨table, htable, ?_⟩
  have htableint (j : ι) (b : o) :
      Integrable (fun x => ∑ a ∈ table (j, b), p b x a) μ :=
    integrable_finsetSum _ (fun a _ => hp b a)
  have heq : continuousListMass ν (fun c => p c.2) (fun c _ => table c) =
      ∑ b, ∫ x, ∑ a ∈ table (code x, b), p b x a ∂μ :=
    sum_integral_code_records μ code hcode _ htableint
  exact htablemass.trans_eq heq

end Submission.Lib.K4MeshListRecovery
