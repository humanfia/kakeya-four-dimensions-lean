/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.RetainedObservedTrajectories

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

/-- A positive causal path weight certifies every retention decision in
its actual past, including the original starting decision. -/
theorem causalRetentionWeights_ne_zero_on_path {X : Type*}
    (w₀ : X → ENNReal)
    (α : (n : ℕ) → ((i : Finset.Iic n) → X) → X → ENNReal)
    (N : ℕ) (x : ℕ → X)
    (hw : causalRetentionWeights w₀ α N (Preorder.frestrictLe N x) ≠ 0) :
    w₀ (x 0) ≠ 0 ∧ ∀ k < N, α k (Preorder.frestrictLe k x) (x (k+1)) ≠ 0 := by
  have hall : ∀ n, causalRetentionWeights w₀ α n (Preorder.frestrictLe n x) ≠ 0 →
      w₀ (x 0) ≠ 0 ∧ ∀ k < n, α k (Preorder.frestrictLe k x) (x (k+1)) ≠ 0 := by
    intro n
    induction n with
    | zero =>
      intro h
      exact ⟨h,fun k hk => (Nat.not_lt_zero k hk).elim⟩
    | succ n ih =>
      intro h
      change causalRetentionWeights w₀ α n (Preorder.frestrictLe n x) *
        α n (Preorder.frestrictLe n x) (x (n+1)) ≠ 0 at h
      obtain ⟨hprev,hn⟩ := mul_ne_zero_iff.mp h
      obtain ⟨h0,hs⟩ := ih hprev
      refine ⟨h0,fun k hk => ?_⟩
      by_cases hkn : k < n
      · exact hs k hkn
      · have hkn' : k = n := by omega
        subst k
        exact hn
  exact hall N hw

/-- The retained original trajectory satisfies all decisions with
nonzero retention weight almost everywhere. -/
theorem causal_retained_trajectory_ae_decisions {X : Type*} [MeasurableSpace X]
    (Q : Measure (ℕ → X))
    (w₀ : X → ENNReal) (hw₀ : Measurable w₀)
    (α : (n : ℕ) → ((i : Finset.Iic n) → X) → X → ENNReal)
    (hα : ∀ n, Measurable (Function.uncurry (α n))) (N : ℕ) :
    ∀ᵐ x ∂Q.withDensity (fun x => causalRetentionWeights w₀ α N (Preorder.frestrictLe N x)),
      w₀ (x 0) ≠ 0 ∧ ∀ k < N, α k (Preorder.frestrictLe k x) (x (k+1)) ≠ 0 := by
  apply (ae_withDensity_iff (μ := Q)
    (f := fun x : ℕ → X => causalRetentionWeights w₀ α N (Preorder.frestrictLe N x))
    ((causalRetentionWeights_measurable w₀ hw₀ α hα N).comp
      (by fun_prop : Measurable (Preorder.frestrictLe (π := fun _ : ℕ => X) N)))).mpr
  exact Filter.Eventually.of_forall (fun x hx => causalRetentionWeights_ne_zero_on_path w₀ α N x hx)


theorem causalObservedHistory_on_path_fst {X Ω V : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace V]
    (start : X → Ω)
    (obs : (n : ℕ) → (((i : Finset.Iic n) → X) × X) → V)
    (n : ℕ) (x : ℕ → X) :
    (causalObservedHistory start obs n (Preorder.frestrictLe n x)).1 = start (x 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (appendObservedCoordinate n
      (causalObservedHistory start obs n (Preorder.frestrictLe n x),
        obs n (Preorder.frestrictLe n x,x (n+1)))).1 = _
    rw [appendObservedCoordinate_apply]
    exact ih

/-- Every observed coordinate is certified by its actual transition in
the original full path. -/
theorem causalObservedHistory_on_path_snd_property {X Ω V : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace V]
    (start : X → Ω)
    (obs : (n : ℕ) → (((i : Finset.Iic n) → X) × X) → V)
    (R : V → Prop) (N : ℕ) (x : ℕ → X)
    (hobs : ∀ k < N, R (obs k (Preorder.frestrictLe k x,x (k+1)))) :
    ∀ i : Fin N, R ((causalObservedHistory start obs N (Preorder.frestrictLe N x)).2 i) := by
  have hall : ∀ n, (∀ k < n, R (obs k (Preorder.frestrictLe k x,x (k+1)))) →
      ∀ i : Fin n, R ((causalObservedHistory start obs n (Preorder.frestrictLe n x)).2 i) := by
    intro n
    induction n with
    | zero => intro _ i; exact Fin.elim0 i
    | succ n ih =>
      intro hs
      have hprev := ih (fun k hk => hs k (Nat.lt_succ_of_lt hk))
      change ∀ i : Fin (n+1), R ((appendObservedCoordinate n
        (causalObservedHistory start obs n (Preorder.frestrictLe n x),
          obs n (Preorder.frestrictLe n x,x (n+1)))).2 i)
      rw [appendObservedCoordinate_apply]
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using hs n (Nat.lt_succ_self n)
      · simpa only [Fin.snoc_castSucc] using hprev j
  exact hall N hobs


/-- Stored observed coordinates retain the exact actual transition index. -/
theorem causalObservedHistory_on_path_snd_apply {X Ω V : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace V]
    (start : X → Ω)
    (obs : (n : ℕ) → (((i : Finset.Iic n) → X) × X) → V)
    (N : ℕ) (x : ℕ → X) (i : Fin N) :
    (causalObservedHistory start obs N (Preorder.frestrictLe N x)).2 i =
      obs i.1 (Preorder.frestrictLe i.1 x,x (i.1+1)) := by
  have hall : ∀ n, ∀ i : Fin n,
      (causalObservedHistory start obs n (Preorder.frestrictLe n x)).2 i =
        obs i.1 (Preorder.frestrictLe i.1 x,x (i.1+1)) := by
    intro n
    induction n with
    | zero => intro i; exact Fin.elim0 i
    | succ n ih =>
      intro i
      change (appendObservedCoordinate n
        (causalObservedHistory start obs n (Preorder.frestrictLe n x),
          obs n (Preorder.frestrictLe n x,x (n+1)))).2 i = _
      rw [appendObservedCoordinate_apply]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last, Fin.val_last]
      · simpa only [Fin.snoc_castSucc, Fin.val_castSucc] using ih j
  exact hall N i

theorem separateObservedCoordinates_apply {Ω C T : Type*}
    [MeasurableSpace Ω] [MeasurableSpace C] [MeasurableSpace T]
    (n : ℕ) (z : Ω × (Fin n → C × T)) :
    separateObservedCoordinates n z = ((z.1,fun i => (z.2 i).1),fun i => (z.2 i).2) := rfl


end Submission.Lib.K4PolynomialNorming
