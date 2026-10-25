import Mathlib
import Submission.Lib.K4QuadraticSheets.BrokenTube
import Submission.Lib.K4QuadraticSheets.ContinuationUse

/-!
# Local branches and continued sheets

Where the discriminant of a quadratic test does not vanish, its roots are the two branches
`rootOf P z (± S z)` built from a square root `S` (one branch when the test is linear in the
hidden variable).  Every continuous root branch on a preconnected set is one of them.  A square
root on a tube around a broken segment therefore continues any given local root branch from the
start of the segment to a simple sheet on the whole tube.
-/

namespace Submission.Lib.K4QuadraticSheets

open MvPolynomial

variable {n : ℕ}

local notation "E" => EuclideanSpace ℂ (Fin n)

/-- Every root of the test at a point with nonzero discriminant is one of the two roots built
from a square root of the discriminant. -/
theorem root_eq_rootOf {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P.totalDegree ≤ 2)
    {z : Fin n → ℂ} {S w : ℂ} (hS : S ^ 2 = qdisc P z) (hd : qdisc P z ≠ 0)
    (hw : eval (Fin.snoc z w : Fin (n + 1) → ℂ) P = 0) :
    w = rootOf P z S ∨ w = rootOf P z (-S) := by
  rw [eval_snoc_quadratic P hP] at hw
  unfold rootOf
  by_cases hc : qc P = 0
  · left
    simp only [hc, ite_true]
    have hb : qb P z ≠ 0 := by
      intro hb; apply hd; rw [qdisc, hb, hc]; ring
    rw [hc] at hw
    field_simp
    linear_combination hw
  · simp only [hc, ite_false]
    have key : (qc P * w + qb P z - S) * (qc P * w + qb P z + S) = 0 := by
      rw [qdisc] at hS
      linear_combination (2 * qc P) * hw - hS
    rcases mul_eq_zero.mp key with h | h
    · left
      field_simp
      linear_combination h
    · right
      field_simp
      linear_combination h

/-- A continuous root branch on a preconnected set where the discriminant has an analytic square
root is one of the two analytic branches. -/
theorem root_branch_eq_rootOf {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P.totalDegree ≤ 2)
    {S g : E → ℂ} {s : Set E} (hs : IsPreconnected s) (hSc : ContinuousOn S s)
    (hS : ∀ z ∈ s, S z ^ 2 = qdisc P (fun j => z j)) (hd : ∀ z ∈ s, qdisc P (fun j => z j) ≠ 0)
    (hgc : ContinuousOn g s)
    (hg : ∀ z ∈ s, eval (Fin.snoc (fun j : Fin n => z j) (g z) : Fin (n + 1) → ℂ) P = 0)
    {b : E} (hb : b ∈ s) :
    (∀ z ∈ s, g z = rootOf P (fun j => z j) (S z)) ∨
      ∀ z ∈ s, g z = rootOf P (fun j => z j) (-S z) := by
  -- the two analytic branches are continuous root branches
  have hcont : ∀ T : E → ℂ, ContinuousOn T s → (∀ z ∈ s, T z ^ 2 = qdisc P (fun j => z j)) →
      ContinuousOn (fun z => rootOf P (fun j => z j) (T z)) s := by
    intro T hT _
    unfold rootOf
    by_cases hc : qc P = 0
    · simp only [hc, ite_true]
      refine ContinuousOn.div (differentiable_qg P).continuous.continuousOn.neg
        (differentiable_qb P).continuous.continuousOn ?_
      intro z hz hb0
      apply hd z hz
      rw [qdisc, hb0, hc]; ring
    · simp only [hc, ite_false]
      exact ((differentiable_qb P).continuous.continuousOn.neg.add hT).div_const _
  have hroot : ∀ T : E → ℂ, (∀ z ∈ s, T z ^ 2 = qdisc P (fun j => z j)) → ∀ z ∈ s,
      eval (Fin.snoc (fun j : Fin n => z j) (rootOf P (fun j => z j) (T z)) :
        Fin (n + 1) → ℂ) P = 0 := fun T hT z hz => eval_rootOf hP (hT z hz) (hd z hz)
  have hSneg : ∀ z ∈ s, (-S z) ^ 2 = qdisc P (fun j => z j) := fun z hz => by
    rw [neg_sq]; exact hS z hz
  rcases root_eq_rootOf hP (hS b hb) (hd b hb) (hg b hb) with h | h
  · left
    exact root_branch_eq_of_eq_at hP hs hgc (hcont S hSc hS) hg (hroot S hS) hd hb h
  · right
    exact root_branch_eq_of_eq_at hP hs hgc (hcont (fun z => -S z) hSc.neg hSneg) hg
      (hroot (fun z => -S z) hSneg) hd hb h

/-- The branch built from a square root is a simple sheet on any set inside its domain. -/
theorem simpleSheet_rootOf {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P.totalDegree ≤ 2)
    (hP0 : P ≠ 0) {S : E → ℂ} {U : Set E} (hSa : AnalyticOnNhd ℂ S U)
    (hS : ∀ z ∈ U, S z ^ 2 = qdisc P (fun j => z j) ∧ qdisc P (fun j => z j) ≠ 0) :
    SimpleSheet P (fun z => rootOf P (fun j => z j) (S z)) U ∧
      AnalyticOnNhd ℂ (fun z => rootOf P (fun j => z j) (S z)) U := by
  have h := sheet_of_sqrt hP hSa.differentiableOn (fun z hz => (hS z hz).1)
    (fun z hz => (hS z hz).2)
  exact ⟨⟨hP0, hP, h.1, h.2⟩, analyticOnNhd_rootOf hSa (fun z hz => (hS z hz).2)⟩

/-- **Continuing a local branch.**  Given an analytic square root of the discriminant on an open
preconnected set `U`, and a continuous local root branch `f₀` on a preconnected neighbourhood
`B ⊆ U` of a point, some analytic simple sheet on `U` agrees with `f₀` on `B`. -/
theorem exists_continued_sheet {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P.totalDegree ≤ 2)
    (hP0 : P ≠ 0) {S : E → ℂ} {U B : Set E} (hSa : AnalyticOnNhd ℂ S U)
    (hS : ∀ z ∈ U, S z ^ 2 = qdisc P (fun j => z j) ∧ qdisc P (fun j => z j) ≠ 0)
    (hBU : B ⊆ U) (hB : IsPreconnected B) {b : E} (hb : b ∈ B) {f₀ : E → ℂ}
    (hf₀c : ContinuousOn f₀ B)
    (hf₀ : ∀ z ∈ B, eval (Fin.snoc (fun j : Fin n => z j) (f₀ z) : Fin (n + 1) → ℂ) P = 0) :
    ∃ f : E → ℂ, SimpleSheet P f U ∧ AnalyticOnNhd ℂ f U ∧ ∀ z ∈ B, f z = f₀ z := by
  have hSB : ContinuousOn S B := hSa.continuousOn.mono hBU
  rcases root_branch_eq_rootOf hP hB hSB (fun z hz => (hS z (hBU hz)).1)
      (fun z hz => (hS z (hBU hz)).2) hf₀c hf₀ hb with h | h
  · obtain ⟨h1, h2⟩ := simpleSheet_rootOf hP hP0 hSa hS
    exact ⟨_, h1, h2, fun z hz => (h z hz).symm⟩
  · have hSa' : AnalyticOnNhd ℂ (fun z => -S z) U := fun z hz => (hSa z hz).neg
    have hS' : ∀ z ∈ U, (-S z) ^ 2 = qdisc P (fun j => z j) ∧ qdisc P (fun j => z j) ≠ 0 :=
      fun z hz => ⟨by rw [neg_sq]; exact (hS z hz).1, (hS z hz).2⟩
    obtain ⟨h1, h2⟩ := simpleSheet_rootOf hP hP0 hSa' hS'
    exact ⟨_, h1, h2, fun z hz => (h z hz).symm⟩

/-- Two functions that agree on a neighbourhood of a point have the same jets there. -/
theorem iteratedFDeriv_eq_of_eqOn_ball {f g : E → ℂ} {α : E} {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ z ∈ Metric.ball α ρ, f z = g z) (j : ℕ) :
    iteratedFDeriv ℂ j f α = iteratedFDeriv ℂ j g α := by
  have heq : f =ᶠ[nhds α] g := Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds α hρ) h
  exact (heq.iteratedFDeriv ℂ j).eq_of_nhds

end Submission.Lib.K4QuadraticSheets
