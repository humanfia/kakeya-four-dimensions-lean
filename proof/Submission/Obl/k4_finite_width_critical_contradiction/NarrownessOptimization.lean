import Mathlib

/-!
Finite optimization of narrowness. The approximation parameter selecting an
exact problem is separate from the positive horizon margin of its charts.
-/

namespace Submission.Obl.k4_finite_width_critical_contradiction

variable {α : Type*}

/-- A width is uniformly available if every fixed positive horizon margin works
on all sufficiently close maximizing problems. -/
def UniformNarrowness (near : ℝ → α → Prop) (attain : α → ℝ → ℝ → Prop)
    (rate width : ℝ) : Prop :=
  ∀ margin : ℝ, 0 < margin → ∃ tolerance : ℝ, 0 < tolerance ∧
    ∀ p, near tolerance p → attain p (rate + margin) width

/-- One fixed positive horizon margin fails at this width arbitrarily near
maximization. Both the width and margin precede the approximation tolerance. -/
def BoundedNarrowness (near : ℝ → α → Prop) (attain : α → ℝ → ℝ → Prop)
    (rate width : ℝ) : Prop :=
  ∃ margin : ℝ, 0 < margin ∧ ∀ tolerance : ℝ, 0 < tolerance →
    ∃ p, near tolerance p ∧ ¬ attain p (rate + margin) width

theorem boundedNarrowness_iff_not_uniformNarrowness
    (near : ℝ → α → Prop) (attain : α → ℝ → ℝ → Prop) (rate width : ℝ) :
    BoundedNarrowness near attain rate width ↔
      ¬ UniformNarrowness near attain rate width := by
  classical
  simp [BoundedNarrowness, UniformNarrowness, not_forall]

theorem UniformNarrowness.mono_width
    {near : ℝ → α → Prop} {attain : α → ℝ → ℝ → Prop} {rate width width' : ℝ}
    (hmono : ∀ p h w w', w' ≤ w → attain p h w → attain p h w')
    (h : UniformNarrowness near attain rate width) (hwidth : width' ≤ width) :
    UniformNarrowness near attain rate width' := by
  intro margin hmargin
  obtain ⟨tolerance, htol, hall⟩ := h margin hmargin
  exact ⟨tolerance, htol, fun p hp => hmono p _ _ _ hwidth (hall p hp)⟩

/-- Bounded width produces a finite nonnegative optimal narrowness. Widths
strictly below it are uniformly attainable; every larger width has a fixed
positive horizon margin witnessing failure. This includes optimal width zero. -/
theorem exists_optimal_narrowness
    (near : ℝ → α → Prop) (attain : α → ℝ → ℝ → Prop) (rate : ℝ)
    (hmono : ∀ p h w w', w' ≤ w → attain p h w → attain p h w')
    (hzero : UniformNarrowness near attain rate 0)
    {bound : ℝ} (hbound : BoundedNarrowness near attain rate bound) :
    ∃ width : ℝ, 0 ≤ width ∧ width ≤ bound ∧
      (∀ w, w < width → UniformNarrowness near attain rate w) ∧
      (∀ ζ, 0 < ζ → UniformNarrowness near attain rate (max 0 (width - ζ))) ∧
      (∀ ζ, 0 < ζ → BoundedNarrowness near attain rate (width + ζ)) := by
  classical
  let S : Set ℝ := {w | UniformNarrowness near attain rate w}
  have hSne : S.Nonempty := ⟨0, hzero⟩
  have hupper : ∀ w ∈ S, w ≤ bound := by
    intro w hw
    by_contra hn
    have hbw : bound ≤ w := le_of_lt (lt_of_not_ge hn)
    exact (boundedNarrowness_iff_not_uniformNarrowness near attain rate bound).mp hbound
      (hw.mono_width hmono hbw)
  have hSb : BddAbove S := ⟨bound, hupper⟩
  have hbelow : ∀ w, w < sSup S → UniformNarrowness near attain rate w := by
    intro w hw
    obtain ⟨v, hv, hwv⟩ := exists_lt_of_lt_csSup hSne hw
    exact hv.mono_width hmono hwv.le
  have hnonneg : 0 ≤ sSup S := le_csSup hSb hzero
  refine ⟨sSup S, hnonneg, csSup_le hSne hupper, hbelow, ?_, ?_⟩
  · intro ζ hζ
    rcases le_total (sSup S - ζ) 0 with h | h
    · simpa only [max_eq_left h] using hzero
    · rw [max_eq_right h]
      exact hbelow _ (sub_lt_self _ hζ)
  · intro ζ hζ
    apply (boundedNarrowness_iff_not_uniformNarrowness near attain rate _).mpr
    intro h
    have := le_csSup hSb h
    linarith

end Submission.Obl.k4_finite_width_critical_contradiction
