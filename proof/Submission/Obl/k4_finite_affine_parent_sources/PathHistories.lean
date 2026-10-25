-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.Path

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set
open Submission.Obl.k4_finite_forest_width_selection
open scoped Classical

noncomputable section

local instance (C : ℕ) : MeasurableSpace (Option (Fin C)) := ⊤
local instance (C : ℕ) : MeasurableSingletonClass (Option (Fin C)) := ⟨fun _ => trivial⟩

/-- Choose a true entry from a finite Boolean record, with an explicit
empty value. All measure-theoretic work is in forming the record. -/
def chooseTrue {C : ℕ} (bits : Fin C → Bool) : Option (Fin C) :=
  if h : ∃ b, bits b = true then some (Classical.choose h) else none

lemma chooseTrue_spec {C : ℕ} (bits : Fin C → Bool) {b : Fin C}
    (hb : chooseTrue bits = some b) : bits b = true := by
  unfold chooseTrue at hb
  split_ifs at hb with h
  · have heq := Option.some.inj hb
    exact heq ▸ Classical.choose_spec h

lemma chooseTrue_some {C : ℕ} (bits : Fin C → Bool) (h : ∃ b, bits b = true) :
    ∃ b, chooseTrue bits = some b := by
  exact ⟨Classical.choose h, by simp only [chooseTrue, dite_eq_left h]⟩

/-- One terminal label of the supplied path, retaining the ORIGINAL world
coordinate. Outside the terminal path this has value none. -/
def PathData.terminalCode {W : ℕ} (p : PathData W) (m : ℕ)
    (z : Fin W × Incidence) : Option (Fin p.C) :=
  chooseTrue (fun b => if p.lev b = m - 1 ∧ p.world b = z.1 ∧ z.2 ∈ p.counted b
    then true else false)

/-- Every nonempty terminal code is an actual supplied terminal chart. -/
lemma PathData.terminalCode_spec {W : ℕ} (p : PathData W) (m : ℕ)
    {z : Fin W × Incidence} {b : Fin p.C} (hb : p.terminalCode m z = some b) :
    p.lev b = m - 1 ∧ p.world b = z.1 ∧ z.2 ∈ p.counted b := by
  have h := chooseTrue_spec _ hb
  by_contra hn
  simp only [ite_eq_right hn, Bool.false_eq_true] at h

lemma PathData.terminalCode_exists {W : ℕ} (p : PathData W) (m : ℕ)
    (w : Fin W) {z : Incidence}
    (hz : z ∈ TerminalInc W p.C m p.lev p.world p.counted w) :
    ∃ b, p.terminalCode m (w, z) = some b := by
  apply chooseTrue_some
  obtain ⟨b, hb, hw, hz⟩ := hz
  exact ⟨b, by simp only [hb, hw, hz, and_self, ite_true]⟩

/-- Apply an actual ancestor map to a finite terminal code. -/
def PathData.ancestorCode {W : ℕ} (p : PathData W) (i : ℕ) :
    Option (Fin p.C) → Option (Fin p.C) :=
  Option.map (fun b => forestAncestor p.lev p.par b i)

def PathData.history {W : ℕ} (p : PathData W) (m i : ℕ) :
    (Fin W × Incidence) → Option (Fin p.C) :=
  p.ancestorCode i ∘ p.terminalCode m

/-- Composition of actual forest ancestors, using the accepted level law. -/
lemma forestAncestor_comp {C : ℕ} (lev : Fin C → ℕ) (par : Fin C → Fin C)
    (hpar : ∀ b, 0 < lev b → lev (par b) + 1 = lev b)
    (b : Fin C) {i j : ℕ} (hij : i ≤ j) (hjb : j ≤ lev b) :
    forestAncestor lev par (forestAncestor lev par b j) i = forestAncestor lev par b i := by
  have hlev := forestAncestor_level hpar b j hjb
  change par^[lev (forestAncestor lev par b j) - i] (par^[lev b - j] b) = par^[lev b - i] b
  rw [hlev, ← Function.iterate_add_apply]
  congr 1
  omega

section

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

lemma PathData.Valid.measurable_terminalCode : Measurable (p.terminalCode m) := by
  have hcells (b : Fin p.C) : MeasurableSet {z : Fin W × Incidence |
      p.lev b = m - 1 ∧ p.world b = z.1 ∧ z.2 ∈ p.counted b} := by
    by_cases hb : p.lev b = m - 1
    · have hm := (measurableSet_singleton (p.world b)).prod (hp.chart b).2.2.2.2.2.2.2.1
      convert hm using 1
      ext z
      simp only [hb, true_and, mem_prod, mem_singleton_iff, mem_ofPred_eq, eq_comm]
    · simp only [hb, false_and, setOf_false]
      exact MeasurableSet.empty
  have hbits : Measurable (fun z : Fin W × Incidence => fun b : Fin p.C =>
      if p.lev b = m - 1 ∧ p.world b = z.1 ∧ z.2 ∈ p.counted b then true else false) := by
    apply measurable_pi_lambda
    intro b
    exact Measurable.ite (hcells b) measurable_const measurable_const
  exact (measurable_of_finite chooseTrue).comp hbits

lemma PathData.Valid.measurable_history (i : ℕ) : Measurable (p.history m i) :=
  (measurable_of_finite (p.ancestorCode i)).comp hp.measurable_terminalCode

/-- The original measurable histories refine by actual parent maps. This
identity holds on the whole source space and hence on every exact finite
code used by the entropy window. -/
lemma PathData.Valid.history_refines {i j : ℕ} (hij : i ≤ j) (hj : j ≤ m - 1)
    (z : Fin W × Incidence) :
    p.history m i z = p.ancestorCode i (p.history m j z) := by
  cases hcode : p.terminalCode m z with
  | none => simp [PathData.history, hcode, PathData.ancestorCode]
  | some b =>
    have hb := (p.terminalCode_spec m hcode).1
    simp only [PathData.history, Function.comp_apply, hcode, PathData.ancestorCode, Option.map_some]
    congr 1
    exact (forestAncestor_comp p.lev p.par (fun b hb => (hp.parent b hb).1)
      b hij (by omega)).symm

end

end

end Submission.Obl.k4_finite_affine_parent_sources
