import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueGridChain

/-! Literal cuts of a true path. Every initialPart and suffix uses the same
normalizations and composes to the original common-law pullback. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueLiftChains.Chain

open MeasureTheory Filter
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open PathMeasures

noncomputable section

variable {p q z : Code}

def append {p q z : Code} (first : Chain p q) (second : Chain q z) : Chain p z :=
  match first with
  | .nil _ _ => second
  | .cons a hL hr hh hrelative tail =>
      .cons a hL hr hh hrelative (tail.append second)

theorem append_depth (first : Chain p q) (second : Chain q z) :
    (first.append second).depth = first.depth + second.depth := by
  induction first with
  | nil => simp [append, depth]
  | cons a hL hr hh hrelative tail ih =>
    simp only [append, depth, ih, add_assoc]

theorem append_cost (first : Chain p q) (second : Chain q z) :
    (first.append second).cost = first.cost + second.cost := by
  induction first with
  | nil => simp [append, cost]
  | cons a hL hr hh hrelative tail ih =>
    simp only [append, cost, ih, add_assoc]

theorem append_sample (first : Chain p q) (second : Chain q z) (k : ℕ) :
    (first.append second).sample k = first.sample (second.sample k) := by
  induction first with
  | nil => rfl
  | cons a hL hr hh hrelative tail ih =>
    change a.witness.sample ((tail.append second).sample k) =
      a.witness.sample (tail.sample (second.sample k))
    rw [ih]

abbrev WorldStates (p : Code) := Σ k : ℕ, Fin (W p k) × State

/-- Remembering the actual sample makes composition independent of transports
between the dependent world index types. -/
def totalPullback (chain : Chain p z) : WorldStates z → WorldStates p :=
  fun u => ⟨chain.sample u.1, chain.pullback u.1 u.2⟩

def stepPullback {r h : ℝ} (a : TrueNormalization p q r r h) :
    WorldStates q → WorldStates p :=
  fun u => ⟨a.witness.sample u.1, pullbackMap a.witness a.parent_exact u.1 u.2⟩

theorem append_pullback (first : Chain p q) (second : Chain q z) :
    (first.append second).totalPullback = first.totalPullback ∘ second.totalPullback := by
  induction first with
  | nil => rfl
  | cons a hL hr hh hrelative tail ih =>
    change stepPullback a ∘ (tail.append second).totalPullback =
      (stepPullback a ∘ tail.totalPullback) ∘ second.totalPullback
    rw [ih]
    rfl

def length {p z : Code} (chain : Chain p z) : ℕ :=
  match chain with
  | .nil _ _ => 0
  | .cons _ _ _ _ _ tail => tail.length + 1

/-- The actual remaining exact code and chain after a given number of
normalizations. Indices past the last node stay at the final code. -/
def cut {p z : Code} (chain : Chain p z) (n : ℕ) : Σ q : Code, Chain q z :=
  (Nat.rec (motive := fun _ => ∀ p z : Code, Chain p z → Σ q : Code, Chain q z)
    (fun p _ c => ⟨p, c⟩)
    (fun _ rec _ _ c =>
      match c with
      | .nil p hp => ⟨p, .nil p hp⟩
      | .cons _ _ _ _ _ tail => rec _ _ tail) n) p z chain

abbrev codeAt (chain : Chain p z) (n : ℕ) : Code := (chain.cut n).1
abbrev suffix (chain : Chain p z) (n : ℕ) : Chain (chain.codeAt n) z := (chain.cut n).2

/-- The original initialPart of that same literal cut. -/
def initialPart {p z : Code} (chain : Chain p z) (n : ℕ) : Chain p (chain.codeAt n) :=
  match n with
  | 0 => .nil p chain.source_exact
  | n + 1 =>
    match chain with
    | .nil p hp => .nil p hp
    | .cons a hL hr hh hrelative tail =>
      .cons a hL hr hh hrelative (tail.initialPart n)

theorem prefix_append_suffix (chain : Chain p z) (n : ℕ) :
    (chain.initialPart n).append (chain.suffix n) = chain := by
  induction n generalizing p with
  | zero =>
    cases chain <;> rfl
  | succ n ih =>
    cases chain with
    | nil => rfl
    | cons a hL hr hh hrelative tail =>
      change Chain.cons a hL hr hh hrelative
        ((tail.initialPart n).append (tail.suffix n)) =
          Chain.cons a hL hr hh hrelative tail
      rw [ih tail]

theorem cut_sample (chain : Chain p z) (n k : ℕ) :
    chain.sample k = (chain.initialPart n).sample ((chain.suffix n).sample k) := by
  calc
    chain.sample k = ((chain.initialPart n).append (chain.suffix n)).sample k :=
      congrArg (fun c => c.sample k) (chain.prefix_append_suffix n).symm
    _ = _ := append_sample _ _ _

/-- Each potential-parent view is the image of the same final probability. -/
theorem cut_pullback (chain : Chain p z) (n : ℕ) :
    chain.totalPullback = (chain.initialPart n).totalPullback ∘
      (chain.suffix n).totalPullback := by
  calc
    chain.totalPullback = ((chain.initialPart n).append (chain.suffix n)).totalPullback :=
      congrArg totalPullback (chain.prefix_append_suffix n).symm
    _ = _ := append_pullback _ _

/-- Every parent reached by a true normalization has calibrated absolute
profile zero, on the actual exact code at that node. -/
theorem codeAt_profile_zero (chain : Chain p z) (n : ℕ)
    (hn : 0 < n) (hnlength : n ≤ chain.length) : f (chain.codeAt n) 0 = 0 := by
  induction n generalizing p with
  | zero => omega
  | succ n ih =>
    cases chain with
    | nil => simp [length] at hnlength
    | cons a hL hr hh hrelative tail =>
      cases n with
      | zero =>
        exact a.profile_zero tail.source_exact hL hr
      | succ n =>
        exact ih tail (by omega) (by simpa only [length, Nat.add_le_add_iff_right] using hnlength)

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueLiftChains.Chain
