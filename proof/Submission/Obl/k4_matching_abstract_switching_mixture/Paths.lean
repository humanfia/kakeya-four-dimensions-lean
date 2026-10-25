import Submission.Obl.k4_matching_abstract_switching_mixture.Finite

namespace Submission.Obl.k4_matching_abstract_switching_mixture

open Finite

variable {Ω : Type*}

/-- Arrival events of a finite path, continued constantly after the last step. -/
def arrival (a : Ω) : List (Ω × Bool × Ω) → ℕ → Ω
  | [], _ => a
  | _ :: _, 0 => a
  | q :: l, p + 1 => arrival q.2.2 l p

/-- Refreshed events of a path, with a constant continuation. -/
def refresh (a : Ω) : List (Ω × Bool × Ω) → ℕ → Ω
  | [], _ => a
  | q :: _, 0 => q.1
  | q :: l, p + 1 => refresh q.2.2 l p

/-- The colours of a path, with the first colour after its end. -/
def pathColor : List (Ω × Bool × Ω) → ℕ → Bool
  | [], _ => true
  | q :: _, 0 => q.2.1
  | _ :: l, p + 1 => pathColor l p

/-- A chronological chain of legal refresh/traverse steps. -/
def Chain (R : Ω → (Ω × Bool × Ω) → Prop) (a : Ω) : List (Ω × Bool × Ω) → Prop
  | [] => True
  | q :: l => R a q ∧ Chain R q.2.2 l

@[simp] theorem curEvent_cons (a : Ω) (q : Ω × Bool × Ω) (l : List (Ω × Bool × Ω)) :
    curEvent a (q :: l) = curEvent q.2.2 l := by
  cases l <;> simp [curEvent, List.getLast?_cons]

@[simp] theorem arrival_zero (a : Ω) (l : List (Ω × Bool × Ω)) : arrival a l 0 = a := by
  cases l <;> rfl

@[simp] theorem arrival_length (a : Ω) (l : List (Ω × Bool × Ω)) :
    arrival a l l.length = curEvent a l := by
  induction l generalizing a with
  | nil => rfl
  | cons q l ih => simpa [arrival] using ih q.2.2

@[simp] theorem chain_append_singleton (R : Ω → (Ω × Bool × Ω) → Prop)
    (a : Ω) (l : List (Ω × Bool × Ω)) (q : Ω × Bool × Ω) :
    Chain R a (l ++ [q]) ↔ Chain R a l ∧ R (curEvent a l) q := by
  induction l generalizing a with
  | nil => simp [Chain, curEvent]
  | cons q' l ih => simp [Chain, ih, and_assoc]

/-- A finite legal path can be padded to arbitrarily many steps by staying put. -/
theorem chain_sequences {R : Ω → (Ω × Bool × Ω) → Prop}
    (hdiag : ∀ a, R a (a, true, a)) {a : Ω} {l : List (Ω × Bool × Ω)}
    (hl : Chain R a l) (p : ℕ) :
    R (arrival a l p) (refresh a l p, pathColor l p, arrival a l (p + 1)) := by
  induction l generalizing a p with
  | nil => exact hdiag a
  | cons q l ih =>
    cases p with
    | zero => simpa [arrival, refresh, pathColor] using hl.1
    | succ p => simpa [arrival, refresh, pathColor] using ih hl.2 p

/-- An arrival within the path is one of its recorded arrival events. -/
theorem arrival_mem {a : Ω} {l : List (Ω × Bool × Ω)} {p : ℕ}
    (hp : 0 < p) (hle : p ≤ l.length) :
    ∃ q ∈ l, arrival a l p = q.2.2 := by
  induction l generalizing a p with
  | nil => simp at hle; omega
  | cons q l ih =>
    cases p with
    | zero => omega
    | succ p =>
      cases p with
      | zero => exact ⟨q, by simp, by simp [arrival]⟩
      | succ p =>
        obtain ⟨r, hr, heq⟩ := ih (a := q.2.2) (p := p + 1) (by omega) (by simp only [List.length_cons] at hle; omega)
        exact ⟨r, by simp [hr], by simpa [arrival] using heq⟩

/-- The triple at any genuine step is recovered from the padded sequences. -/
theorem triple_getElem (a : Ω) (l : List (Ω × Bool × Ω)) (p : ℕ) (hp : p < l.length) :
    (refresh a l p, pathColor l p, arrival a l (p + 1)) = l[p] := by
  induction l generalizing a p with
  | nil => simp at hp
  | cons q l ih =>
    cases p with
    | zero => simp [refresh, pathColor, arrival]
    | succ p => simpa [refresh, pathColor, arrival] using ih q.2.2 p (by simpa using hp)

end Submission.Obl.k4_matching_abstract_switching_mixture
