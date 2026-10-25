import Submission.Obl.k4_matching_abstract_switching_mixture.Paths
import Submission.Obl.k4_matching_abstract_switching_mixture.Estimates

namespace Submission.Obl.k4_matching_abstract_switching_mixture

open Finset
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite
open Classical

variable {Ω Sf Sc Ar Iv Pal Tc : Type*} [Fintype Ω] [DecidableEq Sf]
  [DecidableEq Sc] [DecidableEq Ar] [DecidableEq Iv] [DecidableEq Pal]
  [Fintype Tc] [DecidableEq Tc]

/-- A legal fine refresh followed by traversal on an arm and coarse interval. -/
def legalStep (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (e : Ω) (q : Ω × Bool × Ω) : Prop :=
  X.fine q.1 = X.fine e ∧ X.armKey q.2.1 q.2.2 = X.armKey q.2.1 q.1

/-- Choose a control separated from the preceding one, using the two available colours. -/
noncomputable def adaptiveColor (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (r : ℝ)
    (_a : Ω) (l : List (Ω × Bool × Ω)) (e : Ω) : Bool :=
  match l.getLast? with
  | none => true
  | some q => if r ≤ |X.ctrl e true - X.ctrl q.1 q.2.1| then true else false

/-- Each new arrival avoids all earlier arrival times. -/
def separatedArrival (t : Ω → ℝ) (r : ℝ) (_n : ℕ)
    (l : List (Ω × Bool × Ω)) (e : Ω) : Prop :=
  ∀ q ∈ l, r ≤ |t e - t q.2.2|

/-- The finite path invariant records legal steps, positive masses, and both
control and time separation. -/
def goodPath (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (t : Ω → ℝ) (ru rt : ℝ)
    (a : Ω) (l : List (Ω × Bool × Ω)) : Prop :=
  Chain (legalStep X) a l ∧
    (∀ q ∈ l, 0 < X.P q.1 ∧ 0 < X.P q.2.2) ∧
    l.IsChain (fun q r => ru ≤ |X.ctrl r.1 r.2.1 - X.ctrl q.1 q.2.1|) ∧
    l.Pairwise (fun q r => rt ≤ |t r.2.2 - t q.2.2|)

theorem legalStep_diag (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (a : Ω) :
    legalStep X a (a, true, a) := ⟨rfl, rfl⟩

@[simp] theorem goodPath_nil (X : SwitchData Ω Sf Sc Ar Iv Pal Tc)
    (t : Ω → ℝ) (ru rt : ℝ) (a : Ω) : goodPath X t ru rt a [] := by
  simp [goodPath, Chain]

theorem adaptiveColor_separated (X : SwitchData Ω Sf Sc Ar Iv Pal Tc)
    (r : ℝ) (a : Ω) (l : List (Ω × Bool × Ω)) (e : Ω)
    (hgap : 2 * r ≤ |X.ctrl e true - X.ctrl e false|) :
    ∀ q ∈ l.getLast?, r ≤ |X.ctrl e (adaptiveColor X r a l e) - X.ctrl q.1 q.2.1| := by
  intro q hq
  cases hlast : l.getLast? with
  | none => simp [hlast] at hq
  | some q' =>
    have heq : q = q' := by simpa [hlast, eq_comm] using hq
    subst q'
    simp only [adaptiveColor, hlast]
    split_ifs with h
    · exact h
    · obtain ⟨c, hc⟩ := exists_separated_color (X.ctrl e) (X.ctrl q.1 q.2.1) r hgap
      cases c with
      | false => exact hc
      | true => exact False.elim (h hc)

theorem goodPath_append (X : SwitchData Ω Sf Sc Ar Iv Pal Tc)
    (t : Ω → ℝ) (ru rt : ℝ) {a : Ω} {l : List (Ω × Bool × Ω)}
    (hl : goodPath X t ru rt a l) (er e' : Ω) (c : Bool)
    (hstep : legalStep X (curEvent a l) (er, c, e'))
    (her : 0 < X.P er) (he' : 0 < X.P e')
    (hcontrol : ∀ q ∈ l.getLast?, ru ≤ |X.ctrl er c - X.ctrl q.1 q.2.1|)
    (htime : ∀ q ∈ l, rt ≤ |t e' - t q.2.2|) :
    goodPath X t ru rt a (l ++ [(er, c, e')]) := by
  refine ⟨(chain_append_singleton _ _ _ _).mpr ⟨hl.1, hstep⟩, ?_, ?_, ?_⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hl.2.1 q hq
    · have heq := List.mem_singleton.mp hq
      subst q
      exact ⟨her, he'⟩
  · apply hl.2.2.1.append (by simp)
    intro q hq r hr
    have heq : r = (er, c, e') := by simpa [eq_comm] using hr
    subst r
    exact hcontrol q hq
  · apply List.pairwise_append.mpr
    refine ⟨hl.2.2.2, by simp, ?_⟩
    intro q hq r hr
    have heq : r = (er, c, e') := by simpa using hr
    subst r
    exact htime q hq

/-- A conditional arm event is bounded by its marginal mass divided by the
heavy-atom threshold. -/
theorem condKey_pred_le (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (hP : ∀ e, 0 ≤ X.P e)
    (c : Bool) (er : Ω) (P : Ω → Prop) [DecidablePred P]
    {a lam D : ℝ} (hlam : 0 < lam) (hD : 0 ≤ D)
    (hheavy : a * lam ≤ atomMass X.P (X.armKey c) er)
    (hnum : ∑ e ∈ univ.filter (fun e => X.armKey c e = X.armKey c er ∧ P e), X.P e ≤ a * D) :
    ∑ e, condKey X.P (X.armKey c) er e * (if P e then (1 : ℝ) else 0) ≤ D / lam := by
  have heq : ∑ e, condKey X.P (X.armKey c) er e * (if P e then (1 : ℝ) else 0) =
      (∑ e ∈ univ.filter (fun e => X.armKey c e = X.armKey c er ∧ P e), X.P e) /
        atomMass X.P (X.armKey c) er := by
    rw [sum_div, sum_filter]
    refine sum_congr rfl fun e _ => ?_
    unfold condKey
    split_ifs <;> simp_all
  rw [heq]
  have hm := fiberMass_nonneg hP (X.armKey c) (X.armKey c er)
  change 0 ≤ atomMass X.P (X.armKey c) er at hm
  rcases hm.eq_or_lt with hm | hm
  · rw [← hm, div_zero]
    exact div_nonneg hD hlam.le
  · rw [div_le_div_iff₀ hm hlam]
    calc
      (∑ e ∈ univ.filter (fun e => X.armKey c e = X.armKey c er ∧ P e), X.P e) * lam
        ≤ (a * D) * lam := mul_le_mul_of_nonneg_right hnum hlam.le
      _ = D * (a * lam) := by ring
      _ ≤ D * atomMass X.P (X.armKey c) er := mul_le_mul_of_nonneg_left hheavy hD

/-- A union bound over previous arrivals controls the separation kill. -/
theorem separatedArrival_failure_le (X : SwitchData Ω Sf Sc Ar Iv Pal Tc)
    (hP : ∀ e, 0 ≤ X.P e) (t : Ω → ℝ) (r : ℝ)
    (c : Bool) (er : Ω) (l : List (Ω × Bool × Ω)) (n : ℕ) {v : ℝ} (hv : 0 ≤ v)
    (hnear : ∀ q ∈ l, ∑ e, condKey X.P (X.armKey c) er e *
      (if |t e - t q.2.2| < r then (1 : ℝ) else 0) ≤ v) :
    ∑ e, condKey X.P (X.armKey c) er e *
      (if separatedArrival t r n l e then (0 : ℝ) else 1) ≤ l.length * v := by
  have hind : ∀ e, (if separatedArrival t r n l e then (0 : ℝ) else 1) ≤
      ∑ q ∈ l.toFinset, if |t e - t q.2.2| < r then (1 : ℝ) else 0 := by
    intro e
    split_ifs with he
    · exact sum_nonneg fun q _ => by split_ifs <;> norm_num
    · have hex : ∃ q ∈ l, |t e - t q.2.2| < r := by
        simpa only [separatedArrival, not_forall, not_le, exists_prop] using he
      obtain ⟨q, hq, hdist⟩ := hex
      simpa [hdist] using (single_le_sum
        (f := fun q => if |t e - t q.2.2| < r then (1 : ℝ) else 0)
        (fun q _ => by split_ifs <;> norm_num) (List.mem_toFinset.mpr hq))
  calc
    ∑ e, condKey X.P (X.armKey c) er e *
        (if separatedArrival t r n l e then (0 : ℝ) else 1)
      ≤ ∑ e, condKey X.P (X.armKey c) er e *
        ∑ q ∈ l.toFinset, if |t e - t q.2.2| < r then (1 : ℝ) else 0 :=
          sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hind e) (condKey_nonneg hP _ _ _)
    _ = ∑ q ∈ l.toFinset, ∑ e, condKey X.P (X.armKey c) er e *
        (if |t e - t q.2.2| < r then (1 : ℝ) else 0) := by
          simp only [mul_sum]
          rw [sum_comm]
    _ ≤ ∑ _q ∈ l.toFinset, v := sum_le_sum fun q hq => hnear q (List.mem_toFinset.mp hq)
    _ = l.toFinset.card * v := by simp
    _ ≤ l.length * v := mul_le_mul_of_nonneg_right (by exact_mod_cast List.toFinset_card_le l) hv

end Submission.Obl.k4_matching_abstract_switching_mixture
