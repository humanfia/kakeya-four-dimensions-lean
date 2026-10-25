-- Adapted from the same LOT tree, o201, session x0697, commit d395b4346c32c12a70c4bc86d657dea88e733fcd
-- Source: Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/CriticalRecords.lean
-- Earlier source attribution is retained below.
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/CriticalRecords.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited.SeparationLosses

/-! The actual regularity tests used in a three-traversal critical experiment. -/

namespace Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited

noncomputable section

open Finset Classical Set MeasureTheory
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

variable {Pal Tc : Type*}

/-- Each fresh velocity avoids only the most recently used velocity. -/
def criticalFreshSeparated (vel : Pal → ℝ) (gap : ℝ) (l : List (Pal × Tc)) (z : Pal) : Prop :=
  ∀ a ∈ l.getLast?, gap < |vel z - vel a.1|

/-- Only the second arrival must avoid the first arrival time. -/
def criticalTimeSeparated (center : Tc → ℝ) (gap : ℝ) (l : List (Pal × Tc)) (t : Tc) : Prop :=
  ∀ a, l = [a] → gap < |center t - center a.2|

def criticalRecordRegular (vel : Pal → ℝ) (center : Tc → ℝ) (gap : ℝ)
    (l : List (Pal × Tc)) : Prop :=
  l.IsChain (fun a b => gap ≤ |vel b.1 - vel a.1|) ∧
    match l with
    | a :: b :: _ => gap ≤ |center b.2 - center a.2|
    | _ => True

theorem criticalRecordRegular_nil (vel : Pal → ℝ) (center : Tc → ℝ) (gap : ℝ) :
    criticalRecordRegular vel center gap [] := by
  simp [criticalRecordRegular]

theorem criticalRecordRegular_append
    (vel : Pal → ℝ) (center : Tc → ℝ) (gap : ℝ) (l : List (Pal × Tc)) (z : Pal) (t : Tc)
    (hreg : criticalRecordRegular vel center gap l)
    (hz : criticalFreshSeparated vel gap l z) (ht : criticalTimeSeparated center gap l t) :
    criticalRecordRegular vel center gap (l ++ [(z, t)]) := by
  refine ⟨hreg.1.append (by simp) ?_, ?_⟩
  · intro a ha b hb
    have hb' : b = (z, t) := by simpa using hb.symm
    subst b
    exact (hz a ha).le
  · cases l with
    | nil => trivial
    | cons a l =>
      cases l with
      | nil => exact (ht a rfl).le
      | cons b l => exact hreg.2

theorem criticalRecordRegular_three
    (vel : Pal → ℝ) (center : Tc → ℝ) (gap : ℝ) (a b c : Pal × Tc)
    (hreg : criticalRecordRegular vel center gap [a, b, c]) :
    gap ≤ |vel b.1 - vel a.1| ∧ gap ≤ |vel c.1 - vel b.1| ∧
      gap ≤ |center b.2 - center a.2| :=
  ⟨hreg.1.rel, hreg.1.tail.rel, hreg.2⟩

variable {Ω Sf Sc Ar Iv : Type*} [Fintype Ω] [DecidableEq Sf]
  [DecidableEq Sc] [DecidableEq Ar] [DecidableEq Iv] [Fintype Pal] [DecidableEq Pal]
  [Fintype Tc] [DecidableEq Tc]

/-- The refresh separation test has one interval-cap loss, independent of
the number of earlier records. -/
theorem criticalFreshSeparated_failure_le
    (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (π : Pal → ℝ) (vel : Pal → ℝ)
    (K gap A : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hcap : ∀ e z, (∑ er ∈ univ.filter (fun er => X.Z er = z),
      condKey X.P X.fine e er) ≤ K * π z)
    (hinterval : ∀ v, (∑ z ∈ univ.filter (fun z => |vel z - v| ≤ gap), π z) ≤ A)
    (e : Ω) (l : List (Pal × Tc)) :
    (∑ er, condKey X.P X.fine e er *
      (if criticalFreshSeparated vel gap l (X.Z er) then 0 else 1)) ≤ K * A := by
  cases hl : l.getLast? with
  | none =>
    simpa [criticalFreshSeparated, hl] using mul_nonneg hK hA
  | some a =>
    let B : Finset Pal := univ.filter (fun z => |vel z - vel a.1| ≤ gap)
    have hbad := finite_refresh_bad_palette_bound X π K hcap e B
    have h := hbad.trans (mul_le_mul_of_nonneg_left (hinterval (vel a.1)) hK)
    simpa [B, criticalFreshSeparated, hl, ← not_le] using h

/-- The second-arrival time test has precisely the mesh-independent
near-time loss. All other arrivals pass this test automatically. -/
theorem criticalTimeSeparated_failure_le
    (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (hP : ∀ e, 0 ≤ X.P e)
    (prior : Bool → Ar → ℝ) (I : Tc → Set ℝ) (center : Tc → ℝ)
    (lam H d δ gap : ℝ) (hlam : 0 < lam) (hH : 0 ≤ H)
    (hd : 0 < d) (hδ : 0 ≤ δ) (hgap : 0 ≤ gap)
    (hmeas : ∀ t, MeasurableSet (I t))
    (hdisj : Pairwise (fun t u => Disjoint (I t) (I u)))
    (hvol : ∀ t, volume (I t) = ENNReal.ofReal d)
    (hnear : ∀ t s, s ∈ I t → |s - center t| ≤ δ)
    (hcell : ∀ κ a t, fiberMass X.P (fun e => (X.arm e κ, X.cell e)) (a, t) ≤
      prior κ a * (H * d))
    (er : Ω) (hh : X.heavy prior lam er false) (l : List (Pal × Tc)) :
    (∑ e', condKey X.P (X.armKey false) er e' *
      (if criticalTimeSeparated center gap l (X.cell e') then 0 else 1)) ≤
        2 * H * (gap + δ) / lam := by
  cases l with
  | nil =>
    simp [criticalTimeSeparated]
    positivity
  | cons a l =>
    cases l with
    | nil =>
      have h := finite_traversal_near_time_bound X hP prior I center lam H d δ gap (center a.2)
        hlam hH hd hδ hgap hmeas hdisj hvol hnear hcell er hh
      simpa [criticalTimeSeparated, ← not_le] using h
    | cons b l =>
      simp [criticalTimeSeparated]
      positivity

end

end Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited
