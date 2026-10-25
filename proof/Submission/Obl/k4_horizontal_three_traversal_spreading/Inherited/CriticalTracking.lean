-- Adapted from the same LOT tree, o201, session x0697, commit d395b4346c32c12a70c4bc86d657dea88e733fcd
-- Source: Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/CriticalTracking.lean
-- Earlier source attribution is retained below.
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/CriticalTracking.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited.CriticalPrediction
import Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited.CriticalRecords

/-! A concrete full-past invariant for the finite critical switching experiment. -/

namespace Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited

noncomputable section

open Finset Classical Set MeasureTheory
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

variable {Ω Sf Sc Ar Iv Pal Tc : Type*} [Fintype Ω] [DecidableEq Sf]
  [DecidableEq Sc] [DecidableEq Ar] [DecidableEq Iv] [Fintype Pal] [DecidableEq Pal]
  [Fintype Tc] [DecidableEq Tc]

/-- Geometric certificates for actual finite states. All support bounds are
required only on states with positive original mass. -/
structure FiniteHorizontalGeometry (X : SwitchData Ω Sf Sc Ar Iv Pal Tc)
    (vel : Pal → ℝ) (center : Tc → ℝ) (K E δx δt : ℝ) where
  point : Ω → Fin 3 → ℝ
  point_time : ∀ e, 0 < X.P e → point e 0 ∈ Set.Icc (0 : ℝ) 1
  point_horizontal : ∀ e, 0 < X.P e → |point e 1| ≤ K
  center_time : ∀ t, center t ∈ Set.Icc (0 : ℝ) 1
  control_bound : ∀ z, |vel z| ≤ K
  time_near : ∀ e, 0 < X.P e → |point e 0 - center (X.cell e)| ≤ δt
  refresh_close : ∀ e er, 0 < X.P e → 0 < X.P er → X.fine e = X.fine er →
    ∀ i, |point e i - point er i| ≤ δx
  traverse_close : ∀ er e', 0 < X.P er → 0 < X.P e' →
    X.armKey false er = X.armKey false e' →
    ∀ i : Fin 2, |point e' i.succ - horizontalTraverse (vel (X.Z er))
      (point er 0) (point e' 0) ![point er 1, point er 2] i| ≤ E

def CriticalTracking {X : SwitchData Ω Sf Sc Ar Iv Pal Tc}
    {vel : Pal → ℝ} {center : Tc → ℝ} {K E δx δt : ℝ}
    (D : FiniteHorizontalGeometry X vel center K E δx δt) (A gap : ℝ)
    (s e : Ω) (l : List (Pal × Tc)) : Prop :=
  0 < X.P e ∧
    horizontalPrediction vel center (D.point s) l 0 ∈ Set.Icc (0 : ℝ) 1 ∧
    (∀ i, |horizontalPrediction vel center (D.point s) l i - D.point e i| ≤
      criticalPredictionError K A l.length) ∧
    criticalRecordRegular vel center gap l

theorem criticalTracking_start
    {X : SwitchData Ω Sf Sc Ar Iv Pal Tc} {vel : Pal → ℝ} {center : Tc → ℝ} {K E δx δt : ℝ}
    (D : FiniteHorizontalGeometry X vel center K E δx δt) (A gap : ℝ) (s : Ω)
    (hs : 0 < X.P s) : CriticalTracking D A gap s s [] := by
  refine ⟨hs, ?_, ?_, criticalRecordRegular_nil vel center gap⟩
  · simpa only [horizontalPrediction_nil] using D.point_time s hs
  · intro i
    simp [horizontalPrediction, criticalPredictionError]

/-- The concrete tracking invariant is stable under every retained refresh
and traversal, with the exact regularity tests used by the survival estimate. -/
theorem criticalTracking_step
    {X : SwitchData Ω Sf Sc Ar Iv Pal Tc} (hP : ∀ e, 0 ≤ X.P e)
    {vel : Pal → ℝ} {center : Tc → ℝ} {K E δx δt : ℝ}
    (D : FiniteHorizontalGeometry X vel center K E δx δt)
    (A gap : ℝ) (hK : 1 ≤ K) (hE : 0 ≤ E) (hδx : 0 ≤ δx) (hδt : 0 ≤ δt)
    (hA : 0 ≤ A) (hbudget : E + 2 * K * δt + 6 * K * δx ≤ A)
    (s e er e' : Ω) (l : List (Pal × Tc))
    (hq : CriticalTracking D A gap s e l)
    (hf : condKey X.P X.fine e er ≠ 0)
    (hl : condKey X.P (X.armKey false) er e' ≠ 0)
    (hz : criticalFreshSeparated vel gap l (X.Z er))
    (ht : criticalTimeSeparated center gap l (X.cell e')) :
    CriticalTracking D A gap s e' (l ++ [(X.Z er, X.cell e')]) := by
  have her : 0 < X.P er := condKey_pos_of_ne hP X.fine hf
  have he' : 0 < X.P e' := condKey_pos_of_ne hP (X.armKey false) hl
  let M := criticalPredictionError K A l.length
  have hM : 0 ≤ M := criticalPredictionError_nonneg K A (by linarith) hA l.length
  have hnear : ∀ i, |horizontalPrediction vel center (D.point s) l i - D.point er i| ≤ M + δx := by
    intro i
    exact (abs_sub_le _ (D.point e i) _).trans (add_le_add (hq.2.2.1 i)
      (D.refresh_close e er hq.1 her (condKey_key_eq X.fine hf).symm i))
  have hstep := horizontalNext_step_error vel center
    (horizontalPrediction vel center (D.point s) l) (D.point er) (D.point e')
    (X.Z er, X.cell e') K E (M + δx) δt hK hE (add_nonneg hM hδx) hδt
    (D.control_bound (X.Z er)) (D.point_horizontal er her) hq.2.1 (D.point_time er her)
    (D.center_time (X.cell e')) hnear (D.time_near e' he')
    (D.traverse_close er e' her he' (condKey_key_eq (X.armKey false) hl).symm)
  refine ⟨he', ?_, ?_, criticalRecordRegular_append vel center gap l (X.Z er) (X.cell e')
    hq.2.2.2 hz ht⟩
  · rw [horizontalPrediction_append]
    simpa [horizontalNext] using D.center_time (X.cell e')
  · intro i
    rw [horizontalPrediction_append]
    have hpoint : |horizontalNext vel center
        (horizontalPrediction vel center (D.point s) l) (X.Z er, X.cell e') i - D.point e' i| ≤
        E + 2 * K * δt + 6 * K * (M + δx) := by
      simpa only [abs_sub_comm] using hstep i
    refine hpoint.trans ?_
    simp only [List.length_append, List.length_singleton, criticalPredictionError]
    dsimp [M]
    nlinarith only [hbudget]

end

end Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited
