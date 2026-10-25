-- Adapted from the same LOT tree, o201, session x0697, commit d395b4346c32c12a70c4bc86d657dea88e733fcd
-- Source: Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/CriticalTerminal.lean
-- Earlier source attribution is retained below.
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/CriticalTerminal.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited.CriticalTracking

/-! A terminal test dominated by a regular critical endpoint record. -/

namespace Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited

noncomputable section

open Finset Classical Set MeasureTheory
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

variable {Pal Tc : Type*}

def criticalReferenceTest (vel : Pal → ℝ) (center : Tc → ℝ) (q : Fin 3 → ℝ)
    (gap R : ℝ) (u : Fin 3 → ℝ) (l : List (Pal × Tc)) : ℝ :=
  if l.length = 3 then
    if criticalRecordRegular vel center gap l ∧
        ∀ i, |horizontalPrediction vel center q l i - u i| ≤ R then 1 else 0
    else 1

theorem criticalReferenceTest_nonneg (vel : Pal → ℝ) (center : Tc → ℝ) (q : Fin 3 → ℝ)
    (gap R : ℝ) (u : Fin 3 → ℝ) (l : List (Pal × Tc)) :
    0 ≤ criticalReferenceTest vel center q gap R u l := by
  unfold criticalReferenceTest
  split_ifs <;> norm_num

theorem horizontalPrediction_ofFn_three
    (vel : Pal → ℝ) (center : Tc → ℝ) (q : Fin 3 → ℝ)
    (zs : Fin 3 → Pal) (ts : Fin 3 → Tc) :
    horizontalPrediction vel center q (List.ofFn (fun i => (zs i, ts i))) =
      criticalEndpoint (fun i => vel (zs i)) q
        (center (ts 2), fun i : Fin 2 => center (ts i.castSucc)) := by
  have hl : List.ofFn (fun i => (zs i, ts i)) =
      [(zs 0, ts 0), (zs 1, ts 1), (zs 2, ts 2)] := by
    simp [List.ofFn_succ]
  have hc : (![vel (zs 0), vel (zs 1), vel (zs 2)] : Fin 3 → ℝ) =
      (fun i => vel (zs i)) := by
    ext i
    fin_cases i <;> rfl
  have ht : (![center (ts 0), center (ts 1)] : Fin 2 → ℝ) =
      (fun i : Fin 2 => center (ts i.castSucc)) := by
    ext i
    fin_cases i <;> rfl
  rw [hl, horizontalPrediction_three, hc, ht]

/-- On a triple, the reference test implies exactly the regularity and
endpoint conditions required by the analytic critical cell cap. -/
theorem criticalReferenceTest_three_le
    (vel : Pal → ℝ) (center : Tc → ℝ) (q : Fin 3 → ℝ) (K R : ℝ) (u : Fin 3 → ℝ)
    (hvel : ∀ z, |vel z| ≤ K) (zs : Fin 3 → Pal) (ts : Fin 3 → Tc) :
    criticalReferenceTest vel center q K⁻¹ R u (List.ofFn (fun i => (zs i, ts i))) ≤
      if ((∀ i, |vel (zs i)| ≤ K) ∧
          (∀ i : Fin 2, K⁻¹ ≤ |vel (zs i.succ) - vel (zs i.castSucc)|)) ∧
        (K⁻¹ ≤ |center (ts 1) - center (ts 0)| ∧
          ∀ i, |criticalEndpoint (fun j => vel (zs j)) q
            (center (ts 2), fun j : Fin 2 => center (ts j.castSucc)) i - u i| ≤ R)
      then 1 else 0 := by
  let l := List.ofFn (fun i => (zs i, ts i))
  have hlen : l.length = 3 := List.length_ofFn
  have hlist : l = [(zs 0, ts 0), (zs 1, ts 1), (zs 2, ts 2)] := by
    simp [l, List.ofFn_succ]
  change criticalReferenceTest vel center q K⁻¹ R u l ≤ _
  by_cases hg : criticalRecordRegular vel center K⁻¹ l ∧
      ∀ i, |horizontalPrediction vel center q l i - u i| ≤ R
  · have hreg := criticalRecordRegular_three vel center K⁻¹
      (zs 0, ts 0) (zs 1, ts 1) (zs 2, ts 2) (by rw [← hlist]; exact hg.1)
    have hsep : ∀ i : Fin 2, K⁻¹ ≤ |vel (zs i.succ) - vel (zs i.castSucc)| := by
      intro i
      fin_cases i
      · simpa using hreg.1
      · simpa using hreg.2.1
    have hnear : ∀ i, |criticalEndpoint (fun j => vel (zs j)) q
        (center (ts 2), fun j : Fin 2 => center (ts j.castSucc)) i - u i| ≤ R := by
      simpa only [l, horizontalPrediction_ofFn_three] using hg.2
    have hcontrol : ∀ i : Fin 3, |vel (zs i)| ≤ K := fun i => hvel (zs i)
    simp [criticalReferenceTest, hlen, hg, hcontrol, hsep, hreg.2.2, hnear]
  · have hz : criticalReferenceTest vel center q K⁻¹ R u l = 0 := by
      simp only [criticalReferenceTest, hlen, ite_true, hg, ite_false]
    rw [hz]
    split_ifs <;> norm_num

variable {Ω Sf Sc Ar Iv : Type*} [Fintype Ω] [DecidableEq Sf]
  [DecidableEq Sc] [DecidableEq Ar] [DecidableEq Iv] [Fintype Pal] [DecidableEq Pal]
  [Fintype Tc] [DecidableEq Tc]

/-- A tracking endpoint in a specified actual cell is dominated by the
independent record test. Record lengths other than three cause no difficulty. -/
theorem criticalTracking_terminal_le_reference
    {X : SwitchData Ω Sf Sc Ar Iv Pal Tc} {vel : Pal → ℝ} {center : Tc → ℝ} {K E δx δt : ℝ}
    (D : FiniteHorizontalGeometry X vel center K E δx δt)
    (A gap r R : ℝ) (herror : criticalPredictionError K A 3 + r ≤ R)
    {Cell : Type*} [DecidableEq Cell] (cell : Ω → Cell) (u : Cell → Fin 3 → ℝ)
    (hcell : ∀ e, 0 < X.P e → ∀ i, |D.point e i - u (cell e) i| ≤ r)
    (s e : Ω) (l : List (Pal × Tc)) (target : Cell) :
    (if cell e = target then (if CriticalTracking D A gap s e l then 1 else 0) else 0) ≤
      criticalReferenceTest vel center (D.point s) gap R (u target) l := by
  by_cases he : cell e = target
  swap
  · simpa only [he, ite_false] using
      criticalReferenceTest_nonneg vel center (D.point s) gap R (u target) l
  by_cases hq : CriticalTracking D A gap s e l
  swap
  · simpa only [he, hq, ite_true, ite_false] using
      criticalReferenceTest_nonneg vel center (D.point s) gap R (u target) l
  by_cases hlen : l.length = 3
  swap
  · simp only [he, hq, criticalReferenceTest, hlen, ite_true, ite_false, le_refl]
  have hnear : ∀ i, |horizontalPrediction vel center (D.point s) l i - u target i| ≤ R := by
    intro i
    have hp := hq.2.2.1 i
    rw [hlen] at hp
    have hc := hcell e hq.1 i
    rw [he] at hc
    exact (abs_sub_le _ (D.point e i) _).trans ((add_le_add hp hc).trans herror)
  simp [he, hq, criticalReferenceTest, hlen, hq.2.2.2, hnear]

end

end Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited
