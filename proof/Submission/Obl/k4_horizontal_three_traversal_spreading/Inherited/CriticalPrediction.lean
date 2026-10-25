-- Adapted from the same LOT tree, o201, session x0697, commit d395b4346c32c12a70c4bc86d657dea88e733fcd
-- Source: Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/CriticalPrediction.lean
-- Earlier source attribution is retained below.
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/CriticalPrediction.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited.CriticalSimulation

/-! Exact prediction from palette/time records, with an explicit error recurrence. -/

namespace Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited

noncomputable section

variable {Pal Tc : Type*}

def horizontalNext (vel : Pal → ℝ) (center : Tc → ℝ) (p : Fin 3 → ℝ) (r : Pal × Tc) :
    Fin 3 → ℝ :=
  ![center r.2, horizontalTraverse (vel r.1) (p 0) (center r.2) ![p 1, p 2] 0,
    horizontalTraverse (vel r.1) (p 0) (center r.2) ![p 1, p 2] 1]

def horizontalPrediction (vel : Pal → ℝ) (center : Tc → ℝ) (p : Fin 3 → ℝ)
    (l : List (Pal × Tc)) : Fin 3 → ℝ :=
  l.foldl (horizontalNext vel center) p

theorem horizontalPrediction_nil (vel : Pal → ℝ) (center : Tc → ℝ) (p : Fin 3 → ℝ) :
    horizontalPrediction vel center p [] = p := rfl

theorem horizontalPrediction_append (vel : Pal → ℝ) (center : Tc → ℝ) (p : Fin 3 → ℝ)
    (l : List (Pal × Tc)) (r : Pal × Tc) :
    horizontalPrediction vel center p (l ++ [r]) =
      horizontalNext vel center (horizontalPrediction vel center p l) r := by
  simp [horizontalPrediction, List.foldl_append]

theorem horizontalPrediction_three (vel : Pal → ℝ) (center : Tc → ℝ) (p : Fin 3 → ℝ)
    (z₀ z₁ z₂ : Pal) (t₀ t₁ t₂ : Tc) :
    horizontalPrediction vel center p [(z₀, t₀), (z₁, t₁), (z₂, t₂)] =
      criticalEndpoint ![vel z₀, vel z₁, vel z₂] p (center t₂, ![center t₀, center t₁]) := by
  ext i
  fin_cases i <;>
    simp [horizontalPrediction, horizontalNext, criticalEndpoint,
      criticalSpatialEndpoint, horizontalTraverse] <;> ring

/-- Changing only the end time of a traversal has a uniform bound independent
of the transverse coordinate. -/
theorem horizontalTraverse_end_time_error
    (c t s s' K δ : ℝ) (z : Fin 2 → ℝ)
    (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hc : |c| ≤ K) (hz : |z 0| ≤ K)
    (ht : |t| ≤ 1) (hss : |s - s'| ≤ δ) :
    ∀ i, |horizontalTraverse c t s z i - horizontalTraverse c t s' z i| ≤ 2 * K * δ := by
  have hco : |-z 0 + t * c| ≤ 2 * K := by
    calc
      _ ≤ |z 0| + |t| * |c| := by simpa only [abs_neg, abs_mul] using abs_add_le (-z 0) (t * c)
      _ ≤ K + 1 * K := add_le_add hz (mul_le_mul ht hc (abs_nonneg _) zero_le_one)
      _ = _ := by ring
  intro i
  fin_cases i
  · change |z 0 + c * (s - t) - (z 0 + c * (s' - t))| ≤ _
    calc
      _ = |c * (s - s')| := by congr 1; ring
      _ ≤ K * δ := by rw [abs_mul]; exact mul_le_mul hc hss (abs_nonneg _) hK
      _ ≤ _ := by nlinarith
  · change |z 1 + (-z 0 + t * c) * (s - t) -
      (z 1 + (-z 0 + t * c) * (s' - t))| ≤ _
    calc
      _ = |(-z 0 + t * c) * (s - s')| := by congr 1; ring
      _ ≤ (2 * K) * δ := by
        rw [abs_mul]
        exact mul_le_mul hco hss (abs_nonneg _) (by positivity)
      _ = _ := by ring

/-- One recorded step combines a trajectory error, an end-time representative
error, and a difference between the predicted and refreshed starts. -/
theorem horizontalNext_step_error
    (vel : Pal → ℝ) (center : Tc → ℝ) (q qf qa : Fin 3 → ℝ) (r : Pal × Tc)
    (K E D δ : ℝ) (hK : 1 ≤ K) (hE : 0 ≤ E) (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hc : |vel r.1| ≤ K) (hqf : |qf 1| ≤ K)
    (hqT : q 0 ∈ Set.Icc (0 : ℝ) 1) (hqfT : qf 0 ∈ Set.Icc (0 : ℝ) 1)
    (hcenter : center r.2 ∈ Set.Icc (0 : ℝ) 1)
    (hnear : ∀ i, |q i - qf i| ≤ D) (htime : |qa 0 - center r.2| ≤ δ)
    (htrajectory : ∀ i : Fin 2,
      |qa i.succ - horizontalTraverse (vel r.1) (qf 0) (qa 0) ![qf 1, qf 2] i| ≤ E) :
    ∀ i, |qa i - horizontalNext vel center q r i| ≤ E + 2 * K * δ + 6 * K * D := by
  have hK0 : 0 ≤ K := by linarith
  have hspace : ∀ i : Fin 2, |(![q 1, q 2] : Fin 2 → ℝ) i - ![qf 1, qf 2] i| ≤ D := by
    intro i
    fin_cases i
    · exact hnear 1
    · exact hnear 2
  have hrefresh := horizontalTraverse_refresh_error (vel r.1) (q 0) (qf 0) (center r.2) K D
    ![q 1, q 2] ![qf 1, qf 2] hK hD hc hqf hqT hqfT hcenter (hnear 0) hspace
  have hqft : |qf 0| ≤ 1 := abs_le.mpr ⟨by linarith [hqfT.1], hqfT.2⟩
  have hend := horizontalTraverse_end_time_error (vel r.1) (qf 0) (qa 0) (center r.2) K δ
    ![qf 1, qf 2] hK0 hδ hc hqf hqft htime
  have hspatial (j : Fin 2) :
      |qa j.succ - horizontalTraverse (vel r.1) (q 0) (center r.2) ![q 1, q 2] j| ≤
        E + 2 * K * δ + 6 * K * D := by
    have hr : |horizontalTraverse (vel r.1) (qf 0) (center r.2) ![qf 1, qf 2] j -
        horizontalTraverse (vel r.1) (q 0) (center r.2) ![q 1, q 2] j| ≤ 6 * K * D := by
      simpa only [abs_sub_comm] using hrefresh j
    calc
      _ ≤ |qa j.succ - horizontalTraverse (vel r.1) (qf 0) (center r.2) ![qf 1, qf 2] j| +
          |horizontalTraverse (vel r.1) (qf 0) (center r.2) ![qf 1, qf 2] j -
            horizontalTraverse (vel r.1) (q 0) (center r.2) ![q 1, q 2] j| := abs_sub_le _ _ _
      _ ≤ (E + 2 * K * δ) + 6 * K * D := by
        apply add_le_add _ hr
        exact (abs_sub_le _ (horizontalTraverse (vel r.1) (qf 0) (qa 0) ![qf 1, qf 2] j) _).trans
          (add_le_add (htrajectory j) (hend j))
  intro i
  fin_cases i
  · change |qa 0 - center r.2| ≤ _
    have hKD : δ ≤ K * δ := by nlinarith
    nlinarith [mul_nonneg hK0 hD]
  · simpa [horizontalNext] using hspatial 0
  · simpa [horizontalNext] using hspatial 1

def criticalPredictionError (K A : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => A + 6 * K * criticalPredictionError K A n

theorem criticalPredictionError_nonneg (K A : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A) :
    ∀ n, 0 ≤ criticalPredictionError K A n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => exact add_nonneg hA (mul_nonneg (by positivity) ih)

theorem criticalPredictionError_three (K A : ℝ) :
    criticalPredictionError K A 3 = (1 + 6 * K + 36 * K ^ 2) * A := by
  simp [criticalPredictionError]
  ring

end

end Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited
