/-
Adapted from: here:o116

Original heavy-strip packing and frame proofs by session x0644.
-/

import Mathlib

/-! Second-moment packing for the heavy velocity strips in Corollary 4.13. -/

noncomputable section

namespace Submission.Lib.K4VelocityStrips

open MeasureTheory Set
open scoped BigOperators

/-- The square of the total mass of a finite family of events is controlled by
the sum of its pairwise intersection masses, under the unchanged probability law. -/
theorem event_mass_second_moment {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) [IsProbabilityMeasure μ] (E : ι → Set X)
    (hE : ∀ i, MeasurableSet (E i)) :
    (∑ i, μ.real (E i)) ^ 2 ≤ ∑ i, ∑ j, μ.real (E i ∩ E j) := by
  classical
  let f : ι → X → ℝ := fun i => (E i).indicator (fun _ => 1)
  have hf (i : ι) : MemLp (f i) 2 μ := (memLp_const 1).indicator (hE i)
  have hprod (i j : ι) :
      (fun x => f i x * f j x) = (E i ∩ E j).indicator (fun _ => 1) := by
    funext x
    by_cases hi : x ∈ E i <;> by_cases hj : x ∈ E j <;> simp [f, hi, hj]
  have hmean : (∫ x, ∑ i, f i x ∂μ) = ∑ i, μ.real (E i) := by
    rw [integral_finsetSum _ (fun i _ => (hf i).integrable one_le_two)]
    exact Finset.sum_congr rfl (fun i _ => integral_indicator_one (hE i))
  have hsecond : (∫ x, (∑ i, f i x) ^ 2 ∂μ) = ∑ i, ∑ j, μ.real (E i ∩ E j) := by
    simp_rw [pow_two, Finset.sum_mul_sum]
    rw [integral_finsetSum _ (fun i _ =>
      integrable_finsetSum _ (fun j _ => by
        rw [hprod]
        exact (integrable_const (1 : ℝ)).indicator ((hE i).inter (hE j))))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => by
      rw [hprod]
      exact (integrable_const (1 : ℝ)).indicator ((hE i).inter (hE j)))]
    apply Finset.sum_congr rfl
    intro j _
    rw [hprod]
    exact integral_indicator_one ((hE i).inter (hE j))
  have hLp : MemLp (fun x => ∑ i, f i x) 2 μ := by
    convert memLp_finsetSum' Finset.univ (fun i _ => hf i) using 1
    ext x
    simp
  have hvar := ProbabilityTheory.variance_nonneg (fun x => ∑ i, f i x) μ
  rw [ProbabilityTheory.variance_eq_sub hLp] at hvar
  change 0 ≤ (∫ x, (∑ i, f i x) ^ 2 ∂μ) - (∫ x, ∑ i, f i x ∂μ) ^ 2 at hvar
  rw [hmean, hsecond] at hvar
  linarith

/-- Heavy events with small pairwise intersections form a short list. The
intersection bound is measured in the same prior as the individual mass floors. -/
theorem heavy_event_card_le {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) [IsProbabilityMeasure μ] (E : ι → Set X)
    (hE : ∀ i, MeasurableSet (E i)) {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 ≤ ε)
    (hmass : ∀ i, κ ≤ μ.real (E i))
    (hinter : ∀ i j, i ≠ j → μ.real (E i ∩ E j) ≤ ε)
    (hsmall : 2 * ε ≤ κ ^ 2) :
    (Fintype.card ι : ℝ) ≤ 2 / κ ^ 2 := by
  classical
  let M : ℝ := Fintype.card ι
  change M ≤ 2 / κ ^ 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hfirst : M * κ ≤ ∑ i, μ.real (E i) := by
    simpa [M] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hmass i)
  have hupper : (∑ i, ∑ j, μ.real (E i ∩ E j)) ≤ M + ε * M ^ 2 := by
    calc
      _ ≤ ∑ i : ι, ∑ j : ι, ((if i = j then 1 else 0) + ε) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        by_cases hij : i = j
        · subst j
          have hle : μ.real (E i) ≤ 1 := by
            simp
          simp only [inter_self, ite_true]
          linarith
        · simpa [hij] using hinter i j hij
      _ = M + ε * M ^ 2 := by
        simp [Finset.sum_add_distrib, M]
        ring
  have hsq : (M * κ) ^ 2 ≤ M + ε * M ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity) |>.mpr hfirst).trans
      ((event_mass_second_moment μ E hE).trans hupper)
  by_cases hzero : M = 0
  · simpa only [hzero] using (show (0 : ℝ) ≤ 2 / κ ^ 2 by positivity)
  · have hMp : 0 < M := lt_of_le_of_ne hM (Ne.symm hzero)
    apply (le_div_iff₀ (sq_pos_of_pos hκ)).mpr
    have hmul := mul_le_mul_of_nonneg_right hsmall (sq_nonneg M)
    have hfactor : M * (M * κ ^ 2 - 2) ≤ 0 := by nlinarith [hsq]
    by_contra! hn
    have hn' : 0 < M * κ ^ 2 - 2 := by linarith
    exact (not_lt_of_ge hfactor) (mul_pos hMp hn')

end Submission.Lib.K4VelocityStrips
