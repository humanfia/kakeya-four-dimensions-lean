-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/NormalizedPairDeletion.lean. Existing attribution comments are retained below.

import Submission.Obl.k4_paired_test_normalization.NormalizedSublevel
import Submission.Obl.k4_paired_test_normalization.DiscriminantDegree
import Submission.Obl.k4_paired_test_normalization.PairDeletion

namespace Submission.Obl.k4_paired_test_normalization

open MvPolynomial Set Metric MeasureTheory

/-- Normalize a finite family and remove the small discriminants in both roles.
Only labels that occur in a pair require a coefficient-size lower bound. -/
theorem normalized_pair_deletion :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
        (μ : Measure Ω) (H : ι → ι → Set Ω)
        (P : ι → MvPolynomial (Fin 4) ℝ)
        (z : ι → Ω → EuclideanSpace ℝ (Fin 3)) (β : ι → ℝ)
        (ρ η θ : ℝ),
      (∀ i j, MeasurableSet (H i j)) →
      (∀ j, Pairwise fun i k => Disjoint (H i j) (H k j)) →
      (∀ i, (P i).totalDegree ≤ 2) →
      (∀ i, Measurable (z i)) →
      (∀ i, 0 ≤ β i) →
      (∀ i, ((⋃ j, H i j) ∪ (⋃ j, H j i)).Nonempty →
        ρ ≤ coefficientSize (disc (P i))) →
      (∀ i p, p ∈ (⋃ j, H i j) ∪ (⋃ j, H j i) → ‖z i p‖ ≤ 1 / 8) →
      (∀ i p, p ∈ (⋃ j, H i j) ∪ (⋃ j, H j i) →
        0 ≤ eval (fun k => z i p k) (disc (P i))) →
      (∀ i (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
        μ ((⋃ j, H i j) ∩ (z i ⁻¹' U)) ≤ ENNReal.ofReal (β i) * volume U) →
      (∀ i (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
        μ ((⋃ j, H j i) ∩ (z i ⁻¹' U)) ≤ ENNReal.ofReal (β i) * volume U) →
      0 < ρ → 0 ≤ η → 0 < θ → θ ≤ 1 →
      1152 * C * η < min ρ 1 * θ ^ 2 →
      ∃ (t : ι → ℝ) (H' : ι → ι → Set Ω),
        (∀ i, 0 < t i ∧ t i ≤ 1) ∧
        (∀ i m, |(disc (MvPolynomial.C (t i) * P i)).coeff m| ≤ 1) ∧
        (∀ i j, MeasurableSet (H' i j) ∧ H' i j ⊆ H i j) ∧
        (∀ i j p, p ∈ H' i j →
          η < eval (fun k => z i p k) (disc (MvPolynomial.C (t i) * P i)) ∧
          η < eval (fun k => z j p k) (disc (MvPolynomial.C (t j) * P j))) ∧
        (∑ i, μ (⋃ j, H i j)) ≤ (∑ i, μ (⋃ j, H' i j)) +
          2 * ∑ i, ENNReal.ofReal (β i) *
            (ENNReal.ofReal (128 * θ) *
              volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 8))) := by
  classical
  obtain ⟨C, hC, hsublevel⟩ := coefficient_size_sublevel
  refine ⟨C, hC, ?_⟩
  intro Ω ι _ _ μ H P z β ρ η θ hH hdisj hP hz hβ hanchor hinside hpositive
    hsource hwitness hρ hη hθ hθ1 hsmall
  choose t ht ht1 hcoeff hsize using fun i => exists_discriminant_normalization (P i)
  let Q (i : ι) := disc (MvPolynomial.C (t i) * P i)
  let U (i : ι) : Set (EuclideanSpace ℝ (Fin 3)) :=
    {x | x ∈ closedBall 0 (1 / 8) ∧ |eval (fun k => x k) (Q i)| ≤ η}
  let Bad (i : ι) : Set Ω := z i ⁻¹' U i
  let H' (i j : ι) := H i j \ (Bad i ∪ Bad j)
  let v : ENNReal := ENNReal.ofReal (128 * θ) *
    volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 8))
  have hU (i : ι) : MeasurableSet (U i) := by
    apply MeasurableSet.inter isClosed_closedBall.measurableSet
    exact measurableSet_le
      (((MvPolynomial.continuous_eval (Q i)).comp
        (PiLp.continuous_ofLp 2 _)).abs.measurable) measurable_const
  have hBad (i : ι) : MeasurableSet (Bad i) := (hU i).preimage (hz i)
  have hvol (i : ι) (hi : ((⋃ j, H i j) ∪ (⋃ j, H j i)).Nonempty) :
      volume (U i) ≤ v := by
    have hdegree : (Q i).totalDegree ≤ 2 := by
      dsimp [Q]
      exact disc_totalDegree_le _ ((totalDegree_C_mul_le _ _).trans (hP i))
    apply hsublevel (Q i) hdegree (min ρ 1 / 2) η θ ?_ hθ hθ1 hη ?_
    · exact (div_le_div_of_nonneg_right
        (min_le_min_right 1 (hanchor i hi)) (by norm_num)).trans (hsize i)
    · nlinarith
  have hmarg (i : ι) (S : Set Ω)
      (hS : S ⊆ (⋃ j, H i j) ∪ (⋃ j, H j i))
      (hdensity : ∀ U : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet U →
        μ (S ∩ z i ⁻¹' U) ≤ ENNReal.ofReal (β i) * volume U) :
      μ (S ∩ Bad i) ≤ ENNReal.ofReal (β i) * v := by
    by_cases hSne : S.Nonempty
    · apply (hdensity (U i) (hU i)).trans
      gcongr
      exact hvol i (hSne.mono hS)
    · rw [Set.not_nonempty_iff_eq_empty.mp hSne, empty_inter, measure_empty]
      exact bot_le
  have hloss := two_role_deletion_bound μ H Bad
    (fun i => ENNReal.ofReal (β i) * v) hH hBad hdisj
    (fun i => hmarg i _ subset_union_left (hsource i))
    (fun i => hmarg i _ subset_union_right (hwitness i))
  refine ⟨t, H', fun i => ⟨ht i, ht1 i⟩, hcoeff, ?_, ?_, hloss⟩
  · intro i j
    exact ⟨(hH i j).diff ((hBad i).union (hBad j)), sdiff_subset⟩
  · intro i j p hp
    have hpair : p ∈ H i j := hp.1
    have hi : p ∈ (⋃ j, H i j) ∪ (⋃ j, H j i) :=
      Or.inl (mem_iUnion.mpr ⟨j, hpair⟩)
    have hj : p ∈ (⋃ k, H j k) ∪ (⋃ k, H k j) :=
      Or.inr (mem_iUnion.mpr ⟨i, hpair⟩)
    have hret (s : ι) (hs : p ∈ (⋃ j, H s j) ∪ (⋃ j, H j s))
        (hnot : p ∉ Bad s) : η < eval (fun k => z s p k) (Q s) := by
      have hnonneg : 0 ≤ eval (fun k => z s p k) (Q s) := by
        dsimp [Q]
        rw [disc_C_mul, eval_mul, eval_C]
        exact mul_nonneg (sq_nonneg _) (hpositive s p hs)
      apply lt_of_not_ge
      intro hle
      apply hnot
      exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hinside s p hs,
        by rwa [abs_of_nonneg hnonneg]⟩
    exact ⟨hret i hi (fun h => hp.2 (Or.inl h)),
      hret j hj (fun h => hp.2 (Or.inr h))⟩

end Submission.Obl.k4_paired_test_normalization
