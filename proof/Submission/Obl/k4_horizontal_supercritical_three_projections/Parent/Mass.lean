/-
Adapted from this LOT tree o203, session x0699, commit 4341160d,
Submission/Obl/k4_horizontal_supercritical_rate_candidates/Mass.lean (namespace
Submission.Obl.k4_horizontal_supercritical_rate_candidates renamed to
Submission.Obl.k4_horizontal_supercritical_three_projections.Parent).
-/
import Submission.Obl.k4_scalar_angular_pair_agreement.BadPairs

namespace Submission.Obl.k4_horizontal_supercritical_three_projections.Parent

open MeasureTheory Set
open scoped ENNReal

/-- Count whole true-label witnesses in a common box. Assignments need be
disjoint only within the same time block. -/
theorem whole_witness_count {X ι κ : Type*} [MeasurableSpace X] [DecidableEq κ]
    (μ : Measure X) (S : Finset ι) (j : ι → κ) (W : ι → Set X) (Z : Set X)
    {m V : ℝ} (_hm : 0 ≤ m) (hV : 0 ≤ V)
    (hW : ∀ i ∈ S, MeasurableSet (W i))
    (hdisj : ∀ i ∈ S, ∀ i' ∈ S, i ≠ i' → j i = j i' → Disjoint (W i) (W i'))
    (hsub : ∀ i ∈ S, W i ⊆ Z)
    (hfloor : ∀ i ∈ S, ENNReal.ofReal m ≤ μ (W i))
    (hcap : μ Z ≤ ENNReal.ofReal V) :
    (S.card : ℝ) * m ≤ ((S.image j).card : ℝ) * V := by
  have hsum : ENNReal.ofReal ((S.card : ℝ) * m) ≤ ∑ i ∈ S, μ (W i) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
      ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum hfloor
  have hbound := hsum.trans
    ((Submission.Obl.k4_scalar_angular_pair_agreement.sum_le_card_image_mul
      μ S j W Z hW hdisj hsub).trans (mul_le_mul' le_rfl hcap))
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Nat.cast_nonneg _) hV)).mp hbound

/-- The sum of full trajectory assignments over the occupied blocks has the
correct reference budget, irrespective of the current residual law. -/
theorem full_assignment_budget {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (ν : Measure X) [IsProbabilityMeasure ν] (T : ℕ)
    (j : ι → Fin (2 ^ T)) (A : ι → Set X)
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i')) :
    (∑ i, ν (A i)) ≤ (2 : ENNReal) ^ T := by
  classical
  have h := Submission.Obl.k4_scalar_angular_pair_agreement.sum_le_card_image_mul
    ν Finset.univ j A univ (fun i _ => hA i)
    (fun i _ i' _ => hdisj i i') (fun _ _ => subset_univ _)
  simp only [measure_univ, mul_one] at h
  apply h.trans
  have hc : (Finset.univ.image j).card ≤ 2 ^ T := by
    simpa using (Finset.card_le_univ (Finset.univ.image j))
  exact_mod_cast hc

/-- A fixed mass bound on each true label is charged to the original full
assignment budget. -/
theorem sum_full_label_weights_le_one {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (ν : Measure X) [IsProbabilityMeasure ν] (T : ℕ)
    (j : ι → Fin (2 ^ T)) (A : ι → Set X)
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i')) :
    (∑ i, ((2 : ENNReal) ^ T)⁻¹ * ν (A i)) ≤ 1 := by
  rw [← Finset.mul_sum]
  calc
    _ ≤ ((2 : ENNReal) ^ T)⁻¹ * (2 : ENNReal) ^ T :=
      mul_le_mul' le_rfl (full_assignment_budget ν T j A hA hdisj)
    _ = 1 := ENNReal.inv_mul_cancel (by positivity) (by finiteness)

/-- Earlier disjoint assignment floors give a summable reference budget even
after the current law has been restricted further. -/
theorem original_reference_budget {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Finset ι) (E : ι → Set X) (w : ι → ℝ)
    {L K : ℝ} (hL : 0 < L) (hK : 0 ≤ K)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hE : ∀ i ∈ S, MeasurableSet (E i))
    (hdisj : (S : Set ι).PairwiseDisjoint E)
    (hfloor : ∀ i ∈ S, ENNReal.ofReal (w i / L) ≤ μ (E i))
    (hmass : μ univ ≤ ENNReal.ofReal K) :
    ∑ i ∈ S, w i ≤ L * K := by
  have hsum : ENNReal.ofReal ((∑ i ∈ S, w i) / L) ≤ μ univ := by
    calc
      _ = ∑ i ∈ S, ENNReal.ofReal (w i / L) := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
        exact ENNReal.ofReal_sum_of_nonneg
          (fun i hi => mul_nonneg (hw i hi) (inv_nonneg.mpr hL.le))
      _ ≤ ∑ i ∈ S, μ (E i) := Finset.sum_le_sum hfloor
      _ = μ (⋃ i ∈ S, E i) := (measure_biUnion_finset hdisj hE).symm
      _ ≤ μ univ := measure_mono (subset_univ _)
  have hreal := (ENNReal.ofReal_le_ofReal_iff hK).mp (hsum.trans hmass)
  have hmul := (div_le_iff₀ hL).mp hreal
  simpa only [mul_comm] using hmul

end Submission.Obl.k4_horizontal_supercritical_three_projections.Parent
