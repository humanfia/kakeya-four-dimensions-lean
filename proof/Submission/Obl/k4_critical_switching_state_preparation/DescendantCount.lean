/- Adapted from this LOT tree, obligation o212, session x0762, commit ecff5a0a89fd,
   Submission/Obl/k4_critical_intercept_concentration/DescendantCount.lean.
   Existing source attributions below are preserved. -/
/- Adapted from this LOT tree, obligation o201, session x0697, commit 74bd9a876bac,
   Submission/Obl/k4_horizontal_critical_rate_candidates/DescendantCount.lean.
   Original source attributions below are preserved. -/
import Submission.Obl.k4_scalar_angular_pair_agreement.BadPairs
import Submission.Obl.k4_scalar_angular_pair_agreement.Dyadic

/-! Full assignment weights bound the number of true descendants.
The time-block ratio supplies one of the four powers in the critical count. -/

namespace Submission.Obl.k4_critical_switching_state_preparation

open MeasureTheory Set Finset
open scoped ENNReal BigOperators

noncomputable section

/-- Charge every descendant's original trajectory floor, grouping only by its
actual time block. The surviving incidence law does not enter this count. -/
theorem descendant_assignment_count {α ι : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] (S : Finset ι)
    {T Tp : ℕ} (hT : Tp ≤ T) (jp : Fin (2 ^ Tp))
    (j : ι → Fin (2 ^ T)) (A : ι → Set α) (Ap : Set α)
    (hA : ∀ i ∈ S, MeasurableSet (A i))
    (hdisj : ∀ i ∈ S, ∀ i' ∈ S, i ≠ i' → j i = j i' → Disjoint (A i) (A i'))
    (hsub : ∀ i ∈ S, A i ⊆ Ap)
    (htime : ∀ i ∈ S,
      Submission.Obl.k4_scalar_linear_critical_extremizers.Split.I T (j i) ⊆
        Submission.Obl.k4_scalar_linear_critical_extremizers.Split.I Tp jp)
    (θ : ℝ) (hθ : 0 < θ)
    (hfloor : ∀ i ∈ S, ENNReal.ofReal θ ≤ ν (A i)) :
    (S.card : ℝ) ≤ (2 : ℝ) ^ (T - Tp) * ν.real Ap / θ := by
  classical
  have hcard : (S.image j).card ≤ 2 ^ (T - Tp) := by
    refine (Finset.card_le_card ?_).trans
      (Submission.Obl.k4_scalar_angular_pair_agreement.card_fine_le hT jp)
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htime i hi⟩
  have hsum := Submission.Obl.k4_scalar_angular_pair_agreement.sum_le_card_image_mul
    ν S j A Ap hA hdisj hsub
  have hbound : (S.card : ENNReal) * ENNReal.ofReal θ ≤
      ((2 ^ (T - Tp) : ℕ) : ENNReal) * ν Ap := by
    calc
      _ = ∑ _i ∈ S, ENNReal.ofReal θ := by simp
      _ ≤ ∑ i ∈ S, ν (A i) := Finset.sum_le_sum hfloor
      _ ≤ ((S.image j).card : ENNReal) * ν Ap := hsum
      _ ≤ _ := by
        gcongr
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (measure_ne_top ν Ap)) hbound
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hθ.le, Nat.cast_pow, Nat.cast_ofNat,
    ← measureReal_def] at hreal
  exact (le_div_iff₀ hθ).mpr hreal

/-- The critical trajectory floor has three spatial powers. Summing its
nested time blocks gives the fourth power, with the original parent prior. -/
theorem critical_descendant_count {α ι : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] (S : Finset ι)
    {T Tp : ℕ} (hT : Tp ≤ T) (jp : Fin (2 ^ Tp))
    (j : ι → Fin (2 ^ T)) (A : ι → Set α) (Ap : Set α)
    (hA : ∀ i ∈ S, MeasurableSet (A i))
    (hdisj : ∀ i ∈ S, ∀ i' ∈ S, i ≠ i' → j i = j i' → Disjoint (A i) (A i'))
    (hsub : ∀ i ∈ S, A i ⊆ Ap)
    (htime : ∀ i ∈ S,
      Submission.Obl.k4_scalar_linear_critical_extremizers.Split.I T (j i) ⊆
        Submission.Obl.k4_scalar_linear_critical_extremizers.Split.I Tp jp)
    (a ap d K : ℝ) (ha : 0 < a) (hap : 0 < ap) (hK : 0 < K)
    (hparent : ν.real Ap ≤ K * ((2 : ℝ) ^ Tp)⁻¹ ^ 3 * ap ^ d)
    (hfloor : ∀ i ∈ S,
      ENNReal.ofReal (((2 : ℝ) ^ T)⁻¹ ^ 3 * a ^ d / K) ≤ ν (A i)) :
    (S.card : ℝ) ≤ K ^ 2 *
      (((2 : ℝ) ^ T / (2 : ℝ) ^ Tp) ^ 4) * (ap / a) ^ d := by
  have haD : 0 < a ^ d := Real.rpow_pos_of_pos ha _
  have hapD : 0 < ap ^ d := Real.rpow_pos_of_pos hap _
  have hθ : 0 < ((2 : ℝ) ^ T)⁻¹ ^ 3 * a ^ d / K := by positivity
  have hcount := descendant_assignment_count ν S hT jp j A Ap
    hA hdisj hsub htime _ hθ hfloor
  have hscale := Submission.Obl.k4_scalar_angular_pair_agreement.two_pow_split hT
  have hratio : (2 : ℝ) ^ (T - Tp) = (2 : ℝ) ^ T / (2 : ℝ) ^ Tp := by
    apply (eq_div_iff (by positivity)).mpr
    nlinarith only [hscale]
  calc
    (S.card : ℝ) ≤ (2 : ℝ) ^ (T - Tp) * ν.real Ap /
        (((2 : ℝ) ^ T)⁻¹ ^ 3 * a ^ d / K) := hcount
    _ ≤ (2 : ℝ) ^ (T - Tp) *
        (K * ((2 : ℝ) ^ Tp)⁻¹ ^ 3 * ap ^ d) /
        (((2 : ℝ) ^ T)⁻¹ ^ 3 * a ^ d / K) := by gcongr
    _ = K ^ 2 * (((2 : ℝ) ^ T / (2 : ℝ) ^ Tp) ^ 4) * (ap / a) ^ d := by
      rw [hratio, Real.div_rpow hap.le ha.le]
      field_simp

end

end Submission.Obl.k4_critical_switching_state_preparation
