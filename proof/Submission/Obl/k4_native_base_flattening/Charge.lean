import Mathlib
import Submission.Obl.k4_native_base_flattening.Observation

/-!
# Charging the factor-two and cutoff exceptions in extended reals

On the event where a density `G` is off from an approximant `Ĝ` by more than a factor two, or
where `Ĝ` falls below a cutoff `ε`, the density is at most `2 |G - Ĝ| + ε 1[Ĝ ≠ 0]`. The mass of
the event is therefore at most twice the `L¹` distance plus `ε` times the reference measure of the
support of `Ĝ`. No finiteness of `G` is needed.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_native_base_flattening

lemma bad_pointwise_le {G A ε : ℝ≥0∞}
    (h : G < 2⁻¹ * A ∨ 2 * A < G ∨ A < ε) :
    G ≤ 2 * ediff G A + ε * {x : ℝ≥0∞ | x ≠ 0}.indicator 1 A := by
  have hle : ediff G A ≤ 2 * ediff G A := by
    rw [two_mul]; exact le_add_self
  rcases h with hlow | hhigh | hcut
  · -- `2 G < A`, so `G ≤ A - G`.
    have h2 : G + G < A := by
      calc G + G < 2⁻¹ * A + 2⁻¹ * A := ENNReal.add_lt_add hlow hlow
        _ = A := by rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
    have hGt : G ≠ ∞ := by
      intro hG; rw [hG, top_add] at h2; exact not_top_lt h2
    have h3 : G ≤ A - G := ENNReal.le_sub_of_add_le_left hGt h2.le
    calc G ≤ A - G := h3
      _ ≤ ediff G A := le_add_self
      _ ≤ 2 * ediff G A := hle
      _ ≤ _ := le_self_add
  · -- `2 A < G`, so `A ≤ G - A` and `G = (G - A) + A ≤ 2 (G - A)`.
    have h2 : A + A < G := by rwa [← two_mul]
    have hAt : A ≠ ∞ := by
      intro hA; rw [hA, top_add] at h2; exact not_top_lt h2
    have h3 : A ≤ G - A := ENNReal.le_sub_of_add_le_left hAt h2.le
    have hAG : A ≤ G := le_trans le_self_add h2.le
    calc G = (G - A) + A := (tsub_add_cancel_of_le hAG).symm
      _ ≤ (G - A) + (G - A) := add_le_add le_rfl h3
      _ = 2 * (G - A) := (two_mul _).symm
      _ ≤ 2 * ediff G A := by gcongr; exact le_self_add
      _ ≤ _ := le_self_add
  · -- `A < ε`: `G ≤ A + (G - A)` with `A ≤ ε 1[A ≠ 0]`.
    have hA : A ≤ ε * {x : ℝ≥0∞ | x ≠ 0}.indicator 1 A := by
      by_cases hA0 : A = 0
      · simp [hA0]
      · have hmem : A ∈ {x : ℝ≥0∞ | x ≠ 0} := hA0
        rw [indicator_of_mem hmem, Pi.one_apply, mul_one]
        exact hcut.le
    calc G ≤ A + (G - A) := le_add_tsub
      _ ≤ ε * {x : ℝ≥0∞ | x ≠ 0}.indicator 1 A + 2 * ediff G A :=
          add_le_add hA (le_trans le_self_add hle)
      _ = _ := add_comm _ _

/-- Mass of the factor-two and cutoff exceptions of a density against an approximant. -/
theorem bad_lintegral_le {Y : Type*} [MeasurableSpace Y] (ρ : Measure Y)
    {G A : Y → ℝ≥0∞} (hG : Measurable G) (hA : Measurable A) (ε : ℝ≥0∞) :
    ∫⁻ y in {y | G y < 2⁻¹ * A y ∨ 2 * A y < G y ∨ A y < ε}, G y ∂ρ ≤
      2 * ∫⁻ y, ediff (G y) (A y) ∂ρ + ε * ρ {y | A y ≠ 0} := by
  have hbad : MeasurableSet {y | G y < 2⁻¹ * A y ∨ 2 * A y < G y ∨ A y < ε} :=
    (measurableSet_lt hG (measurable_const.mul hA)).union
      ((measurableSet_lt (measurable_const.mul hA) hG).union
        (measurableSet_lt hA measurable_const))
  have hsupp : MeasurableSet {y | A y ≠ 0} :=
    (hA (measurableSet_singleton 0)).compl
  rw [← lintegral_indicator hbad]
  calc
    _ ≤ ∫⁻ y, 2 * ediff (G y) (A y) + ε * {y | A y ≠ 0}.indicator 1 y ∂ρ := by
      refine lintegral_mono fun y => ?_
      by_cases hy : y ∈ {y | G y < 2⁻¹ * A y ∨ 2 * A y < G y ∨ A y < ε}
      · rw [indicator_of_mem hy]
        have h := bad_pointwise_le hy
        have hind : {x : ℝ≥0∞ | x ≠ 0}.indicator 1 (A y) =
            {y | A y ≠ 0}.indicator (1 : Y → ℝ≥0∞) y := by
          by_cases h0 : A y = 0
          · have h1 : A y ∉ {x : ℝ≥0∞ | x ≠ 0} := fun h' => h' h0
            have h2 : y ∉ {y | A y ≠ 0} := fun h' => h' h0
            rw [indicator_of_notMem h1, indicator_of_notMem h2]
          · have h1 : A y ∈ {x : ℝ≥0∞ | x ≠ 0} := h0
            have h2 : y ∈ {y | A y ≠ 0} := h0
            rw [indicator_of_mem h1, indicator_of_mem h2]
            rfl
        rwa [hind] at h
      · rw [indicator_of_notMem hy]
        exact zero_le
    _ = 2 * ∫⁻ y, ediff (G y) (A y) ∂ρ + ε * ρ {y | A y ≠ 0} := by
      rw [lintegral_add_left ((measurable_ediff hG hA).const_mul 2),
        lintegral_const_mul _ (measurable_ediff hG hA),
        lintegral_const_mul _ (measurable_one.indicator hsupp), lintegral_indicator_one hsupp]

end Submission.Obl.k4_native_base_flattening
