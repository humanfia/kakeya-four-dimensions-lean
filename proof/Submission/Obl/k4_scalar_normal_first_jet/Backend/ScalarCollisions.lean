/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarCollisions.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarCollisions.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Lib.K4WeightedCellEnergy

/-! Lower bounds for scalar collisions with the original trajectory and time
weights. The label weights may vary in time; no success normalization occurs. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory
open scoped BigOperators

/-- A scalar support using at most `B` cells has original same-cell collision
mass at least its squared mass divided by `B`. -/
theorem weighted_cell_collision_lower {ι β : Type*} [DecidableEq ι] [DecidableEq β]
    (S : Finset ι) (code : ι → β) (w : ι → ℝ) {B : ℝ}
    (hcard : ((S.image code).card : ℝ) ≤ B) :
    (∑ i ∈ S, w i) ^ 2 ≤
      B * (∑ i ∈ S, ∑ j ∈ S, if code i = code j then w i * w j else 0) := by
  classical
  let m : β → ℝ := fun b => ∑ i ∈ S with code i = b, w i
  have hsum : (∑ i ∈ S, w i) = ∑ b ∈ S.image code, m b :=
    (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem code hi) _).symm
  rw [Submission.Lib.K4WeightedCellEnergy.weighted_cell_energy_eq, hsum]
  exact (sq_sum_le_card_mul_sum_sq (s := S.image code) (f := m)).trans
    (mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg fun _ _ => sq_nonneg _))

/-- The scalar collision lower bound survives averaging in time under the
unchanged time weights. The prior label weights are allowed to depend on time. -/
theorem time_averaged_collision_lower {ι κ β : Type*}
    [DecidableEq ι] [DecidableEq κ] [DecidableEq β]
    (S : Finset ι) (T : Finset κ) (a : κ → ℝ) (w : κ → ι → ℝ)
    (code : κ → ι → β) {B : ℝ}
    (ha : ∀ t ∈ T, 0 ≤ a t) (ha₁ : ∑ t ∈ T, a t ≤ 1)
    (hcard : ∀ t ∈ T, ((S.image (code t)).card : ℝ) ≤ B) :
    (∑ t ∈ T, a t * ∑ i ∈ S, w t i) ^ 2 ≤
      B * (∑ t ∈ T, a t *
        (∑ i ∈ S, ∑ j ∈ S, if code t i = code t j then w t i * w t j else 0)) := by
  let m : κ → ℝ := fun t => ∑ i ∈ S, w t i
  have hcs : (∑ t ∈ T, a t * m t) ^ 2 ≤
      (∑ t ∈ T, a t) * ∑ t ∈ T, a t * (m t) ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul T ha
      (fun t ht => mul_nonneg (ha t ht) (sq_nonneg _))
    intro t ht
    exact (by ring : (a t * m t) ^ 2 = a t * (a t * (m t) ^ 2)).le
  have hnon : 0 ≤ ∑ t ∈ T, a t * (m t) ^ 2 :=
    Finset.sum_nonneg fun t ht => mul_nonneg (ha t ht) (sq_nonneg _)
  calc
    (∑ t ∈ T, a t * m t) ^ 2 ≤
        (∑ t ∈ T, a t) * ∑ t ∈ T, a t * (m t) ^ 2 := hcs
    _ ≤ 1 * ∑ t ∈ T, a t * (m t) ^ 2 := mul_le_mul_of_nonneg_right ha₁ hnon
    _ = ∑ t ∈ T, a t * (m t) ^ 2 := one_mul _
    _ ≤ ∑ t ∈ T, a t *
        (B * (∑ i ∈ S, ∑ j ∈ S,
          if code t i = code t j then w t i * w t j else 0)) := by
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_left
        (weighted_cell_collision_lower S (code t) (w t) (hcard t ht)) (ha t ht)
    _ = B * (∑ t ∈ T, a t *
        (∑ i ∈ S, ∑ j ∈ S,
          if code t i = code t j then w t i * w t j else 0)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      ring

/-- The same collision estimate for a continuous exact time law. The
original row mass may vanish at some times; no conditional row is normalized. -/
theorem integral_collision_lower_variable_support {Θ ι β : Type*} [MeasurableSpace Θ]
    [DecidableEq ι] [DecidableEq β] (μ : Measure Θ) [IsProbabilityMeasure μ]
    (S : Θ → Finset ι) (w : Θ → ι → ℝ) (code : Θ → ι → β) {B V : ℝ}
    (hmm : Measurable (fun θ => ∑ i ∈ S θ, w θ i))
    (hw : ∀ θ i, i ∈ S θ → 0 ≤ w θ i)
    (hsum : ∀ θ, ∑ i ∈ S θ, w θ i ≤ V)
    (hcard : ∀ θ, (((S θ).image (code θ)).card : ℝ) ≤ B)
    (he : Measurable (fun θ => ∑ i ∈ S θ, ∑ j ∈ S θ,
      if code θ i = code θ j then w θ i * w θ j else 0)) :
    (∫ θ, ∑ i ∈ S θ, w θ i ∂μ) ^ 2 ≤
      B * ∫ θ, ∑ i ∈ S θ, ∑ j ∈ S θ,
        if code θ i = code θ j then w θ i * w θ j else 0 ∂μ := by
  let m : Θ → ℝ := fun θ => ∑ i ∈ S θ, w θ i
  let e : Θ → ℝ := fun θ => ∑ i ∈ S θ, ∑ j ∈ S θ,
    if code θ i = code θ j then w θ i * w θ j else 0
  have hm : Measurable m := hmm
  have hmr θ : 0 ≤ m θ ∧ m θ ≤ V :=
    ⟨Finset.sum_nonneg (fun i hi => hw θ i hi), hsum θ⟩
  have her θ : 0 ≤ e θ ∧ e θ ≤ (m θ) ^ 2 := by
    constructor
    · exact Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => by
        split_ifs
        · exact mul_nonneg (hw θ i hi) (hw θ j hj)
        · exact le_rfl
    · calc
        e θ ≤ ∑ i ∈ S θ, ∑ j ∈ S θ, w θ i * w θ j := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          split_ifs
          · exact le_rfl
          · exact mul_nonneg (hw θ i hi) (hw θ j hj)
        _ = (m θ) ^ 2 := by simp only [m, ← Finset.mul_sum, ← Finset.sum_mul, pow_two]
  have hmi : Integrable m μ := Integrable.of_bound hm.aestronglyMeasurable V
    (Filter.Eventually.of_forall fun θ => by simpa [abs_of_nonneg (hmr θ).1] using (hmr θ).2)
  have hmsq : Integrable (fun θ => (m θ) ^ 2) μ :=
    Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable (V ^ 2) (Filter.Eventually.of_forall fun θ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [(hmr θ).1, (hmr θ).2])
  have hei : Integrable e μ := Integrable.of_bound he.aestronglyMeasurable (V ^ 2)
    (Filter.Eventually.of_forall fun θ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (her θ).1]
      nlinarith [(her θ).2, (hmr θ).1, (hmr θ).2])
  have hJ : (∫ θ, m θ ∂μ) ^ 2 ≤ ∫ θ, (m θ) ^ 2 ∂μ :=
    (convexOn_pow (𝕜 := ℝ) 2).map_integral_le (continuous_pow 2).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall fun θ => (hmr θ).1) hmi hmsq
  calc
    (∫ θ, m θ ∂μ) ^ 2 ≤ ∫ θ, (m θ) ^ 2 ∂μ := hJ
    _ ≤ ∫ θ, B * e θ ∂μ := integral_mono hmsq (hei.const_mul B)
      (fun θ => weighted_cell_collision_lower (S θ) (code θ) (w θ) (hcard θ))
    _ = B * ∫ θ, e θ ∂μ := integral_const_mul B e

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
