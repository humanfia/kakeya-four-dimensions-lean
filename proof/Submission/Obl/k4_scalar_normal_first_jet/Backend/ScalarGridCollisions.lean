/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarGridCollisions.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarGridCollisions.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCellMass
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCollisions
import Mathlib.MeasureTheory.Integral.Prod

/-! Scalar collision lower bounds for infinite grid-code types. Only the
occupied list at each time is finite; the scalar grid itself may be `ℤ`. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open scoped BigOperators

theorem original_grid_collision_lower {Θ Λ ι : Type*}
    [MeasurableSpace Θ] [MeasurableSpace Λ] [MeasurableSpace ι] [MeasurableEq ι]
    (μ : Measure Θ) [IsProbabilityMeasure μ] (ν : Measure Λ) [IsFiniteMeasure ν]
    {E : Set (Θ × Λ)} (hE : MeasurableSet E) {Y : Θ × Λ → ι} (hY : Measurable Y)
    (K : Θ → Finset ι) (hcover : ∀ θ l, (θ, l) ∈ E → Y (θ, l) ∈ K θ)
    {B : ℝ} (hcard : ∀ θ, ((K θ).card : ℝ) ≤ B) :
    ((μ.prod ν).real E) ^ 2 ≤ B * ∫ θ,
      (ν.prod ν).real {p : Λ × Λ | (θ, p.1) ∈ E ∧ (θ, p.2) ∈ E ∧
        Y (θ, p.1) = Y (θ, p.2)} ∂μ := by
  classical
  let w : Θ → ι → ℝ := fun θ b =>
    ν.real ((Prod.mk θ ⁻¹' E) ∩ (fun l => Y (θ, l)) ⁻¹' {b})
  let Q : Θ → Set (Λ × Λ) := fun θ =>
    {p | (θ, p.1) ∈ E ∧ (θ, p.2) ∈ E ∧ Y (θ, p.1) = Y (θ, p.2)}
  have hmass θ : (∑ b ∈ K θ, w θ b) = ν.real (Prod.mk θ ⁻¹' E) :=
    sum_original_code_masses ν (measurable_prodMk_left hE)
      (hY.comp measurable_prodMk_left) (K θ) (hcover θ)
  have hpair θ : (∑ b ∈ K θ, w θ b ^ 2) = (ν.prod ν).real (Q θ) :=
    original_finite_code_pair_energy ν (measurable_prodMk_left hE)
      (hY.comp measurable_prodMk_left) (K θ) (hcover θ)
  have henergy θ :
      (∑ i ∈ K θ, ∑ j ∈ K θ, if i = j then w θ i * w θ j else 0) =
        (ν.prod ν).real (Q θ) := by
    calc
      _ = ∑ i ∈ K θ, w θ i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_ite_eq, ite_eq_left hi, pow_two]
      _ = _ := hpair θ
  let P : Set (Θ × (Λ × Λ)) := {p | p.2 ∈ Q p.1}
  have hleft : Measurable (fun p : Θ × (Λ × Λ) => (p.1, p.2.1)) :=
    measurable_fst.prodMk measurable_snd.fst
  have hright : Measurable (fun p : Θ × (Λ × Λ) => (p.1, p.2.2)) :=
    measurable_fst.prodMk measurable_snd.snd
  have hP : MeasurableSet P :=
    (hE.preimage hleft).inter ((hE.preimage hright).inter
      (measurableSet_eq_fun (hY.comp hleft) (hY.comp hright)))
  have hem₀ : Measurable (fun θ => (ν.prod ν).real (Q θ)) :=
    (measurable_measure_prodMk_left hP).ennreal_toReal
  have hem : Measurable (fun θ =>
      ∑ i ∈ K θ, ∑ j ∈ K θ, if i = j then w θ i * w θ j else 0) := by
    simpa only [henergy] using hem₀
  have hmm : Measurable (fun θ => ∑ b ∈ K θ, w θ b) := by
    simpa only [hmass, Measure.real] using (measurable_measure_prodMk_left hE).ennreal_toReal
  have h := integral_collision_lower_variable_support (B := B) μ K w (fun _ b => b) hmm
    (fun _ _ _ => measureReal_nonneg)
    (fun θ => by rw [hmass]; exact measureReal_mono (subset_univ _))
    (fun θ => by
      change ((Finset.image id (K θ)).card : ℝ) ≤ B
      simpa only [Finset.image_id] using hcard θ) hem
  simp only [hmass, henergy] at h
  have hmean : (∫ θ, ν.real (Prod.mk θ ⁻¹' E) ∂μ) = (μ.prod ν).real E := by
    unfold Measure.real
    rw [integral_toReal (measurable_measure_prodMk_left hE).aemeasurable
      (Filter.Eventually.of_forall fun θ => measure_lt_top ν _), Measure.prod_apply hE]
  rw [hmean] at h
  exact h

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
