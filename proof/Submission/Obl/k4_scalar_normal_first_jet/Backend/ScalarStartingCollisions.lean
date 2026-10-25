/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarStartingCollisions.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarStartingCollisions.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarADCollisions

/-! Selecting an original heavy starting scalar bin in the collision event. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

noncomputable def scalarCollisionEvent {Θ Λ : Type*} (E : Set (Θ × Λ))
    (F : Θ × Λ → ℝ) (p : ℝ) : Set (Θ × (Λ × Λ)) :=
  {q | (q.1, q.2.1) ∈ E ∧ (q.1, q.2.2) ∈ E ∧
    (⌊F (q.1, q.2.1) / p⌋ : ℤ) = ⌊F (q.1, q.2.2) / p⌋}

noncomputable def scalarStartingCollisionEvent {Θ Λ : Type*} (E : Set (Θ × Λ))
    (F : Θ × Λ → ℝ) (Z : Λ → ℝ) (p : ℝ) (b : ℤ) : Set (Θ × (Λ × Λ)) :=
  scalarCollisionEvent E F p ∩ {q | (⌊Z q.2.1 / p⌋ : ℤ) = b}

theorem scalarCollisionEvent_measurable {Θ Λ : Type*} [MeasurableSpace Θ] [MeasurableSpace Λ]
    {E : Set (Θ × Λ)} (hE : MeasurableSet E) {F : Θ × Λ → ℝ} (hF : Measurable F) (p : ℝ) :
    MeasurableSet (scalarCollisionEvent E F p) := by
  have hleft : Measurable (fun q : Θ × (Λ × Λ) => (q.1, q.2.1)) :=
    measurable_fst.prodMk measurable_snd.fst
  have hright : Measurable (fun q : Θ × (Λ × Λ) => (q.1, q.2.2)) :=
    measurable_fst.prodMk measurable_snd.snd
  exact (hE.preimage hleft).inter ((hE.preimage hright).inter
    (measurableSet_eq_fun (Int.measurable_floor.comp ((hF.comp hleft).div_const p))
      (Int.measurable_floor.comp ((hF.comp hright).div_const p))))

theorem scalarStartingCollisionEvent_measurable {Θ Λ : Type*}
    [MeasurableSpace Θ] [MeasurableSpace Λ]
    {E : Set (Θ × Λ)} (hE : MeasurableSet E) {F : Θ × Λ → ℝ} (hF : Measurable F)
    {Z : Λ → ℝ} (hZ : Measurable Z) (p : ℝ) (b : ℤ) :
    MeasurableSet (scalarStartingCollisionEvent E F Z p b) :=
  (scalarCollisionEvent_measurable hE hF p).inter (measurableSet_eq_fun
    (Int.measurable_floor.comp ((hZ.comp measurable_snd.fst).div_const p)) measurable_const)

theorem original_heavy_starting_collision {Θ Λ : Type*}
    [MeasurableSpace Θ] [MeasurableSpace Λ]
    (μ : Measure Θ) [IsProbabilityMeasure μ] (ν : Measure Λ) [IsFiniteMeasure ν]
    {E : Set (Θ × Λ)} (hE : MeasurableSet E) {F : Θ × Λ → ℝ} (hF : Measurable F)
    {Z : Λ → ℝ} (hZ : Measurable Z)
    {p d C R left C₀ R₀ left₀ δ : ℝ} (hp : 0 < p) (hpR : p ≤ R) (hpR₀ : p ≤ R₀)
    (hC : 0 < C) (hC₀ : 0 < C₀) (hδ : 0 < δ) (hmass : δ ≤ (μ.prod ν).real E)
    (S : Θ → Set ℝ) (S₀ : Set ℝ) (hS : ∀ t, IntervalAD p d C (S t))
    (hS₀ : IntervalAD p d C₀ S₀)
    (hsupport : ∀ t l, (t, l) ∈ E → F (t, l) ∈ S t ∩ Icc left (left + R))
    (hstart : ∀ t l, (t, l) ∈ E → Z l ∈ S₀ ∩ Icc left₀ (left₀ + R₀)) :
    ∃ b : ℤ, MeasurableSet (scalarStartingCollisionEvent E F Z p b) ∧
      (δ ^ 2 / (3 * (C * (R / p) ^ d))) / (3 * (C₀ * (R₀ / p) ^ d)) ≤
        (μ.prod (ν.prod ν)).real (scalarStartingCollisionEvent E F Z p b) := by
  classical
  let P := scalarCollisionEvent E F p
  have hP : MeasurableSet P := scalarCollisionEvent_measurable hE hF p
  let B := 3 * (C * (R / p) ^ d)
  let B₀ := 3 * (C₀ * (R₀ / p) ^ d)
  have hR : 0 < R := hp.trans_le hpR
  have hR₀ : 0 < R₀ := hp.trans_le hpR₀
  have hB : 0 < B := by dsimp [B]; positivity
  have hB₀ : 0 < B₀ := by dsimp [B₀]; positivity
  have hmean : (∫ t, (ν.prod ν).real (Prod.mk t ⁻¹' P) ∂μ) = (μ.prod (ν.prod ν)).real P := by
    unfold Measure.real
    rw [integral_toReal (measurable_measure_prodMk_left hP).aemeasurable
      (Filter.Eventually.of_forall fun t => measure_lt_top (ν.prod ν) _), Measure.prod_apply hP]
  have hlower := original_intervalAD_collision_lower μ ν hE hF hp hpR S hS hsupport
  change ((μ.prod ν).real E) ^ 2 ≤ B * (∫ t, (ν.prod ν).real (Prod.mk t ⁻¹' P) ∂μ) at hlower
  rw [hmean] at hlower
  have hδsq : δ ^ 2 ≤ ((μ.prod ν).real E) ^ 2 :=
    (sq_le_sq₀ hδ.le measureReal_nonneg).mpr hmass
  have hPmass : δ ^ 2 / B ≤ (μ.prod (ν.prod ν)).real P :=
    (div_le_iff₀ hB).mpr (by simpa only [mul_comm] using hδsq.trans hlower)
  obtain ⟨K₀, hcard, hcover⟩ := intervalAD_grid_list (a := left₀) hp hpR₀ hS₀
  let code : Θ × (Λ × Λ) → ℤ := fun q => ⌊Z q.2.1 / p⌋
  have hcodes : ∀ q ∈ P, code q ∈ K₀ := by
    intro q hq
    exact hcover _ (hstart q.1 q.2.1 hq.1)
  obtain ⟨b, hb, hheavy⟩ := exists_heavy_original_cell (μ.prod (ν.prod ν)) P code K₀
    (Filter.Eventually.of_forall hcodes) (div_pos (sq_pos_of_pos hδ) hB) hPmass hcard
  exact ⟨b, scalarStartingCollisionEvent_measurable hE hF hZ p b, hheavy⟩

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
