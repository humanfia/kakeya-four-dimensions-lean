/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarCollisionModelConstruction.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarCollisionModelConstruction.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCollisionMeasureModel
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarStartingCollisions
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarBoundedGrid

/-! Constructing the collision model from actual scalar observations. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

theorem scalar_collision_model_from_original_observations {Λ : Type*}
    [MeasurableSpace Λ] (ν : Measure Λ) {p K d C error : ℝ}
    (hp : 0 < p) (hK : 1 ≤ K)
    {A : Set Λ} {E : Set (ℝ × Λ)} (hE : MeasurableSet E)
    (hEsub : E ⊆ Icc (-1 : ℝ) 1 ×ˢ A)
    {v Z : Λ → ℝ} (hv : Measurable v) (hZ : Measurable Z)
    {F : ℝ × Λ → ℝ} (hF : Measurable F) (f G : ℝ → ℝ)
    (hf0 : f 0 = 0) (hf : ∀ u t, |f u - f t| ≤ |u - t|)
    (hG : ∀ v w, |G v - G w| ≤ K * |v - w|)
    (hbound : ∀ l ∈ A, |v l| ≤ K ∧ |G (v l)| ≤ K)
    (S₀ : Set ℝ) (hstart : ∀ l ∈ A, Z l ∈ S₀)
    (hmodel : ∀ u l, (u, l) ∈ E → |F (u, l) - (Z l + u * G (v l) + f u * v l)| ≤ error * p)
    (hjoint : ∀ a b r : ℝ, p ≤ r →
      ν.real {l | l ∈ A ∧ v l ∈ Icc a (a + r) ∧ Z l ∈ Icc b (b + r)} ≤ C * r ^ (1 + d))
    (b : ℤ) :
    ∃ D : OriginalScalarCollisionModel ν p K d C (1 + 2 * error),
      D.labels = A ∧ D.velocity = v ∧ D.startValue = Z ∧ D.row = f ∧ D.slopeGraph = G ∧
        D.scalarSupport = S₀ ∧ D.pairEvent = scalarStartingCollisionEvent E F Z p b ∧
        (D.timeGrid.card : ℝ) ≤ 2 / p + 3 ∧ (D.velocityGrid.card : ℝ) ≤ 2 * K / p + 3 := by
  classical
  obtain ⟨Kt, hKt, htime, htimeRep⟩ := bounded_original_grid (Icc (-1 : ℝ) 1) id
    (by norm_num : (0 : ℝ) ≤ 1) hp (fun u hu => abs_le.mpr hu)
  obtain ⟨J, hJ, hvel, hvelRep⟩ := bounded_original_grid A v (zero_le_one.trans hK) hp
    (fun l hl => (hbound l hl).1)
  let D : OriginalScalarCollisionModel ν p K d C (1 + 2 * error) := {
    labels := A
    velocity := v
    startValue := Z
    velocity_measurable := hv
    startValue_measurable := hZ
    row := f
    slopeGraph := G
    row_zero := hf0
    row_compare := hf
    slope_compare := hG
    coordinate_bound := hbound
    scalarSupport := S₀
    start_support := hstart
    timeGrid := Kt
    velocityGrid := J
    velocity_cover := hvel
    velocity_witness := hvelRep
    startBin := b
    pairEvent := scalarStartingCollisionEvent E F Z p b
    pair_measurable := scalarStartingCollisionEvent_measurable hE hF hZ p b
    time_cover := fun q hq => htime q.1 (hEsub hq.1.1).1
    pair_geometry := by
      intro q hq
      have h₁ : (q.1, q.2.1) ∈ E := hq.1.1
      have h₂ : (q.1, q.2.2) ∈ E := hq.1.2.1
      exact ⟨abs_le.mpr (hEsub h₁).1, (hEsub h₁).2, (hEsub h₂).2, hq.2,
        scalar_collision_of_model_error (hmodel _ _ h₁) (hmodel _ _ h₂)
          (same_mesh_cell_close hp hq.1.2.2)⟩
    joint_cap := hjoint }
  refine ⟨D, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simpa only [D, mul_one] using hKt
  · exact hJ

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
