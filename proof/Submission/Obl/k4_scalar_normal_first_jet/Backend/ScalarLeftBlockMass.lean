/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarLeftBlockMass.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarLeftBlockMass.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarBlockTime
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarLeftBlockEvent
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGroupLeftMass

/-! Exact original mass of the left-normalized residual groups. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

theorem original_left_block_event_real {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [SFinite ν] {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    {A : Set Λ} (hA : MeasurableSet A) (s : ℝ) {H : ℝ} (hH : 0 < H)
    (hblock : E ⊆ univ ×ˢ Icc s (s + H)) :
    (ν.prod volume).real (scalarLeftBlockEvent E A s H) =
      (ν.prod volume).real (E ∩ (A ×ˢ univ)) / H := by
  let Q := scalarLeftBlockEvent E A s H
  have hQm := scalarLeftBlockEvent_measurable hE hA s H
  have hQunit : Q ⊆ univ ×ˢ Icc (0 : ℝ) 1 :=
    fun q hq => ⟨mem_univ _, (scalarLeftBlockEvent_unit hH hblock hq).2⟩
  have hswap := original_unit_time_swap_real ν hQm hQunit
  have hm := original_centered_block_real ν s 0 hH
    (hE.inter (hA.prod MeasurableSet.univ)) (fun q hq => hblock hq.1)
  have hset : {q : ℝ × Λ | (q.2, s + H * 0 + H * q.1) ∈ E ∩ (A ×ˢ univ)} =
      Prod.swap ⁻¹' Q := by
    ext q
    simp only [Q, scalarLeftBlockEvent, mem_setOf_eq, mem_inter_iff, mem_prod,
      mem_preimage, mem_univ, mul_zero, add_zero, Prod.fst_swap, Prod.snd_swap, and_true]
  rw [hset] at hm
  have hμ : scalarIntervalTime (-(0 : ℝ)) = scalarUnitTime := by
    simp only [scalarIntervalTime, scalarUnitTime, neg_zero, zero_add]
  rw [hμ, hswap] at hm
  exact hm

theorem original_left_group_event_real {Λ β : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν] (Aanchor : Set Λ) (code : Λ → β) (bin : β)
    {E : Set (Λ × ℝ)} (hE : MeasurableSet E) {A : Set Λ} (hA : MeasurableSet A)
    (hsub : A ⊆ Aanchor ∩ code ⁻¹' {bin}) (s : ℝ) {H d : ℝ} (hH : 0 < H)
    (hblock : E ⊆ univ ×ˢ Icc s (s + H)) :
    ((scalarGroupPrior (ν.restrict Aanchor) code bin (H ^ d)).prod volume).real
      (scalarLeftBlockEvent E A s H) =
      (ν.prod volume).real (E ∩ (A ×ˢ univ)) / (H * H ^ d) := by
  let νb := scalarGroupPrior (ν.restrict Aanchor) code bin (H ^ d)
  letI : IsFiniteMeasure νb := scalarGroupPrior_finite _ _ _ _
  rw [original_left_block_event_real νb hE hA s hH hblock]
  rw [original_scalar_group_left_mass volume ν Aanchor code bin (Real.rpow_pos_of_pos hH d)
    (hE.inter (hA.prod MeasurableSet.univ)) (fun q hq => ⟨hsub hq.2.1, mem_univ _⟩)]
  field_simp

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
