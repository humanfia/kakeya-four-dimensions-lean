/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarLeftBlockAnchor.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarLeftBlockAnchor.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarLeftBlockMass
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarAnchorOverlap

/-! One original overlap anchor serves all starting bins of a physical block. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

theorem exists_original_left_block_anchor {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsProbabilityMeasure ν] {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    {K H s : ℝ} (hK : 0 < K) (hH : 0 < H)
    (hblock : E ⊆ univ ×ˢ Icc s (s + H)) (hmass : H / K ≤ (ν.prod volume).real E) :
    ∃ anchor : ℝ, anchor ∈ Icc (0 : ℝ) 1 ∧ (∃ l, (l, s + H * anchor) ∈ E) ∧
      (K⁻¹) ^ 2 ≤ (ν.prod scalarUnitTime).real
        (scalarLeftBlockEvent E ((fun l => (l, s + H * anchor)) ⁻¹' E) s H) := by
  letI : IsProbabilityMeasure scalarUnitTime := scalarUnitTime_probability
  let Q := scalarLeftBlockEvent E univ s H
  let P := Prod.swap ⁻¹' Q
  have hQm := scalarLeftBlockEvent_measurable hE MeasurableSet.univ s H
  have hQunit := scalarLeftBlockEvent_unit (A := (univ : Set Λ)) hH hblock
  have hPm : MeasurableSet P := hQm.preimage measurable_swap
  have hmass₀ : K⁻¹ ≤ (scalarUnitTime.prod ν).real P := by
    rw [original_unit_time_swap_real ν hQm hQunit,
      original_left_block_event_real ν hE MeasurableSet.univ s hH hblock,
      univ_prod_univ, inter_univ]
    apply (le_div_iff₀ hH).mpr
    simpa only [div_eq_mul_inv, mul_comm] using hmass
  have hnull : scalarUnitTime (Icc (0 : ℝ) 1)ᶜ = 0 := by simp [scalarUnitTime]
  obtain ⟨anchor, hanchor, hoverlap⟩ := exists_original_anchor_event scalarUnitTime ν hPm hnull
  have ha : anchor ∈ Icc (0 : ℝ) 1 := by simpa only [mem_compl_iff, not_not] using hanchor
  let A : Set Λ := (fun l => (l, s + H * anchor)) ⁻¹' E
  have hAm : MeasurableSet A := measurable_prodMk_right hE
  let R := scalarLeftBlockEvent E A s H
  have hRm := scalarLeftBlockEvent_measurable hE hAm s H
  have hRunit : R ⊆ univ ×ˢ Icc (0 : ℝ) 1 :=
    fun q hq => ⟨mem_univ _, (scalarLeftBlockEvent_unit hH hblock hq).2⟩
  have he : P ∩ (univ ×ˢ (Prod.mk anchor ⁻¹' P)) = Prod.swap ⁻¹' R := by
    ext q
    simp only [P, Q, R, A, scalarLeftBlockEvent, mem_inter_iff, mem_preimage,
      mem_prod, mem_univ, mem_setOf_eq, Prod.fst_swap, Prod.snd_swap, and_true, true_and]
  have hmassR : (K⁻¹) ^ 2 ≤ (ν.prod scalarUnitTime).real R := by
    rw [he, original_unit_time_swap_real ν hRm hRunit] at hoverlap
    rw [original_unit_time_prod_real ν hRm hRunit]
    have hsq : (K⁻¹) ^ 2 ≤ ((scalarUnitTime.prod ν).real P) ^ 2 :=
      (sq_le_sq₀ (inv_nonneg.mpr hK.le) measureReal_nonneg).mpr hmass₀
    simpa only [show ν.real univ = 1 from by simp [Measure.real], one_mul] using hsq.trans hoverlap
  have hRnonempty : R.Nonempty := by
    apply nonempty_of_measureReal_ne_zero
    exact ne_of_gt ((sq_pos_of_pos (inv_pos.mpr hK)).trans_le hmassR)
  obtain ⟨q, hq⟩ := hRnonempty
  exact ⟨anchor, ha, ⟨q.1, hq.2⟩, hmassR⟩

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
