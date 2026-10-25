/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarBlockSearch.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarBlockSearch.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarBlockMass
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarBlockGroup
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarBlockGraph
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarAnchorOverlap

/-! Choose the actual original anchor and normalized starting-bin search law. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

namespace ScalarNormalHyp

theorem exists_original_block_search {Λ : Type*} [MeasurableSpace Λ]
    {D : ScalarMotion Λ} {ν : Measure Λ} [IsProbabilityMeasure ν] {E : Set (Λ × ℝ)}
    {F : ℝ → ℝ} {S : ℝ → Set ℝ} {K ζ d H s : ℝ}
    (h : ScalarNormalHyp D ν E F S K ζ d) (hK : 1 ≤ K) (hζ : 0 < ζ) (hd : d ≤ 1)
    (hH : 0 < H) (hH1 : H ≤ 1) (hζH : ζ ≤ H)
    (hblock : E ⊆ univ ×ˢ Icc s (s + H)) (hmass : H / K ≤ (ν.prod volume).real E) :
    ∃ (anchor : ℝ) (bin : ℤ), anchor ∈ Icc (0 : ℝ) 1 ∧
      s + H * anchor ∈ scalarNormalTimes E ∧
      let c := s + H * anchor
      let νb := scalarGroupPrior (ν.restrict ((fun l => (l, c)) ⁻¹' E))
        (fun l => ⌊D.scalar F l c / H⌋) bin (H ^ d)
      νb.real univ ≤ 10000 * K ^ 4 ∧
      (K⁻¹) ^ 2 / (10000 * K ^ 4) ≤
        ((scalarIntervalTime (-anchor)).prod νb).real
          (scalarCenteredEvent E (scalarStartingLabels D E F c H bin) c H) := by
  let μ := scalarUnitTime
  letI : IsProbabilityMeasure μ := scalarUnitTime_probability
  let E₀ := scalarCenteredEvent E univ s H
  have hE₀ : MeasurableSet E₀ := scalarCenteredEvent_measurable h.event_measurable MeasurableSet.univ s H
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hmass₀ : K⁻¹ ≤ (μ.prod ν).real E₀ := by
    have hm : (μ.prod ν).real E₀ = (ν.prod volume).real E / H := by
      simpa only [μ, E₀, mul_zero, add_zero, neg_zero, scalarIntervalTime,
        scalarUnitTime, zero_add, univ_prod_univ, inter_univ] using
        original_centered_event_real ν h.event_measurable MeasurableSet.univ s 0 hH hblock
    rw [hm]
    apply (le_div_iff₀ hH).mpr
    simpa only [div_eq_mul_inv, mul_comm] using hmass
  have hnull : μ (Icc (0 : ℝ) 1)ᶜ = 0 := by simp [μ, scalarUnitTime]
  obtain ⟨anchor, hanchor, hoverlap⟩ := exists_original_anchor_event μ ν hE₀ hnull
  have ha : anchor ∈ Icc (0 : ℝ) 1 := by
    simpa only [mem_compl_iff, not_not] using hanchor
  let c := s + H * anchor
  let A₀ : Set Λ := (fun l => (l, c)) ⁻¹' E
  let P := E₀ ∩ (univ ×ˢ A₀)
  have hA₀ : MeasurableSet A₀ := measurable_prodMk_right h.event_measurable
  have hP : MeasurableSet P := hE₀.inter (MeasurableSet.univ.prod hA₀)
  have hsection : Prod.mk anchor ⁻¹' E₀ = A₀ := by
    ext l
    simp [E₀, A₀, c, scalarCenteredEvent, scalarCenteredLift]
  have hδ : 0 < (K⁻¹) ^ 2 := sq_pos_of_pos (inv_pos.mpr hKpos)
  have hPmass : (K⁻¹) ^ 2 ≤ (μ.prod ν).real P := by
    rw [hsection, show ν.real univ = 1 from by simp [Measure.real]] at hoverlap
    have hsq : (K⁻¹) ^ 2 ≤ ((μ.prod ν).real E₀) ^ 2 :=
      (sq_le_sq₀ (inv_nonneg.mpr hKpos.le) measureReal_nonneg).mpr hmass₀
    simpa only [one_mul] using hsq.trans hoverlap
  have hPne : P.Nonempty := by
    by_contra hne
    have he : P = ∅ := not_nonempty_iff_eq_empty.mp hne
    rw [he, measureReal_empty] at hPmass
    exact (not_le_of_gt hδ) hPmass
  have hc : c ∈ scalarNormalTimes E := by
    obtain ⟨p, hp⟩ := hPne
    exact ⟨p.2, hp.2.2⟩
  obtain ⟨bin, hprior, hselected⟩ := h.exists_original_starting_bin_group hK hζ hd hH hH1 hζH
    μ hP (fun p hp => hp.2) hδ hPmass
  let νb := scalarGroupPrior (ν.restrict A₀) (fun l => ⌊D.scalar F l c / H⌋) bin (H ^ d)
  letI : IsFiniteMeasure νb := scalarGroupPrior_finite _ _ _ _
  have hselected_set : P ∩ (univ ×ˢ {l | ⌊D.scalar F l c / H⌋ = bin}) =
      scalarCenteredEvent E (scalarStartingLabels D E F c H bin) s H := by
    ext p
    simp only [P, E₀, A₀, scalarCenteredEvent, scalarStartingLabels,
      mem_inter_iff, mem_preimage, mem_prod, mem_univ, mem_setOf_eq, true_and, and_true]
    tauto
  rw [hselected_set] at hselected
  refine ⟨anchor, bin, ha, hc, hprior, ?_⟩
  rw [original_recentered_event_real νb h.event_measurable
    (scalarStartingLabels_measurable D h.event_measurable F c H bin) s anchor hH hblock]
  exact hselected

end ScalarNormalHyp

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
