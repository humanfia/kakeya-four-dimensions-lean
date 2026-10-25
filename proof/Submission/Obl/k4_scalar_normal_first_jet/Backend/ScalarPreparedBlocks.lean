/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarPreparedBlocks.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarPreparedBlocks.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarBlockPreparation
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarTimeGrid
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarTimeRecovery
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarBlockTime

/-! Prepare simultaneous original time and block floors before local searches. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

theorem prepare_original_scalar_blocks {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsProbabilityMeasure ν] {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) {δ τ : ℝ} (hτ : 0 < τ) (hbudget : 4 * τ ≤ δ)
    (hmass : δ ≤ (ν.prod volume).real E) {J : ℕ} (hJ : 0 < J) :
    ∃ (S : Set ℝ) (K : Finset (Fin J)), MeasurableSet S ∧ S ⊆ Ico (0 : ℝ) 1 ∧
      δ / 2 ≤ (ν.prod volume).real (E ∩ (univ ×ˢ S)) ∧
      (∀ t ∈ S, ENNReal.ofReal τ ≤ ν {l | (l, t) ∈ E ∩ (univ ×ˢ S)}) ∧
      (∀ j ∈ K, ENNReal.ofReal (τ / (J : ℝ)) ≤
        (ν.prod volume) ((E ∩ (univ ×ˢ S)) ∩ (univ ×ˢ timeCell J j))) ∧
      δ / 2 ≤ (K.card : ℝ) / (J : ℝ) := by
  letI : IsProbabilityMeasure scalarUnitTime := scalarUnitTime_probability
  let μ := ν.prod scalarUnitTime
  let Eclip := E ∩ (univ ×ˢ Ico (0 : ℝ) 1)
  have hclipm : MeasurableSet Eclip := hE.inter (MeasurableSet.univ.prod measurableSet_Ico)
  have hclipunit : Eclip ⊆ univ ×ˢ Icc (0 : ℝ) 1 :=
    fun p hp => ⟨mem_univ _, hp.2.2.1, hp.2.2.2.le⟩
  have hclipmass : (ν.prod volume) Eclip = (ν.prod volume) E := by
    simpa only [timeCell, Fin.sum_univ_one, Fin.val_zero, Nat.cast_zero, Nat.cast_one,
      zero_div, zero_add, div_one] using
      (Submission.Obl.k4_horizon_chart_assembly.sum_block_incidence ν E hE hunit (J := 1) (by norm_num))
  obtain ⟨S₀, hS₀m, hS₀unit, hfloor₀, hloss₀⟩ := prepare_time_floor ν hclipm hclipunit τ
  have hS₀open : S₀ ⊆ Ico (0 : ℝ) 1 := by
    intro t ht
    have hpos : 0 < ν {l | (l, t) ∈ Eclip} := (ENNReal.ofReal_pos.mpr hτ).trans_le (hfloor₀ t ht)
    obtain ⟨l, hl⟩ := nonempty_of_measure_ne_zero (ne_of_gt hpos)
    exact hl.2.2
  let E₀ := Eclip ∩ (univ ×ˢ S₀)
  have hE₀m : MeasurableSet E₀ := hclipm.inter (MeasurableSet.univ.prod hS₀m)
  have hE₀unit : E₀ ⊆ univ ×ˢ Ico (0 : ℝ) 1 := fun p hp => hp.1.2
  have hE₀closed : E₀ ⊆ univ ×ˢ Icc (0 : ℝ) 1 :=
    fun p hp => ⟨mem_univ _, (hE₀unit hp).2.1, (hE₀unit hp).2.2.le⟩
  have hfinite₀ := original_unit_incidence_ne_top ν hE₀m hE₀closed
  have hlossreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hfinite₀, ENNReal.ofReal_ne_top⟩) hloss₀
  rw [ENNReal.toReal_add hfinite₀ ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hτ.le,
    hclipmass] at hlossreal
  change (ν.prod volume).real E ≤ (ν.prod volume).real E₀ + τ at hlossreal
  have hμ₀ : μ.real E₀ = (ν.prod volume).real E₀ := original_unit_time_prod_real ν hE₀m hE₀closed
  have hmass₀ : δ - τ ≤ μ.real E₀ := by rw [hμ₀]; linarith
  have hJpos : (0 : ℝ) < J := Nat.cast_pos.mpr hJ
  have hpartition : (Fintype.card (Fin J) : ℝ) * (1 / (J : ℝ)) ≤ 1 := by
    simp only [Fintype.card_fin]
    field_simp
    norm_num
  obtain ⟨K, U, hUeq, hUm, hloss, hblock, hcount⟩ := prepare_original_time_blocks μ hE₀m
    (scalarTimeBlockCode J hJ) (scalarTimeBlockCode_measurable J hJ)
    (by positivity : (0 : ℝ) ≤ 1 / (J : ℝ)) hτ.le hpartition
    (original_time_grid_cell_cap ν hE₀unit hJ)
  let S := S₀ ∩ U
  let R := E ∩ (univ ×ˢ S)
  have hSm : MeasurableSet S := hS₀m.inter hUm
  have hSunit : S ⊆ Ico (0 : ℝ) 1 := fun t ht => hS₀open ht.1
  have hRm : MeasurableSet R := hE.inter (MeasurableSet.univ.prod hSm)
  have hRunit : R ⊆ univ ×ˢ Icc (0 : ℝ) 1 := fun p hp => hunit hp.1
  have hReq : E₀ ∩ (univ ×ˢ U) = R := by
    ext p
    constructor
    · exact fun hp => ⟨hp.1.1.1, mem_univ _, hp.1.2.2, hp.2.2⟩
    · intro hp
      exact ⟨⟨⟨hp.1, mem_univ _, hSunit hp.2.2⟩, mem_univ _, hp.2.2.1⟩, mem_univ _, hp.2.2.2⟩
  rw [hReq] at hloss hblock hcount
  have hμR : μ.real R = (ν.prod volume).real R := original_unit_time_prod_real ν hRm hRunit
  have hRmass : δ / 2 ≤ (ν.prod volume).real R := by rw [← hμR]; linarith
  refine ⟨S, K, hSm, hSunit, hRmass, ?_, ?_, ?_⟩
  · intro t ht
    have hsection : {l | (l, t) ∈ R} = {l | (l, t) ∈ Eclip} := by
      ext l
      simp only [R, Eclip, mem_inter_iff, mem_prod, mem_univ, true_and, ht, hSunit ht,
        and_true, mem_setOf_eq]
    change ENNReal.ofReal τ ≤ ν {l | (l, t) ∈ R}
    rw [hsection]
    exact hfloor₀ t ht.1
  · intro j hj
    have hcell : R ∩ (fun p => scalarTimeBlockCode J hJ p.2) ⁻¹' {j} =
        R ∩ (univ ×ˢ timeCell J j) := by
      ext p
      constructor
      · exact fun hp => ⟨hp.1, mem_univ _, (scalarTimeBlockCode_eq_iff hJ j (hSunit hp.1.2.2)).mp hp.2⟩
      · exact fun hp => ⟨hp.1, (scalarTimeBlockCode_eq_iff hJ j (hSunit hp.1.2.2)).mpr hp.2.2⟩
    have hr := hblock j hj
    rw [hcell, original_unit_time_prod_real ν (hRm.inter (MeasurableSet.univ.prod (measurableSet_timeCell J j)))
      (fun p hp => hRunit hp.1)] at hr
    have hfinite := original_unit_incidence_ne_top ν
      (hRm.inter (MeasurableSet.univ.prod (measurableSet_timeCell J j))) (fun p hp => hRunit hp.1)
    change ENNReal.ofReal (τ / (J : ℝ)) ≤ (ν.prod volume) (R ∩ (univ ×ˢ timeCell J j))
    calc
      _ ≤ ENNReal.ofReal ((ν.prod volume).real (R ∩ (univ ×ˢ timeCell J j))) :=
        ENNReal.ofReal_le_ofReal (by simpa only [mul_one_div] using hr)
      _ = _ := ENNReal.ofReal_toReal hfinite
  · calc
      _ ≤ (ν.prod volume).real R := hRmass
      _ = μ.real R := hμR.symm
      _ ≤ (K.card : ℝ) * (1 / (J : ℝ)) := hcount
      _ = _ := by ring

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
