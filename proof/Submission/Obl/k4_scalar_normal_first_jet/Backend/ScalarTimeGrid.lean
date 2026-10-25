/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarTimeGrid.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarTimeGrid.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarUnitTime
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.TimeCells
import Mathlib.MeasureTheory.Function.Floor

/-! The actual finite equal-time code and its original-prior cell ceiling. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

noncomputable def scalarTimeBlockCode (J : ℕ) (hJ : 0 < J) (t : ℝ) : Fin J :=
  ⟨⌊t * (J : ℝ)⌋₊ % J, Nat.mod_lt _ hJ⟩

theorem scalarTimeBlockCode_measurable (J : ℕ) (hJ : 0 < J) :
    Measurable (scalarTimeBlockCode J hJ) := by
  have hpost : Measurable (fun n : ℕ => (⟨n % J, Nat.mod_lt n hJ⟩ : Fin J)) :=
    Measurable.of_discrete
  exact hpost.comp (measurable_id.mul_const (J : ℝ)).nat_floor

theorem scalarTimeBlockCode_on_cell {J : ℕ} (hJ : 0 < J) (j : Fin J) {t : ℝ}
    (ht : t ∈ timeCell J j) : scalarTimeBlockCode J hJ t = j := by
  have hJpos : (0 : ℝ) < J := Nat.cast_pos.mpr hJ
  have ht0 : 0 ≤ t := (timeCell_subset hJ j ht).1
  have hf : ⌊t * (J : ℝ)⌋₊ = j.val := by
    apply (Nat.floor_eq_iff (mul_nonneg ht0 hJpos.le)).mpr
    exact ⟨(div_le_iff₀ hJpos).mp ht.1, (lt_div_iff₀ hJpos).mp ht.2⟩
  apply Fin.ext
  change ⌊t * (J : ℝ)⌋₊ % J = j.val
  rw [hf, Nat.mod_eq_of_lt j.isLt]

theorem scalarTimeBlockCode_eq_iff {J : ℕ} (hJ : 0 < J) (j : Fin J) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) : scalarTimeBlockCode J hJ t = j ↔ t ∈ timeCell J j := by
  constructor
  · intro he
    obtain ⟨j', hj'⟩ := mem_iUnion.mp (show t ∈ ⋃ i : Fin J, timeCell J i by
      rw [iUnion_timeCell hJ]; exact ht)
    have hj'eq : j' = j := (scalarTimeBlockCode_on_cell hJ j' hj').symm.trans he
    simpa only [hj'eq] using hj'
  · exact scalarTimeBlockCode_on_cell hJ j

theorem original_time_grid_cell_cap {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsProbabilityMeasure ν] {E : Set (Λ × ℝ)}
    (hunit : E ⊆ univ ×ˢ Ico (0 : ℝ) 1) {J : ℕ} (hJ : 0 < J) (j : Fin J) :
    (ν.prod scalarUnitTime).real (E ∩ (fun p => scalarTimeBlockCode J hJ p.2) ⁻¹' {j}) ≤
      1 / (J : ℝ) := by
  letI : IsProbabilityMeasure scalarUnitTime := scalarUnitTime_probability
  have hsub : E ∩ (fun p => scalarTimeBlockCode J hJ p.2) ⁻¹' {j} ⊆
      univ ×ˢ timeCell J j := by
    intro p hp
    exact ⟨mem_univ _, (scalarTimeBlockCode_eq_iff hJ j (hunit hp.1).2).mp hp.2⟩
  have htime : scalarUnitTime.real (timeCell J j) ≤ 1 / (J : ℝ) := by
    have h := (scalarUnitTime_le_volume (timeCell J j)).trans_eq (volume_timeCell hJ j)
    have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    simpa only [Measure.real, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / (J : ℝ))] using h'
  calc
    _ ≤ (ν.prod scalarUnitTime).real (univ ×ˢ timeCell J j) := measureReal_mono hsub
    _ = scalarUnitTime.real (timeCell J j) := by rw [measureReal_prod_prod]; simp
    _ ≤ _ := htime

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
