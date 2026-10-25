/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarPrunedHierarchy.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarPrunedHierarchy.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarHierarchyCurrentTaylor
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarHierarchyFloorPruning

/-! One original restriction carries all hierarchy floors and the finest Taylor row. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

namespace ScalarGridHierarchy

theorem exists_common_current_floor_set_of_pos {Λ : Type*} [MeasurableSpace Λ] {n : ℕ}
    {ν : Measure Λ} [IsProbabilityMeasure ν] {E : Set (Λ × ℝ)} {F : ℝ → ℝ}
    {J : Fin n → ℕ} {hJ : ∀ i, 0 < J i} {p : Fin n → ℝ} {B : ℝ}
    (G : ScalarGridHierarchy ν E F J hJ p B) (hE : MeasurableSet E) (hB : 0 < B) (hn0 : 0 < n) :
    ∃ R : Set (Λ × ℝ), MeasurableSet R ∧ R ⊆ E ∩ (univ ×ˢ G.times) ∧
      (2 * B)⁻¹ ≤ (ν.prod volume).real R ∧
      ∀ q ∈ R, ∀ i,
        ENNReal.ofReal ((1 / (J i : ℝ)) / (4 * (n : ℝ) * B)) ≤
          (ν.prod volume) (R ∩
            (univ ×ˢ timeCell (J i) (scalarTimeBlockCode (J i) (hJ i) q.2))) := by
  let P := E ∩ (univ ×ˢ G.times)
  let K : ℝ := 4 * (n : ℝ) * B
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hK : 0 < K := by dsimp [K]; positivity
  have hPm : MeasurableSet P := hE.inter (MeasurableSet.univ.prod G.measurable_times)
  have hPunit : P ⊆ univ ×ˢ Ico (0 : ℝ) 1 :=
    fun q hq => ⟨mem_univ _, G.unit_time hq.2.2⟩
  have hfinite := original_unit_incidence_ne_top ν hPm
    (fun q hq => ⟨mem_univ _, (hPunit hq).2.1, (hPunit hq).2.2.le⟩)
  obtain ⟨R, hRm, hRP, hloss, hfloor⟩ :=
    original_scalar_hierarchy_floor_pruning ν hPm hPunit J hJ hK
  have hmassP : B⁻¹ ≤ (ν.prod volume).real P := by
    have hh := ENNReal.toReal_mono hfinite G.mass
    simpa only [measureReal_def, ENNReal.toReal_ofReal (inv_nonneg.mpr hB.le)] using hh
  have hlossR : (ν.prod volume).real (P \ R) ≤ (n : ℝ) / K := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hloss
    change (ν.prod volume).real (P \ R) ≤ (ENNReal.ofReal ((n : ℝ) / K)).toReal at hh
    rw [ENNReal.toReal_ofReal (div_nonneg (Nat.cast_nonneg n) hK.le)] at hh
    exact hh
  have hsplit := measureReal_sdiff hRP hRm hfinite
  have hbudget : (2 * B)⁻¹ + (n : ℝ) / K ≤ B⁻¹ := by
    dsimp [K]
    field_simp
    nlinarith
  refine ⟨R, hRm, hRP, ?_, hfloor⟩
  linarith

theorem exists_common_current_floor_set {Λ : Type*} [MeasurableSpace Λ] {n : ℕ}
    {ν : Measure Λ} [IsProbabilityMeasure ν] {E : Set (Λ × ℝ)} {F : ℝ → ℝ}
    {J : Fin (n + 1) → ℕ} {hJ : ∀ i, 0 < J i} {p : Fin (n + 1) → ℝ} {B : ℝ}
    (G : ScalarGridHierarchy ν E F J hJ p B) (hE : MeasurableSet E) (hB : 0 < B) :
    ∃ R : Set (Λ × ℝ), MeasurableSet R ∧ R ⊆ E ∩ (univ ×ˢ G.times) ∧
      (2 * B)⁻¹ ≤ (ν.prod volume).real R ∧
      ∀ q ∈ R, ∀ i,
        ENNReal.ofReal ((1 / (J i : ℝ)) / (4 * (n + 1 : ℕ) * B)) ≤
          (ν.prod volume) (R ∩
            (univ ×ˢ timeCell (J i) (scalarTimeBlockCode (J i) (hJ i) q.2))) :=
  G.exists_common_current_floor_set_of_pos hE hB (by omega)

theorem exists_first_jet_taylor_restriction {Λ : Type*} [MeasurableSpace Λ] {n : ℕ}
    {ν : Measure Λ} [IsProbabilityMeasure ν] {E : Set (Λ × ℝ)} {F : ℝ → ℝ}
    {J : Fin (n + 1) → ℕ} {hJ : ∀ i, 0 < J i} {p : Fin (n + 1) → ℝ} {B : ℝ}
    (G : ScalarGridHierarchy ν E F J hJ p B) (hE : MeasurableSet E) (hB : 0 < B)
    (hmesh : Antitone (fun i => 1 / (J i : ℝ)))
    (hlower : ∀ j : Fin n,
      (1 / (J j.castSucc : ℝ)) ^ (33 / 32 : ℝ) / 2 ≤ 1 / (J j.succ : ℝ))
    (hreading : ∀ i, p i ≤ 2 * (1 / (J i : ℝ)) ^ (1 / 4 : ℝ))
    (hnesting : ∀ i j, i ≤ j → ∀ t ∈ G.times, ∀ u ∈ G.times,
      scalarTimeBlockCode (J j) (hJ j) t = scalarTimeBlockCode (J j) (hJ j) u →
      scalarTimeBlockCode (J i) (hJ i) t = scalarTimeBlockCode (J i) (hJ i) u) :
    ∃ R : Set (Λ × ℝ), MeasurableSet R ∧ R ⊆ E ∩ (univ ×ˢ G.times) ∧
      (2 * B)⁻¹ ≤ (ν.prod volume).real R ∧
      (∀ q ∈ R, ∀ i,
        ENNReal.ofReal ((1 / (J i : ℝ)) / (4 * (n + 1 : ℕ) * B)) ≤
          (ν.prod volume) (R ∩
            (univ ×ˢ timeCell (J i) (scalarTimeBlockCode (J i) (hJ i) q.2)))) ∧
      ∀ q ∈ R, ∀ q' ∈ R, ∀ i,
        scalarTimeBlockCode (J i) (hJ i) q.2 = scalarTimeBlockCode (J i) (hJ i) q'.2 →
        |F q'.2 - F q.2 - (q'.2 - q.2) * G.slope (Fin.last n) q.2| ≤
          (4 * B + 32 * (n : ℝ) * B * (4 * (n + 1 : ℕ) * B)) *
            (1 / (J i : ℝ)) ^ (11 / 10 : ℝ) := by
  obtain ⟨R, hRm, hRP, hmass, hfloor⟩ := G.exists_common_current_floor_set hE hB
  refine ⟨R, hRm, hRP, hmass, hfloor, ?_⟩
  exact G.taylor_on_current_floor_set hB.le (by positivity)
    hmesh hlower hreading hnesting hRP hfloor

end ScalarGridHierarchy

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
