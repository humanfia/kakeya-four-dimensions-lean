/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarGridHierarchy.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarGridHierarchy.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGridAffineFit
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGridStageBounds

/-! A finite family of scalar affine rows on one unchanged original law. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

structure ScalarGridHierarchy {Λ : Type*} [MeasurableSpace Λ] {n : ℕ}
    (ν : Measure Λ) (E : Set (Λ × ℝ)) (F : ℝ → ℝ)
    (J : Fin n → ℕ) (hJ : ∀ i, 0 < J i) (p : Fin n → ℝ) (B : ℝ) where
  times : Set ℝ
  slope : Fin n → ℝ → ℝ
  intercept : Fin n → ℝ → ℝ
  measurable_times : MeasurableSet times
  unit_time : times ⊆ Ico (0 : ℝ) 1
  active_time : times ⊆ scalarNormalTimes E
  measurable_slope : ∀ i, Measurable (slope i)
  measurable_intercept : ∀ i, Measurable (intercept i)
  bounded : ∀ i t, |slope i t| ≤ B ∧ |intercept i t| ≤ B
  mass : ENNReal.ofReal (B⁻¹) ≤ (ν.prod volume) (E ∩ (univ ×ˢ times))
  time_floor : ∀ t ∈ times, ENNReal.ofReal (B⁻¹) ≤ ν {l | (l, t) ∈ E ∩ (univ ×ˢ times)}
  constant_on_grid : ∀ i t, t ∈ times → ∀ u, u ∈ times →
    scalarTimeBlockCode (J i) (hJ i) t = scalarTimeBlockCode (J i) (hJ i) u →
      slope i t = slope i u ∧ intercept i t = intercept i u
  fit : ∀ i q, q ∈ E ∩ (univ ×ˢ times) →
    |F q.2 - (intercept i q.2 + slope i q.2 * q.2)| ≤ B * (1 / (J i : ℝ)) * p i

theorem exists_initial_scalar_grid_hierarchy {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsProbabilityMeasure ν] {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) {K : ℝ} (hK : 1 ≤ K)
    (hmass : K⁻¹ ≤ (ν.prod volume).real E) (F : ℝ → ℝ)
    (J : Fin 0 → ℕ) (hJ : ∀ i, 0 < J i) (p : Fin 0 → ℝ) :
    Nonempty (ScalarGridHierarchy ν E F J hJ p (8 * K)) := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hτ : 0 < 1 / (8 * K) := by positivity
  have hbudget : 4 * (1 / (8 * K)) ≤ K⁻¹ := by field_simp; nlinarith
  obtain ⟨U, _, hUm, hUunit, hUmass, hfloor, _, _⟩ :=
    prepare_original_scalar_blocks ν hE hunit hτ hbudget hmass (J := 1) (by norm_num)
  have hUactive : U ⊆ scalarNormalTimes E := by
    intro t ht
    have hpos := (ENNReal.ofReal_pos.mpr hτ).trans_le (hfloor t ht)
    obtain ⟨l, hl⟩ := nonempty_of_measure_ne_zero (ne_of_gt hpos)
    exact ⟨l, hl.1⟩
  have hfinite := original_unit_incidence_ne_top ν (hE.inter (MeasurableSet.univ.prod hUm))
    (fun q hq => hunit hq.1)
  have hnum : (8 * K)⁻¹ ≤ K⁻¹ / 2 := by
    have he : (8 * K)⁻¹ = K⁻¹ / 8 := by field_simp
    rw [he]
    linarith [inv_pos.mpr hKpos]
  have hmass' : ENNReal.ofReal ((8 * K)⁻¹) ≤ (ν.prod volume) (E ∩ (univ ×ˢ U)) := by
    calc
      _ ≤ ENNReal.ofReal ((ν.prod volume).real (E ∩ (univ ×ˢ U))) :=
        ENNReal.ofReal_le_ofReal (hnum.trans hUmass)
      _ = _ := ENNReal.ofReal_toReal hfinite
  refine ⟨{
    times := U
    slope := Fin.elim0
    intercept := Fin.elim0
    measurable_times := hUm
    unit_time := hUunit
    active_time := hUactive
    measurable_slope := fun i => Fin.elim0 i
    measurable_intercept := fun i => Fin.elim0 i
    bounded := fun i => Fin.elim0 i
    mass := hmass'
    time_floor := by simpa only [one_div] using hfloor
    constant_on_grid := fun i => Fin.elim0 i
    fit := fun i => Fin.elim0 i }⟩

namespace ScalarGridHierarchy

theorem extend {Λ : Type*} [MeasurableSpace Λ] {n : ℕ}
    {D : ScalarMotion Λ} {ν : Measure Λ} [IsProbabilityMeasure ν] {E : Set (Λ × ℝ)}
    {F : ℝ → ℝ} {S : ℝ → Set ℝ} {K B Q ζ d : ℝ}
    (J : Fin (n + 1) → ℕ) (hJ : ∀ i, 0 < J i) (p : Fin (n + 1) → ℝ)
    (G : ScalarGridHierarchy ν E F (fun i => J i.succ) (fun i => hJ i.succ) (fun i => p i.succ) B)
    (h : ScalarNormalHyp D ν E F S K ζ d) (hζ : 0 < ζ) (hKB : K ≤ B)
    (hB : 1 ≤ B) (hQ : 1 ≤ Q) (hp : ∀ i, 0 ≤ p i)
    (hHp : 1 / (J 0 : ℝ) ≤ p 0) (hζH : ζ ≤ (1 / (J 0 : ℝ)) ^ 2)
    (hfit : OriginalScalarBlockFitAt (d := d) Λ (8 * B) (p 0) Q⁻¹) :
    Nonempty (ScalarGridHierarchy ν E F J hJ p (scalarGridStageBound B Q)) := by
  let R := E ∩ (univ ×ˢ G.times)
  have hR : MeasurableSet R := h.event_measurable.inter (MeasurableSet.univ.prod G.measurable_times)
  have hRunit : R ⊆ univ ×ˢ Icc (0 : ℝ) 1 := fun q hq => h.unit_time hq.1
  have hRnormal : ScalarNormalHyp D ν R F S B ζ d :=
    (h.restrict_event hR inter_subset_left).increase_constant hζ hKB
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hRmass : B⁻¹ ≤ (ν.prod volume).real R := by
    have hh := ENNReal.toReal_mono (original_unit_incidence_ne_top ν hR hRunit) G.mass
    simpa only [measureReal_def, ENNReal.toReal_ofReal (inv_nonneg.mpr hBpos.le)] using hh
  obtain ⟨V, A, C, hVm, hVunit, hVactive, hAm, hCm, hbound, hvol, hmassV,
      hfloorV, hconstant, hfitV⟩ :=
    original_scalar_grid_affine_fit hRnormal hB hζ (inv_nonneg.mpr hQpos.le)
      hRmass (hJ 0) hHp hζH hfit
  have hVU : V ⊆ G.times := by
    rintro t ht
    obtain ⟨l, hl⟩ := hVactive ht
    exact hl.2.2
  have hRVequal : R ∩ (univ ×ˢ V) = E ∩ (univ ×ˢ V) := by
    ext q
    constructor
    · exact fun hq => ⟨hq.1.1, hq.2⟩
    · exact fun hq => ⟨⟨hq.1, mem_univ _, hVU hq.2.2⟩, hq.2⟩
  rw [hRVequal] at hmassV hfloorV hfitV
  obtain ⟨hnew1, hBnew, hnewbound, hnewfloor⟩ := scalarGridStageBound_bounds hB hQ
  have hsmall i : 0 ≤ (1 / (J i : ℝ)) * p i :=
    mul_nonneg (by positivity) (hp i)
  refine ⟨{
    times := V
    slope := Fin.cases A G.slope
    intercept := Fin.cases C G.intercept
    measurable_times := hVm
    unit_time := hVunit
    active_time := fun t ht => by
      obtain ⟨l, hl⟩ := hVactive ht
      exact ⟨l, hl.1⟩
    measurable_slope := by
      intro i
      exact Fin.cases hAm G.measurable_slope i
    measurable_intercept := by
      intro i
      exact Fin.cases hCm G.measurable_intercept i
    bounded := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · intro t
        exact ⟨(hbound t).1.trans hnewbound, (hbound t).2.trans hnewbound⟩
      · intro t
        exact ⟨(G.bounded j t).1.trans hBnew, (G.bounded j t).2.trans hBnew⟩
    mass := (ENNReal.ofReal_le_ofReal (scalarGridStageBound_mass hB hQ)).trans hmassV
    time_floor := fun t ht =>
      (ENNReal.ofReal_le_ofReal (scalarGridStageBound_floor hB hQ)).trans (hfloorV t ht)
    constant_on_grid := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hconstant
      · intro t ht u hu hcode
        exact G.constant_on_grid j t (hVU ht) u (hVU hu) hcode
    fit := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · intro q hq
        exact (hfitV q hq).trans (by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hnewbound (hsmall 0))
      · intro q hq
        exact (G.fit j q ⟨hq.1, mem_univ _, hVU hq.2.2⟩).trans (by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hBnew (hsmall j.succ)) }⟩

end ScalarGridHierarchy

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
