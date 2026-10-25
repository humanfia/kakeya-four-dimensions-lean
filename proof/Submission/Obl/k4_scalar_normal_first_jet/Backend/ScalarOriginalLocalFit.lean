/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarOriginalLocalFit.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarOriginalLocalFit.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCollisionMeasureModel
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarActiveGrid
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarActiveCells
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarMeasuredFit

/-! A local affine fit on substantial ORIGINAL active times, from the actual
continuous collision event. All grid ceilings are derived internally. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity
open scoped ENNReal

theorem original_active_scalar_affine_fit (hproj : ProjectionDichotomy)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ η p₀ : ℝ, 0 < η ∧ 0 < p₀ ∧ ∀ {Λ : Type*} [MeasurableSpace Λ]
      (μ : Measure ℝ) [IsProbabilityMeasure μ] (ν : Measure Λ) [IsFiniteMeasure ν]
      {jointDim : ℝ} (p K C Cs error ell N : ℝ) (n : ℕ), μ ≤ volume →
      0 < p → p ≤ p₀ → p ≤ 1 → 1 ≤ K → 0 < C → 0 ≤ Cs → 0 ≤ error → 0 ≤ ell →
      ∀ D : OriginalScalarCollisionModel ν p K jointDim C error,
      11 ≤ N → 16 * (2 * K + 1) + 3 ≤ N → 33 * N < p ^ (ε - 1) →
      11 ≤ p ^ (-η) → 4 * (K + 1) + 3 ≤ p ^ (-η) →
      (2 * (n : ℝ) + 3) * Cs * (1 + 2 * (n : ℝ)) ^ (1 - σ) ≤ p ^ (-η) →
      error + 6 * K + 2 * K ^ 2 + 1 ≤ (n : ℝ) →
      IntervalAD p (1 - σ) Cs D.scalarSupport →
      2 * (N ^ 3 * p ^ (η - 3)) * (scalarCollisionPairCeiling p K jointDim C error * p) +
        ((D.velocityGrid.card : ℝ) ^ 2 * scalarCollisionPairCeiling p K jointDim C error) *
          (ell * (D.timeGrid.card : ℝ)) ≤ (μ.prod (ν.prod ν)).real D.pairEvent →
      ∃ (T : Set ℝ) (a slope : ℝ), MeasurableSet T ∧
        T ⊆ {u | 0 < (ν.prod ν) (Prod.mk u ⁻¹' D.pairEvent) ∧ |u| ≤ 1} ∧
        ENNReal.ofReal (ell * p ^ (ε - 1)) ≤ volume T ∧ |a| ≤ 9 ∧ |slope| ≤ 4 ∧
        ∀ u ∈ T, |D.row u - (a + slope * u)| ≤ 13 * p := by
  classical
  obtain ⟨η, p₀, hη, hp₀, hfit⟩ := original_mass_scalar_collision_fit hproj hσ hσ1 hε
  refine ⟨η, p₀, hη, hp₀, ?_⟩
  intro Λ _ μ _ ν _ jointDim p K C Cs error ell N n hμ hp hpmax hp1 hK hC hCs he hell D
    hNA hNB hlarge hbudgetA hbudgetB hbudgetD hn hAD hmass
  let cap := scalarCollisionPairCeiling p K jointDim C error
  let Q := (D.velocityGrid.card : ℝ) ^ 2 * cap
  have hcap : 0 < cap := scalarCollisionPairCeiling_pos hp hK hC he
  have hQ : 0 ≤ Q := mul_nonneg (sq_nonneg _) hcap.le
  have hsection : ∀ u, (ν.prod ν) (Prod.mk u ⁻¹' D.pairEvent) ≤ ENNReal.ofReal Q := by
    intro u
    have h := ENNReal.ofReal_le_ofReal (D.pair_section_cap hp hK hC.le he u)
    simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top (ν.prod ν) _)] using h
  have htimecode : Measurable (fun u : ℝ => (⌊u / p⌋ : ℤ)) :=
    Int.measurable_floor.comp (measurable_id.div_const p)
  obtain ⟨U, hU, hactive, hUK, hfloor, hloss⟩ := prepare_active_parameter_cells μ (ν.prod ν)
    D.pair_measurable htimecode D.timeGrid (fun u q hq => D.time_cover (u, q) hq)
    (ENNReal.ofReal Q) (ENNReal.ofReal ell) hsection
  have hUbound : ∀ u ∈ U, |u| ≤ 1 := by
    intro u hu
    have hpos := hactive hu
    obtain ⟨q, hq⟩ := nonempty_of_measure_ne_zero (ne_of_gt hpos)
    exact (D.pair_geometry (u, q) hq).1
  obtain ⟨Kt, t, hKt, hcoverU, hrep⟩ := original_active_grid_representatives U D.timeGrid p hUK hUbound
  let P := D.pairEvent ∩ (U ×ˢ univ)
  have hP : MeasurableSet P := D.pair_measurable.inter (hU.prod MeasurableSet.univ)
  have hlossReal : (μ.prod (ν.prod ν)).real D.pairEvent ≤
      (μ.prod (ν.prod ν)).real P + Q * (ell * (D.timeGrid.card : ℝ)) := by
    have h := ENNReal.toReal_mono (by finiteness) hloss
    rw [ENNReal.toReal_add (measure_ne_top (μ.prod (ν.prod ν)) _) (by finiteness)] at h
    simpa only [Measure.real, P,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hQ, ENNReal.toReal_ofReal hell, ENNReal.toReal_natCast] using h
  have hmassFit : 2 * (N ^ 3 * p ^ (η - 3)) * (cap * p) ≤ (μ.prod (ν.prod ν)).real P := by
    change 2 * (N ^ 3 * p ^ (η - 3)) * (cap * p) + Q * (ell * D.timeGrid.card) ≤ _ at hmass
    linarith
  have hcoverP : ∀ q ∈ P, D.tupleCode q ∈ Kt ×ˢ (D.velocityGrid ×ˢ D.velocityGrid) := by
    intro q hq
    have hg := D.pair_geometry q hq.1
    exact Finset.mem_product.mpr ⟨hcoverU q.1 hq.2.1, Finset.mem_product.mpr
      ⟨D.velocity_cover _ hg.2.1, D.velocity_cover _ hg.2.2.1⟩⟩
  have hcell : ∀ q ∈ Kt ×ˢ (D.velocityGrid ×ˢ D.velocityGrid),
      (μ.prod (ν.prod ν)).real (P ∩ D.tupleCode ⁻¹' {q}) ≤ cap * p := by
    intro q hq
    have hsub : P ∩ D.tupleCode ⁻¹' {q} ⊆ D.pairEvent ∩ D.tupleCode ⁻¹' {q} :=
      fun x hx => ⟨hx.1.1, hx.2⟩
    exact (measureReal_mono hsub).trans (D.tuple_cell_cap μ hμ hp hK hC.le he q)
  have hnear : ∀ q ∈ P, ∃ s ∈ D.scalarSupport,
      |t (D.tupleCode q).1 * (D.slopeGraph (p * (D.tupleCode q).2.1) -
          D.slopeGraph (p * (D.tupleCode q).2.2)) +
        D.row (t (D.tupleCode q).1) * (p * (D.tupleCode q).2.1 - p * (D.tupleCode q).2.2) -
          (s + -(p * D.startBin))| ≤ (n : ℝ) * p := by
    intro q hq
    have hk := hcoverU q.1 hq.2.1
    obtain ⟨s, hs, hbound⟩ := D.frozen_dot_support hp hK q hq.1 (hrep _ hk).2.1 (hrep _ hk).2.2
    exact ⟨s, hs, hbound.trans (mul_le_mul_of_nonneg_right hn hp.le)⟩
  have hb := bounded_grid_slope_representatives D.labels D.velocity D.slopeGraph hK hp hp1
    D.slope_compare D.coordinate_bound D.velocityGrid D.velocity_witness
  have hrow t : |D.row t| ≤ |t| := by
    simpa only [D.row_zero, sub_zero] using D.row_compare t 0
  obtain ⟨K', a, slope, hK', hcard, ha, hslope, hfitrow⟩ := hfit p hp hpmax (μ.prod (ν.prod ν))
    P D.tupleCode Kt D.velocityGrid t (fun j => p * j) D.row D.slopeGraph D.scalarSupport
    (2 * K + 1) K Cs N (-(p * D.startBin)) (cap * p) n (by linarith) (by linarith) hCs hNA hNB hlarge
    (mul_pos hcap hp) (fun k hk => ⟨(hrep k hk).2.2, hrow _⟩)
    (fun k hk k' hk' => D.row_compare _ _) hb
    (fun j hj j' hj' => D.slope_compare _ _)
    (fun k hk => (hrep k hk).2.1) (fun j hj => mesh_lower_endpoint_index hp j)
    hbudgetA hbudgetB hbudgetD (Filter.Eventually.of_forall hcoverP) hcell hmassFit hAD hnear
  let V : ℤ → Set ℝ := fun k => U ∩ {u | ⌊u / p⌋ = k}
  have hVm : ∀ k, MeasurableSet (V k) := fun k =>
    hU.inter (measurableSet_eq_fun htimecode measurable_const)
  have hVfloor : ∀ k ∈ K', ENNReal.ofReal ell ≤ μ (V k) := by
    intro k hk
    have hkn := hK' hk
    rcases hfloor k (hKt hkn) with hempty | hlong
    · have hmem : t k ∈ U ∩ (fun u : ℝ => (⌊u / p⌋ : ℤ)) ⁻¹' {k} :=
        ⟨(hrep k hkn).1, (hrep k hkn).2.1⟩
      exact (Set.notMem_empty _ (hempty ▸ hmem)).elim
    · exact hlong.le
  have hVdisj : ∀ i ∈ K', ∀ j ∈ K', i ≠ j → Disjoint (V i) (V j) := by
    intro i hi j hj hij
    apply disjoint_left.mpr
    intro u hui huj
    exact hij (hui.2.symm.trans huj.2)
  let T : Set ℝ := ⋃ k ∈ K', V k
  have hTm : MeasurableSet T := K'.measurableSet_biUnion (fun k hk => hVm k)
  have hμmass : ENNReal.ofReal ((K'.card : ℝ) * ell) ≤ μ T := by
    change _ ≤ μ (⋃ k ∈ K', V k)
    rw [measure_biUnion_finset hVdisj (fun k hk => hVm k)]
    calc
      _ = ∑ _k ∈ K', ENNReal.ofReal ell := by
        simp only [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ _ := Finset.sum_le_sum hVfloor
  refine ⟨T, a, slope, hTm, ?_, ?_, ha, hslope, ?_⟩
  · intro u hu
    obtain ⟨k, hk, hu⟩ := mem_iUnion₂.mp hu
    exact ⟨hactive hu.1, hUbound _ hu.1⟩
  · calc
      _ ≤ ENNReal.ofReal ((K'.card : ℝ) * ell) :=
        ENNReal.ofReal_le_ofReal (by nlinarith only [mul_le_mul_of_nonneg_right hcard hell])
      _ ≤ μ T := hμmass
      _ ≤ volume T := hμ T
  · intro u hu
    obtain ⟨k, hk, hu⟩ := mem_iUnion₂.mp hu
    have hkn := hK' hk
    have hdist : |u - t k| ≤ p := same_mesh_cell_close hp (hu.2.trans (hrep k hkn).2.1.symm)
    have hrowdist : |D.row u - D.row (t k)| ≤ p := (D.row_compare _ _).trans hdist
    have hslopeDist : |slope * (t k - u)| ≤ 4 * p := by
      rw [abs_mul, abs_sub_comm]
      exact mul_le_mul hslope hdist (abs_nonneg _) (by norm_num)
    have heq : D.row u - (a + slope * u) =
        (D.row u - D.row (t k)) + (D.row (t k) - (a + slope * t k)) + slope * (t k - u) := by ring
    rw [heq]
    have htri := (abs_add_le ((D.row u - D.row (t k)) + (D.row (t k) - (a + slope * t k)))
      (slope * (t k - u))).trans (add_le_add (abs_add_le _ _) le_rfl)
    linarith [hfitrow k hk]

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
