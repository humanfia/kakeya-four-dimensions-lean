/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/CorrectedCharts.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.CorrectedScalarSupport
import Submission.Obl.k4_subcritical_corrected_scalar_charts.GoodChartSeeds
import Submission.Obl.k4_subcritical_corrected_scalar_charts.DenseCorrections
import Submission.Obl.k4_subcritical_corrected_scalar_charts.CorrectionLosses

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory Filter
open Submission.Obl.k4_critical_intercept_concentration.Data

noncomputable section

/-- Directional correction and scalar support from the original endpoint and
native families. All later restrictions preserve the original chart floors. -/
theorem correctedCharts : CorrectedCharts := by
  classical
  intro α _ cfg h M RE s₀ hM hMe hs₀ hU hgrid hpaired depth hdepth ξ hξ
  let m := min cfg.κ (1 - 2 * cfg.κ)
  have hm : 0 < m := lt_min h.rate_pos (by linarith [h.subcritical_rate])
  have hm1 : m ≤ 1 := (min_le_left _ _).trans h.rate_le_one
  let ε := min (ξ / 100) (s₀ * m / 1000)
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεξ : ε ≤ ξ / 100 := min_le_left _ _
  have hεs : ε ≤ s₀ * m / 1000 := min_le_right _ _
  have hgap : 10 * ε < ξ := by linarith
  have hη : 0 < 10 * ε := by positivity
  have hηs : 10 * ε ≤ s₀ * min cfg.κ (1 - 2 * cfg.κ) / 16 := by
    change 10 * ε ≤ s₀ * m / 16
    nlinarith [mul_pos hs₀ hm]
  have hεsmall : ε ≤ s₀ * min cfg.κ (1 - 2 * cfg.κ) / 16 := by linarith
  have hdepthU : ∀ r, s₀ < depth r ∧ depth r ≤ cfg.U := by
    intro r
    have hnear := (hdepth r).2
    have hsmall := mul_le_mul_of_nonneg_left hm1 hs₀.le
    refine ⟨(hdepth r).1, ?_⟩
    change depth r - s₀ ≤ s₀ * m / 16 at hnear
    linarith
  have hparentU : s₀ ≤ cfg.U := by linarith
  have hnatives : ∀ᶠ k in atTop, ∀ r, Nonempty (cfg.NativeLevel k (depth r)) :=
    Filter.eventually_all.mpr fun r => h.eventually_native_level
      (hs₀.trans (hdepth r).1) (hdepthU r).2
  have hsupports := Filter.eventually_all.mpr fun r : Fin 3 =>
    h.eventually_corrected_scalar_support hs₀ (hdepth r).1.le (hdepth r).2
      hgrid hη hηs hξ
  filter_upwards [hpaired ε hε, h.eventually_native_level hs₀ hparentU,
    h.eventually_native_level (show 0 < 3 * s₀ / 2 by positivity) hU.le, hnatives,
    h.eventually_correction_event_cover hs₀ hU.le depth hdepthU,
    h.eventually_correction_event_fit hs₀ hε hεsmall,
    h.eventually_correction_losses hs₀ hε,
    h.eventually_corrected_chart_budget hε hgap, hsupports]
    with k hpair hparent hfine hterminal hcover hfit hloss hbudget hsupport
  obtain ⟨parent⟩ := hparent
  obtain ⟨fine⟩ := hfine
  let terminal : ∀ r, cfg.NativeLevel k (depth r) := fun r => Classical.choice (hterminal r)
  obtain ⟨sample⟩ := hpair.exists_chosen_sample h parent
  let A := cfg.N k ^ (-s₀)
  let D := cfg.N k ^ (-(2 * cfg.κ * s₀))
  let χ := cfg.N k ^ (-M)
  let σ := cfg.N k ^ (-(20 * s₀))
  let w := fun r : Fin 3 => cfg.N k ^ (-(depth r - s₀))
  let δ := cfg.N k ^ (-(s₀ * m / 4))
  let τ := cfg.N k ^ (-(3 * ε))
  let E := sample.correctionEvent parent depth
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hN1 : 1 ≤ cfg.N k := by linarith [h.scale k]
  have hA : 0 < A := Real.rpow_pos_of_pos hN _
  have hD : 0 < D := Real.rpow_pos_of_pos hN _
  have hA1 : A ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hτ : 0 < τ := Real.rpow_pos_of_pos hN _
  have hτK : τ ≤ cfg.K k := (Real.rpow_le_one_of_one_le_of_nonpos hN1
    (show -(3 * ε) ≤ 0 by linarith)).trans (h.subpower.1 k)
  have hK : 0 < cfg.K k := by linarith [h.subpower.1 k]
  letI : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  have hdom := sample.le_rho.trans ((h.basic k).2.2.2.2.1.trans (h.basic k).2.2.2.1)
  have hmass : ENNReal.ofReal (2 * τ) ≤ sample.σ univ :=
    (ENNReal.ofReal_le_ofReal hloss.1).trans sample.mass
  obtain ⟨β, F, hβ, hF, hmassF, hFmem⟩ := exists_dense_prior_relative_corrections
    (cfg.ν k) sample.σ sample.originalGoodChart (sample.measurableSet_originalGoodChart h)
    sample.originalGoodChart_disjoint E
    (sample.measurableSet_correctionEvent h parent fine depth terminal)
    (sample.correctionEvent_subset parent depth) (hcover sample hMe.le parent fine terminal)
    (fun _ => sample.fine.charts.baselineSelector) sample.coarse.charts.g (D / A)
    (sample.signal parent) (sample.measurable_signal parent) hK hτ hτK
    (show 0 ≤ 6 * cfg.N k ^ ε by positivity) (show 0 ≤ δ by dsimp [δ]; positivity)
    hdom hmass (fun c p hp => sample.correctionEvent_signal_bound h parent depth c hp)
    (hfit sample parent fine depth)
  have hβbound : ∀ c e, |β c e| ≤ cfg.N k ^ (10 * ε) :=
    fun c e => (hβ c e).trans hloss.2.1
  let ρ' := sample.σ.restrict F
  have hρ' : ρ' ≤ cfg.ρ k := Measure.restrict_le_self.trans sample.le_rho
  have hρ'mass : ENNReal.ofReal (cfg.N k ^ (-ξ)) ≤ ρ' univ := by
    rw [show ρ' univ = sample.σ F from Measure.restrict_apply_univ F]
    exact (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hN1
      (show -ξ ≤ -(10 * ε) by linarith))).trans
      ((ENNReal.ofReal_le_ofReal hloss.2.2).trans hmassF)
  have hEc (c : Fin sample.coarse.charts.n) {p : α × ℝ}
      (hpF : p ∈ F) (hpc : p.1 ∈ sample.originalGoodChart c) :
      p ∈ E c ∧ |sample.signal parent c p.2 - fiberDerivative (fiberCorrection (β c)) p.2| ≤ δ := by
    obtain ⟨c', hpE, hpβ⟩ := hFmem p hpF
    have he : c' = c := by
      by_contra hne
      exact disjoint_left.mp (sample.originalGoodChart_disjoint hne) hpE.1 hpc
    simpa only [he] using And.intro hpE hpβ
  have hρ'cover : ∀ᵐ p ∂ρ', ∃ c, p.1 ∈ sample.seedCharts.G c := by
    filter_upwards [ae_restrict_mem hF] with p hp
    obtain ⟨c, hpE, _⟩ := hFmem p hp
    exact ⟨c, hpE.1⟩
  let C := sample.seedCharts.withCorrections β A D
  refine ⟨C, ρ', ?_⟩
  apply (sample.seed_prepared h parent hMe.le (show ε ≤ ξ by linarith) hbudget.2).corrected_prepared
    β hβbound hA hA1 hD hbudget.1 hρ' hρ'mass hρ'cover
  intro c r
  change Fin sample.coarse.charts.n at c
  by_cases hc : (sample.originalGoodChart c).Nonempty
  · obtain ⟨hpc, hv⟩ := sample.originalGoodChart_center_bounds h hM hs₀ hc
    let Ec := {p : α × ℝ | p ∈ F ∧ p.1 ∈ sample.originalGoodChart c}
    have hEbase : ∀ p ∈ Ec, p.2 ∈ Icc (0 : ℝ) 1 ∧
        ⌊cfg.b k p.1 0 / D⌋ = sample.coarse.charts.q c 1 ∧
        ⌊cfg.b k p.1 1 / D⌋ = sample.coarse.charts.q c 2 ∧
        ⌊cfg.b k p.1 3 / χ⌋ = sample.coarse.charts.q c 0 ∧
        |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ χ := by
      intro p hp
      have he := (hEc c hp.1 hp.2).1
      have hlab := sample.coarse.labels c p.1 he.1.1
      exact ⟨he.2.1, hlab.2.1, hlab.2.2, hlab.1, he.1.2.2⟩
    have hnamed : ∀ p ∈ Ec, ∃ z, cfg.namedNativeIncidence k s₀ (depth r) (sample.choice c) p z :=
      fun p hp => (hEc c hp.1 hp.2).1.2.2.2.2 r
    have hsig : ∀ p ∈ Ec, ∀ ip : Fin (cfg.n k s₀),
        sample.choice c (cfg.j k s₀ ip) = some ip →
        p.2 ∈ I (cfg.T k s₀) (cfg.j k s₀ ip) →
        |nativeFiberSignal (sample.coarse.charts.g c) (parent.L ip) D A p.2 -
          (β c 0 + β c 1 * p.2 + β c 2 * p.2 ^ 2)| ≤ δ := by
      intro p hp ip hi ht
      obtain ⟨he, hβfit⟩ := hEc c hp.1 hp.2
      rw [he.2.2.1 (cfg.j k s₀ ip) ht, sample.row_of_choice parent hi,
        fiberDerivative_correction] at hβfit
      exact hβfit
    have hεη : cfg.N k ^ ε ≤ cfg.N k ^ (10 * ε) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    obtain ⟨S, hS, hScov⟩ := hsupport r parent (terminal r)
      (sample.coarse.charts.q c 1) (sample.coarse.charts.q c 2) (sample.coarse.charts.q c 0)
      (sample.coarse.charts.g c) (β c) (sample.choice c) Ec hpc hv (hβbound c 2)
      (fun t ht p hp q hq => (sample.coarse.box c t ht p hp q hq).trans hεη)
      hEbase hnamed hsig
    refine ⟨S, hS, ?_⟩
    filter_upwards [ae_restrict_mem hF] with p hp
    intro hpc
    exact hScov p ⟨hp, hpc⟩
  · refine ⟨∅, ?_, Filter.Eventually.of_forall fun p hp => False.elim (hc ⟨p.1, hp⟩)⟩
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    positivity

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
