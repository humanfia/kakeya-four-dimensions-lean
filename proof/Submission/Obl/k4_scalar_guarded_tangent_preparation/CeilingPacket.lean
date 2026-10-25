import Submission.Obl.k4_scalar_guarded_tangent_preparation.GraphNorm
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.MassBounds

/-!
# Packets under a pure observation ceiling

If the pure observations of a measure `σ` have a pushed-forward law at most `θ` times the
reference measure, then a chart packet carries `σ`-mass at most `θ (2Λ + 3)` times the area
of its base parallelogram (restricted where the graph is bounded). With a mass floor this
gives the whole-block graph bound. This is the version of `current_packet_base_cap` and
`graph_norm_of_current_mass` for a ceiling on the law itself rather than on the density of a
larger law; the box count follows `thin_packet_diff_le` of the accepted o094.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open MeasureTheory Set
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction
open scoped ENNReal

/-- The mass of a packet under a pure observation ceiling. -/
theorem ceiling_packet_le {σ : Measure (Coeff × ℝ)} {a θ : ℝ} (ha : 0 < a)
    (hceil : σ.map (obsL a) ≤ ENNReal.ofReal θ • (volume.prod Measure.count))
    {P : MvPolynomial (Fin 2) ℝ} (hP : P.totalDegree ≤ 2)
    {A : Set Coeff} {t₀ q u v w Λ K : ℝ} (hΛ : 0 ≤ Λ)
    (hconf : ∀ l ∈ A, ∀ t ∈ Icc t₀ (t₀ + q),
      |spatial l t - (u + v * t)| ≤ w ∧
      |hidden l t - MvPolynomial.eval ![t, spatial l t] P| ≤ Λ * a)
    (hval : ∀ l ∈ A, ∀ t ∈ Icc t₀ (t₀ + q),
      |MvPolynomial.eval ![t, spatial l t] P| ≤ K) :
    σ (A ×ˢ Icc t₀ (t₀ + q)) ≤
      ENNReal.ofReal θ * (ENNReal.ofReal (2 * Λ + 3) *
        volume (graphGoodRegion P t₀ q u v w K)) := by
  set f : ℝ → ℝ → ℝ := fun t y => MvPolynomial.eval ![t, y] P with hfdef
  have hf : IsQuad2 f := isQuad2_eval P hP
  set Z : Set (ℝ × ℝ) := graphGoodRegion P t₀ q u v w K with hZ
  have hZm : MeasurableSet Z := by
    show MeasurableSet ((Prod.fst ⁻¹' Icc t₀ (t₀ + q)) ∩
      ({p : ℝ × ℝ | |p.2 - (u + v * p.1)| ≤ w} ∩ {p : ℝ × ℝ | |f p.1 p.2| ≤ K}))
    refine (measurableSet_Icc.preimage measurable_fst).inter ((measurableSet_le ?_ ?_).inter
      (measurableSet_le ?_ ?_))
    · fun_prop
    · fun_prop
    · exact (continuous_abs.comp hf.continuous).measurable
    · fun_prop
  set ZF : Set (Fin 2 → ℝ) := {v | (v 0, v 1) ∈ Z} with hZF
  have hZFm : MeasurableSet ZF := hZm.preimage (by fun_prop)
  have hfm : Measurable (fun v : Fin 2 → ℝ => f (v 0) (v 1) / a) := by
    have h' : Continuous (fun v : Fin 2 → ℝ => f (v 0) (v 1)) :=
      hf.continuous.comp (f := fun v : Fin 2 → ℝ => (v 0, v 1)) (by fun_prop)
    exact h'.measurable.div_const a
  set S : Set ((Fin 2 → ℝ) × ℤ) :=
    {x | x.1 ∈ ZF ∧ |(x.2 : ℝ) - f (x.1 0) (x.1 1) / a| ≤ Λ + 1} with hS
  have hSm : MeasurableSet S := by
    show MeasurableSet ((Prod.fst ⁻¹' ZF) ∩
      {x : (Fin 2 → ℝ) × ℤ | |(x.2 : ℝ) - f (x.1 0) (x.1 1) / a| ≤ Λ + 1})
    refine (hZFm.preimage measurable_fst).inter (measurableSet_le ?_ measurable_const)
    have h2 : Measurable (fun p : (Fin 2 → ℝ) × ℤ => ((p.2 : ℤ) : ℝ)) :=
      (measurable_from_top (f := fun k : ℤ => (k : ℝ))).comp measurable_snd
    exact (h2.sub (hfm.comp measurable_fst)).abs
  have hsub : A ×ˢ Icc t₀ (t₀ + q) ⊆ obsL a ⁻¹' S := by
    rintro ⟨l, t⟩ ⟨hl, ht⟩
    obtain ⟨hc, hx⟩ := hconf l hl t ht
    refine ⟨?_, ?_⟩
    · show (t, spatial l t) ∈ Z
      exact ⟨ht, hc, hval l hl t ht⟩
    · show |((⌊hidden l t / a⌋ : ℤ) : ℝ) - f t (spatial l t) / a| ≤ Λ + 1
      exact floor_near_of_fit ha hx
  calc σ (A ×ˢ Icc t₀ (t₀ + q)) ≤ σ (obsL a ⁻¹' S) := measure_mono hsub
    _ = (σ.map (obsL a)) S := (Measure.map_apply (measurable_obsL a) hSm).symm
    _ ≤ (ENNReal.ofReal θ • (volume.prod Measure.count)) S := hceil S
    _ = ENNReal.ofReal θ * (volume.prod Measure.count) S := rfl
    _ ≤ ENNReal.ofReal θ * (ENNReal.ofReal (2 * (Λ + 1) + 1) * volume ZF) := by
        gcongr
        exact prod_count_box_le hZFm hfm (by linarith)
    _ = ENNReal.ofReal θ * (ENNReal.ofReal (2 * Λ + 3) * volume Z) := by
        rw [hZF, volume_fin2_eq hZm]
        congr 3
        ring

/-- A mass floor on the current packet, below a pure observation ceiling of a larger law,
gives the whole-block graph bound. -/
theorem graph_norm_of_ceiling {σ ρ : Measure (Coeff × ℝ)} (hρ : ρ ≤ σ) {a θ : ℝ}
    (ha : 0 < a) (hθ : 0 < θ)
    (hceil : σ.map (obsL a) ≤ ENNReal.ofReal θ • (volume.prod Measure.count))
    {P : MvPolynomial (Fin 2) ℝ} (hP : P.totalDegree ≤ 2)
    {A : Set Coeff} {t₀ q u v w Λ K : ℝ}
    (hK : 1 ≤ K) (hq : 0 < q) (hw : 0 < w) (hwidth : q ≤ K * w) (hΛ : 0 ≤ Λ)
    (hconf : ∀ l ∈ A, ∀ t ∈ Icc t₀ (t₀ + q),
      |spatial l t - (u + v * t)| ≤ w ∧
      |hidden l t - MvPolynomial.eval ![t, spatial l t] P| ≤ Λ * a)
    (hval : ∀ l ∈ A, ∀ t ∈ Icc t₀ (t₀ + q),
      |MvPolynomial.eval ![t, spatial l t] P| ≤ K)
    (hmass : ENNReal.ofReal θ * ENNReal.ofReal (2 * Λ + 3) *
        ENNReal.ofReal ((q * (2 * w)) / K) ≤ ρ (A ×ˢ Icc t₀ (t₀ + q)))
    {t z : ℝ} (ht : t ∈ Icc t₀ (t₀ + q)) (hz : z ∈ Icc (-2 : ℝ) 2) :
    |MvPolynomial.eval ![t, u + t * v + z * q] P| ≤ 4665600 * K ^ 7 := by
  have hcap := (hρ _).trans (ceiling_packet_le ha hceil hP hΛ hconf hval)
  have hfactor0 : ENNReal.ofReal θ * ENNReal.ofReal (2 * Λ + 3) ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr hθ).ne' (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hfactortop : ENNReal.ofReal θ * ENNReal.ofReal (2 * Λ + 3) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hvolume : ENNReal.ofReal ((q * (2 * w)) / K) ≤
      volume (graphGoodRegion P t₀ q u v w K) := by
    apply (ENNReal.mul_le_mul_iff_left hfactor0 hfactortop).mp
    calc ENNReal.ofReal ((q * (2 * w)) / K) * (ENNReal.ofReal θ * ENNReal.ofReal (2 * Λ + 3))
        = ENNReal.ofReal θ * ENNReal.ofReal (2 * Λ + 3) * ENNReal.ofReal ((q * (2 * w)) / K) :=
          mul_comm _ _
      _ ≤ ρ (A ×ˢ Icc t₀ (t₀ + q)) := hmass
      _ ≤ ENNReal.ofReal θ * (ENNReal.ofReal (2 * Λ + 3) *
          volume (graphGoodRegion P t₀ q u v w K)) := hcap
      _ = volume (graphGoodRegion P t₀ q u v w K) *
          (ENNReal.ofReal θ * ENNReal.ofReal (2 * Λ + 3)) := by
          ring
  exact graph_norm_on_block hP hK hq hw hwidth hvolume ht hz

end Submission.Obl.k4_scalar_guarded_tangent_preparation
