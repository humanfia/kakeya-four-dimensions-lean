import Submission.Obl.k4_remainder_pure_profile_normalization.ChartTransport
import Submission.Obl.k4_remainder_pure_profile_normalization.Overlap

namespace Submission.Obl.k4_remainder_pure_profile_normalization
open MeasureTheory Set
open scoped ENNReal

/-- Intermediate upper tails pull back to original-world upper tails with only
the common normalizer and terminal-list overlap loss. -/
theorem KnownSystem.Valid.normalized_upper_tail {p : Data} (hp : p.Valid)
    {k M D : ℕ} {r σ : ℝ} {s : KnownSystem p k} (hs : s.Valid M D r)
    (hr : 0 ≤ r) (hσ : 0 ≤ σ) (hL : r + σ ≤ p.L)
    (hprior : ∀ b, 0 < s.atlas.priorMass b) (hκ : 0 < s.atlas.κ) (hi : ℝ) :
    (∑ b, ENNReal.ofReal (s.atlas.system.normWeight (p.ω k) (p.ν k) b) *
      s.atlas.normalizedMeasure b {z |
        ENNReal.ofReal (s.atlas.densityRatio b * hi) <
          s.atlas.normalizedDensity (fun b => (hs.chart b).1) (composedDepth (p.N k) r σ) b
            (s.atlas.normalizedObservation r σ b z)}) ≤
      ENNReal.ofReal (s.atlas.system.normZ (p.ω k) (p.ν k))⁻¹ * ENNReal.ofReal s.atlas.κ *
        ∑ γ, ENNReal.ofReal (p.ω k γ) * p.incidenceMeasure k γ {z |
          ENNReal.ofReal hi < p.g k γ (composedDepth (p.N k) r σ)
            (obs (p.B k γ) (δ (p.N k) (composedDepth (p.N k) r σ)) z)} := by
  let t := composedDepth (p.N k) r σ
  let hD := fun b => (hs.chart b).1
  let Bad (b : Fin s.atlas.C) : Set Incidence := {z |
    ENNReal.ofReal (s.atlas.densityRatio b * hi) < s.atlas.normalizedDensity hD t b
      (s.atlas.normalizedObservation r σ b z)}
  let Old (γ : Fin (p.W k)) : Set Incidence := {z |
    ENNReal.ofReal hi < p.g k γ t (obs (p.B k γ) (δ (p.N k) t) z)}
  have hN : 1 < p.N k := by linarith [hp.1 k]
  have ht : 0 ≤ t := composedDepth_nonneg hN hr hσ
  have htL : t ≤ p.L := (composedDepth_bounds hN r σ).2.trans hL
  have hobs (b : Fin s.atlas.C) : Measurable (s.atlas.normalizedObservation r σ b) :=
    Submission.Obl.k4_native_grid_profile_extension.measurable_pureObservation _ _
  have hBad (b : Fin s.atlas.C) : MeasurableSet (Bad b) :=
    measurableSet_lt measurable_const ((s.atlas.measurable_normalizedDensity hD t b).comp (hobs b))
  have hOld (γ : Fin (p.W k)) : MeasurableSet (Old γ) :=
    measurableSet_lt measurable_const ((hp.2.2.2.2.2.2.2.2.2.1 k γ t ht htL).1.comp
      (Submission.Obl.k4_native_grid_profile_extension.measurable_pureObservation _ _))
  have hbound (b : Fin s.atlas.C) :
      s.atlas.selectedMeasure b ((s.atlas.system.frameOf b).normInc ⁻¹' Bad b) ≤
        s.atlas.selectedMeasure b (Old (s.atlas.γ b)) := by
    apply measure_mono_ae
    filter_upwards [hs.sampled_labelDensity_le hp ht htL b] with z hz hbad
    change ENNReal.ofReal (s.atlas.densityRatio b * hi) <
      s.atlas.normalizedDensity hD t b (s.atlas.normalizedObservation r σ b
        ((s.atlas.system.frameOf b).normInc z)) at hbad
    rw [s.atlas.normalizedDensity_observed hD hN b z] at hbad
    by_contra hn
    have hgood : p.g k (s.atlas.γ b) t (obs (p.B k (s.atlas.γ b)) (δ (p.N k) t) z) ≤
        ENNReal.ofReal hi := not_lt.mp hn
    have hh : ENNReal.ofReal (s.atlas.densityRatio b) * s.atlas.labelDensity t b
        (obs (p.B k (s.atlas.γ b)) (δ (p.N k) t) z) ≤
          ENNReal.ofReal (s.atlas.densityRatio b * hi) := by
      calc _ ≤ ENNReal.ofReal (s.atlas.densityRatio b) * ENNReal.ofReal hi :=
          mul_le_mul' le_rfl (hz.trans hgood)
        _ = _ := (ENNReal.ofReal_mul (div_nonneg (abs_nonneg _) (hprior b).le)).symm
    exact not_lt_of_ge hh hbad
  have hm (b : Fin s.atlas.C) := hs.normalized_weighted_event hp hprior hκ b (Bad b) (hBad b)
  change (∑ b, _ * s.atlas.normalizedMeasure b (Bad b)) ≤ _
  calc
    (∑ b, _ * s.atlas.normalizedMeasure b (Bad b)) =
        ENNReal.ofReal (s.atlas.system.normZ (p.ω k) (p.ν k))⁻¹ *
          ∑ b, ENNReal.ofReal (p.ω k (s.atlas.γ b)) *
            s.atlas.selectedMeasure b ((s.atlas.system.frameOf b).normInc ⁻¹' Bad b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      simpa only [mul_assoc] using hm b
    _ ≤ ENNReal.ofReal (s.atlas.system.normZ (p.ω k) (p.ν k))⁻¹ *
          ∑ b, ENNReal.ofReal (p.ω k (s.atlas.γ b)) * s.atlas.selectedMeasure b (Old (s.atlas.γ b)) := by
      apply mul_le_mul' le_rfl
      exact Finset.sum_le_sum fun b _ => mul_le_mul' le_rfl (hbound b)
    _ ≤ ENNReal.ofReal (s.atlas.system.normZ (p.ω k) (p.ν k))⁻¹ *
          (ENNReal.ofReal s.atlas.κ * ∑ γ, ENNReal.ofReal (p.ω k γ) *
            p.incidenceMeasure k γ (Old γ)) :=
      mul_le_mul' le_rfl (hs.weighted_overlap (fun γ => ENNReal.ofReal (p.ω k γ)) Old hOld)
    _ = _ := by rw [mul_assoc]

/-- At every remaining depth, the original terminal list supplies a lower
density comparison. The lower tail costs only epsilon times the list slack. -/
theorem KnownSystem.Valid.normalized_lower_tail {p : Data} (hp : p.Valid)
    {k M D : ℕ} {r σ : ℝ} {s : KnownSystem p k} (hs : s.Valid M D r)
    (hr : 0 ≤ r) (hσ : 0 ≤ σ) (hL : r + σ ≤ p.L)
    (hprior : ∀ b, 0 < s.atlas.priorMass b) (hκ : 0 < s.atlas.κ) (lo ε : ℝ)
    (hε : 0 ≤ ε) :
    (∑ b, ENNReal.ofReal (s.atlas.system.normWeight (p.ω k) (p.ν k) b) *
      s.atlas.normalizedMeasure b {z |
        s.atlas.normalizedDensity (fun b => (hs.chart b).1) (composedDepth (p.N k) r σ) b
            (s.atlas.normalizedObservation r σ b z) <
          ENNReal.ofReal (s.atlas.densityRatio b * ε * lo)}) ≤
      ENNReal.ofReal (s.atlas.system.normZ (p.ω k) (p.ν k))⁻¹ * ENNReal.ofReal s.atlas.κ *
        ((∑ γ, ENNReal.ofReal (p.ω k γ) * p.incidenceMeasure k γ {z |
          p.g k γ p.L (obs (p.B k γ) (δ (p.N k) p.L) z) < ENNReal.ofReal lo}) +
          ENNReal.ofReal ε) := by
  let t := composedDepth (p.N k) r σ
  let hD := fun b => (hs.chart b).1
  let Bad (b : Fin s.atlas.C) : Set Incidence := {z |
    s.atlas.normalizedDensity hD t b (s.atlas.normalizedObservation r σ b z) <
      ENNReal.ofReal (s.atlas.densityRatio b * ε * lo)}
  let Old (γ : Fin (p.W k)) : Set Incidence := {z |
    p.g k γ p.L (obs (p.B k γ) (δ (p.N k) p.L) z) < ENNReal.ofReal lo}
  let Low (b : Fin s.atlas.C) : Set Incidence := {z |
    s.atlas.labelDensity p.L b (s.atlas.terminalObservation b z) <
      ENNReal.ofReal ε * p.g k (s.atlas.γ b) p.L (s.atlas.terminalObservation b z)}
  have hN : 1 < p.N k := by linarith [hp.1 k]
  have ht : 0 ≤ t := composedDepth_nonneg hN hr hσ
  have htL : t ≤ p.L := (composedDepth_bounds hN r σ).2.trans hL
  have hobs (b : Fin s.atlas.C) : Measurable (s.atlas.normalizedObservation r σ b) :=
    Submission.Obl.k4_native_grid_profile_extension.measurable_pureObservation _ _
  have hBad (b : Fin s.atlas.C) : MeasurableSet (Bad b) :=
    measurableSet_lt ((s.atlas.measurable_normalizedDensity hD t b).comp (hobs b)) measurable_const
  have hOld (γ : Fin (p.W k)) : MeasurableSet (Old γ) :=
    measurableSet_lt ((hp.2.2.2.2.2.2.2.2.2.1 k γ p.L hp.L_pos.le le_rfl).1.comp
      (Submission.Obl.k4_native_grid_profile_extension.measurable_pureObservation _ _)) measurable_const
  have hbound (b : Fin s.atlas.C) :
      s.atlas.selectedMeasure b ((s.atlas.system.frameOf b).normInc ⁻¹' Bad b) ≤
        s.atlas.selectedMeasure b (Old (s.atlas.γ b)) + s.atlas.selectedMeasure b (Low b) := by
    refine (measure_mono_ae ?_).trans (measure_union_le _ _)
    filter_upwards [hs.labelDensity_antitone hp ht htL le_rfl b] with z hz hbad
    change s.atlas.normalizedDensity hD t b (s.atlas.normalizedObservation r σ b
      ((s.atlas.system.frameOf b).normInc z)) <
        ENNReal.ofReal (s.atlas.densityRatio b * ε * lo) at hbad
    rw [s.atlas.normalizedDensity_observed hD hN b z] at hbad
    by_contra hn
    have hOldGood : ENNReal.ofReal lo ≤
        p.g k (s.atlas.γ b) p.L (s.atlas.terminalObservation b z) := not_lt.mp (not_or.mp hn).1
    have hLowGood : ENNReal.ofReal ε * p.g k (s.atlas.γ b) p.L
        (s.atlas.terminalObservation b z) ≤ s.atlas.labelDensity p.L b
          (s.atlas.terminalObservation b z) := not_lt.mp (not_or.mp hn).2
    have hh : ENNReal.ofReal (s.atlas.densityRatio b * ε * lo) ≤
        ENNReal.ofReal (s.atlas.densityRatio b) * s.atlas.labelDensity t b
          (obs (p.B k (s.atlas.γ b)) (δ (p.N k) t) z) := by
      have hratio : 0 ≤ s.atlas.densityRatio b :=
        div_nonneg (abs_nonneg _) (hprior b).le
      rw [ENNReal.ofReal_mul (mul_nonneg hratio hε), ENNReal.ofReal_mul hratio, mul_assoc]
      exact mul_le_mul' le_rfl ((mul_le_mul' le_rfl hOldGood).trans (hLowGood.trans hz))
    exact not_lt_of_ge hh hbad
  have hm (b : Fin s.atlas.C) := hs.normalized_weighted_event hp hprior hκ b (Bad b) (hBad b)
  change (∑ b, _ * s.atlas.normalizedMeasure b (Bad b)) ≤ _
  calc
    (∑ b, _ * s.atlas.normalizedMeasure b (Bad b)) =
        ENNReal.ofReal (s.atlas.system.normZ (p.ω k) (p.ν k))⁻¹ *
          ∑ b, ENNReal.ofReal (p.ω k (s.atlas.γ b)) *
            s.atlas.selectedMeasure b ((s.atlas.system.frameOf b).normInc ⁻¹' Bad b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      simpa only [mul_assoc] using hm b
    _ ≤ ENNReal.ofReal (s.atlas.system.normZ (p.ω k) (p.ν k))⁻¹ *
          ((∑ b, ENNReal.ofReal (p.ω k (s.atlas.γ b)) * s.atlas.selectedMeasure b (Old (s.atlas.γ b))) +
            ∑ b, ENNReal.ofReal (p.ω k (s.atlas.γ b)) * s.atlas.selectedMeasure b (Low b)) := by
      apply mul_le_mul' le_rfl
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro b _
      simpa only [mul_add] using mul_le_mul' (le_rfl (a := ENNReal.ofReal (p.ω k (s.atlas.γ b)))) (hbound b)
    _ ≤ ENNReal.ofReal (s.atlas.system.normZ (p.ω k) (p.ν k))⁻¹ *
          (ENNReal.ofReal s.atlas.κ * (∑ γ, ENNReal.ofReal (p.ω k γ) * p.incidenceMeasure k γ (Old γ)) +
            ENNReal.ofReal ε * ENNReal.ofReal s.atlas.κ) :=
      mul_le_mul' le_rfl (add_le_add
        (hs.weighted_overlap (fun γ => ENNReal.ofReal (p.ω k γ)) Old hOld)
        (hs.canonical_terminal_refinement hp (ENNReal.ofReal ε)))
    _ = _ := by ring

end Submission.Obl.k4_remainder_pure_profile_normalization
