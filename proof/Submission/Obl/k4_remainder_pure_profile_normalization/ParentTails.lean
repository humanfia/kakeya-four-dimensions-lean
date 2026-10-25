import Submission.Obl.k4_remainder_pure_profile_normalization.ComposedDepth
import Submission.Obl.k4_remainder_pure_profile_normalization.VariableNativeDepth

namespace Submission.Obl.k4_remainder_pure_profile_normalization
open MeasureTheory Filter Set
open Submission.Obl.k4_native_grid_profile_extension.Profiles
open scoped ENNReal Topology

/-- Decode the world-tagged varying-depth squeeze as the frozen weighted tail. -/
theorem Data.Valid.varying_depth_typical {p : Data} (hp : p.Valid)
    {a : ℕ → ℝ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) p.L)
    (hat : Tendsto a atTop (𝓝 t)) (ha : ∀ k, a k ∈ Icc (0 : ℝ) p.L) :
    ∀ τ : ℝ, 0 < τ → IsPowerSmall p.N (fun k =>
      ∑ γ, ENNReal.ofReal (p.ω k γ) * p.incidenceMeasure k γ
        {z | p.g k γ (a k) (obs (p.B k γ) (δ (p.N k) (a k)) z) <
            ENNReal.ofReal (p.N k ^ (-p.f t - τ)) ∨
          ENNReal.ofReal (p.N k ^ (-p.f t + τ)) <
            p.g k γ (a k) (obs (p.B k γ) (δ (p.N k) (a k)) z)}) := by
  have hh := hp.sampledDensity_at_tendsto_depth ht hat (Eventually.of_forall ha)
  intro τ hτ
  apply IsPowerSmall.mono (hh τ hτ)
  apply Eventually.of_forall
  intro k
  have hdm := hp.measurable_sampledDensity (ha k).1 (ha k).2 k
  have hm : MeasurableSet {z : p.SampleState k |
      p.sampledDensity (a k) k z < ENNReal.ofReal (p.N k ^ (-p.f t - τ)) ∨
      ENNReal.ofReal (p.N k ^ (-p.f t + τ)) < p.sampledDensity (a k) k z} :=
    (measurableSet_lt hdm measurable_const).union (measurableSet_lt measurable_const hdm)
  rw [Data.sampleMeasure_apply p k hm]
  exact le_rfl

/-- The original exponent at `r+s` is still typical at the exact rounded
composed depth; this includes the terminal endpoint. -/
theorem Data.Valid.composed_depth_typical {p : Data} (hp : p.Valid)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hL : r + s ≤ p.L) :
    ∀ τ : ℝ, 0 < τ → IsPowerSmall p.N (fun k =>
      ∑ γ, ENNReal.ofReal (p.ω k γ) * p.incidenceMeasure k γ
        {z | p.g k γ (composedDepth (p.N k) r s)
            (obs (p.B k γ) (δ (p.N k) (composedDepth (p.N k) r s)) z) <
            ENNReal.ofReal (p.N k ^ (-p.f (r + s) - τ)) ∨
          ENNReal.ofReal (p.N k ^ (-p.f (r + s) + τ)) <
            p.g k γ (composedDepth (p.N k) r s)
              (obs (p.B k γ) (δ (p.N k) (composedDepth (p.N k) r s)) z)}) := by
  apply hp.varying_depth_typical ⟨add_nonneg hr hs, hL⟩
    (composedDepth_tendsto (fun k => by linarith [hp.1 k]) hp.2.1 r s)
  intro k
  exact ⟨composedDepth_nonneg (by linarith [hp.1 k]) hr hs,
    (composedDepth_bounds (by linarith [hp.1 k]) r s).2.trans hL⟩

end Submission.Obl.k4_remainder_pure_profile_normalization
