/-
Adapted from this LOT tree, o147, session x0498, commit 5dd59d875729,
Submission/Obl/k4_local_remainder_horizon_transfer/Normalizer.lean.
Earlier provenance is preserved below.
-/
import Submission.Obl.k4_remainder_pure_profile_normalization.SampleBridge

/-! The normalizing constant is bounded below by the retained incidence mass. -/

namespace Submission.Obl.k4_remainder_pure_profile_normalization

open MeasureTheory Filter

theorem Atlas.KnownAt.normalizer_lower {p : Data} {k M D : ℕ} {a : Atlas p k} {r : ℝ}
    (ha : a.KnownAt M D r) (hprob : ∀ γ, IsProbabilityMeasure (p.ν k γ))
    (hω : ∀ γ, 0 ≤ p.ω k γ) (hκ : 0 < a.κ) :
    a.κ⁻¹ ≤ a.system.normZ (p.ω k) (p.ν k) := by
  letI : ∀ γ, IsProbabilityMeasure (p.ν k γ) := hprob
  obtain ⟨_, _, _, _, hchart, hmass⟩ := ha
  let Z := a.system.normZ (p.ω k) (p.ν k)
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun c _ => mul_nonneg (hω _) (by positivity)
  have hbound : a.mass ≤ ENNReal.ofReal Z := by
    calc
      a.mass ≤ ∑ c, ENNReal.ofReal (p.ω k (a.γ c) *
          ((p.ν k (a.γ c) (a.A c)).toReal / (2 : ℝ) ^ a.T)) := by
        apply Finset.sum_le_sum
        intro c _
        obtain ⟨_, _, _, _, _, _, _, _, _, _, hselected, _⟩ := hchart c
        have hsub : a.F c ⊆ a.A c ×ˢ Set.Icc
            ((a.j c : ℝ) / (2 : ℝ) ^ a.T) (((a.j c : ℝ) + 1) / (2 : ℝ) ^ a.T) := by
          intro q hq
          exact ⟨(hselected q hq).2.1, (hselected q hq).2.2.1⟩
        have hlength : volume (Set.Icc ((a.j c : ℝ) / (2 : ℝ) ^ a.T)
            (((a.j c : ℝ) + 1) / (2 : ℝ) ^ a.T)) = ENNReal.ofReal (((2 : ℝ) ^ a.T)⁻¹) := by
          rw [Real.volume_Icc]
          congr 1
          ring
        have hc : ((p.ν k (a.γ c)).prod volume) (a.F c) ≤
            p.ν k (a.γ c) (a.A c) * ENNReal.ofReal (((2 : ℝ) ^ a.T)⁻¹) := by
          calc _ ≤ ((p.ν k (a.γ c)).prod volume) (a.A c ×ˢ Set.Icc
                ((a.j c : ℝ) / (2 : ℝ) ^ a.T) (((a.j c : ℝ) + 1) / (2 : ℝ) ^ a.T)) :=
                  measure_mono hsub
            _ = _ := by rw [Measure.prod_prod, hlength]
        calc ENNReal.ofReal (p.ω k (a.γ c)) * ((p.ν k (a.γ c)).prod volume) (a.F c)
            ≤ ENNReal.ofReal (p.ω k (a.γ c)) *
              (p.ν k (a.γ c) (a.A c) * ENNReal.ofReal (((2 : ℝ) ^ a.T)⁻¹)) :=
                mul_le_mul' le_rfl hc
          _ = ENNReal.ofReal (p.ω k (a.γ c) *
              ((p.ν k (a.γ c) (a.A c)).toReal / (2 : ℝ) ^ a.T)) := by
            rw [div_eq_mul_inv, ENNReal.ofReal_mul (hω _),
              ENNReal.ofReal_mul ENNReal.toReal_nonneg,
              ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ = ENNReal.ofReal Z := by
        dsimp only [Z, Normalization.ChartSystem.normZ, Atlas.system]
        rw [ENNReal.ofReal_sum_of_nonneg (fun c _ => mul_nonneg (hω _) (by positivity))]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmass.trans hbound)
  simpa only [ENNReal.toReal_ofReal (inv_nonneg.mpr hκ.le), ENNReal.toReal_ofReal hZ0] using hreal

/-- Normalization loses at most the same subpower factor as the known atlas. -/
theorem KnownSequence.normalizer_subpower {p : Data} (hp : p.Valid)
    {M D : ℕ} {r h : ℝ} (s : KnownSequence p M D r h) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      ((s.atlas k).system.normZ (p.ω (s.index k)) (p.ν (s.index k)))⁻¹ ≤
        p.N (s.index k) ^ ε := by
  obtain ⟨_, _, hsample⟩ := hp.sampleProblem
  intro ε hε
  filter_upwards [s.slack_subpower ε hε] with k hk
  have hκ : 0 < (s.atlas k).κ := by linarith [s.slack_one k]
  have hZ := (s.valid k).normalizer_lower (hsample (s.index k)).prob
    (hsample (s.index k)).weight_nonneg hκ
  have hi : ((s.atlas k).system.normZ (p.ω (s.index k)) (p.ν (s.index k)))⁻¹ ≤
      (s.atlas k).κ := by
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hκ) hZ
  exact hi.trans hk

end Submission.Obl.k4_remainder_pure_profile_normalization
