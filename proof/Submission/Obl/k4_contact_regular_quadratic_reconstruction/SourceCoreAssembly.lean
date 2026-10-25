import Submission.Obl.k4_contact_regular_quadratic_reconstruction.Model

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction

open MeasureTheory Set Filter MvPolynomial
open Submission.Lib.K4ContactNormalization
open Submission.Obl.k4_critical_switching_state_preparation.Data

noncomputable section

namespace Model

variable {α : Type} [MeasurableSpace α] {cfg : Model α}

theorem AffineCandidate.mono_tolerance {k : ℕ} {s v η ε : ℝ}
    {i : Fin (cfg.n k s)} (ha : cfg.AffineCandidate k s v η i)
    (hN : 1 ≤ cfg.N k) (hηε : η ≤ ε) : cfg.AffineCandidate k s v ε i := by
  obtain ⟨σ, L, hσ, hmass, hsource⟩ := ha
  refine ⟨σ, L, hσ, ?_, ?_⟩
  · have hweight : ENNReal.ofReal (cfg.N k ^ (-cfg.d * v - ε) / (2 : ℝ) ^ cfg.T k s) ≤
        ENNReal.ofReal (cfg.N k ^ (-cfg.d * v - η) / (2 : ℝ) ^ cfg.T k s) := by
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    exact (mul_le_mul_left hweight _).trans hmass
  · filter_upwards [hsource] with p hp
    refine ⟨hp.1, hp.2.1, ?_⟩
    intro t ht
    exact (hp.2.2 t ht).trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hN hηε) (by positivity))

theorem VelocityCandidate.mono_tolerance {k : ℕ} {s v η ε R : ℝ}
    {i : Fin (cfg.n k s)} (ha : cfg.VelocityCandidate k s v η R i)
    (hN : 1 ≤ cfg.N k) (hηε : η ≤ ε) : cfg.VelocityCandidate k s v ε R i := by
  obtain ⟨z, hz, hmass⟩ := ha
  refine ⟨z, hz, ?_⟩
  have hweight : ENNReal.ofReal (cfg.N k ^ (-ε) / (2 : ℝ) ^ cfg.T k s) ≤
      ENNReal.ofReal (cfg.N k ^ (-η) / (2 : ℝ) ^ cfg.T k s) := by
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  refine (mul_le_mul_left hweight _).trans (hmass.trans (measure_mono ?_))
  intro p hp
  exact ⟨hp.1, hp.2.1, hp.2.2.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hN hηε) (by positivity))⟩

/-- Increasing tolerance preserves the same shifted test and all of its
original witnesses, including the active derivative floor. -/
theorem ShiftedCandidate.mono_tolerance {k : ℕ} {s v η ε R : ℝ}
    {i : Fin (cfg.n k s)} (ha : cfg.ShiftedCandidate k s v η R i)
    (hN : 1 ≤ cfg.N k) (hηε : η ≤ ε) : cfg.ShiftedCandidate k s v ε R i := by
  obtain ⟨L, G, hG, hcoeff, hmass⟩ := ha
  refine ⟨L, G, hG, hcoeff, ?_⟩
  have hpower : cfg.N k ^ η ≤ cfg.N k ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hN hηε
  have hneg : cfg.N k ^ (-ε) ≤ cfg.N k ^ (-η) :=
    Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hηε)
  have hweight : ENNReal.ofReal (cfg.N k ^ (-cfg.d * v - ε) / (2 : ℝ) ^ cfg.T k s) ≤
      ENNReal.ofReal (cfg.N k ^ (-cfg.d * v - η) / (2 : ℝ) ^ cfg.T k s) := by
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hηε])
  refine (mul_le_mul_left hweight _).trans (hmass.trans (measure_mono ?_))
  intro p hp
  refine ⟨hp.1, hp.2.1, ?_, hneg.trans hp.2.2.2⟩
  intro t ht
  obtain ⟨hy, hv, hd, hdd⟩ := hp.2.2.1 t ht
  exact ⟨hy, hv.trans (mul_le_mul_of_nonneg_right hpower (by positivity)),
    hd.trans hpower, hdd.trans (div_le_div_of_nonneg_right hpower (by positivity))⟩

/-- The remaining analytic interface: on a sufficiently small fixed horizon,
any desired output tolerance admits a positive input tolerance for the second
affine preparation, preserving the original coarse label. -/
def SecondAffineCore (cfg : Model α) : Prop :=
  ∃ V : ℝ, 0 < V ∧ V ≤ cfg.U ∧
    ∀ R : ℝ, 1 < R → ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ᶠ k in atTop, ∀ (s v : ℝ) (i : Fin (cfg.n k s)),
        R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R → s + v ≤ V →
        cfg.ShiftedCandidate k s v η R i → cfg.AffineCandidate k s v ε i

/-- All horizon choices and tolerance losses are discharged once the
per-sample second affine preparation is available. -/
theorem Valid.affine_candidates_of_core (h : cfg.Valid)
    (hcore : cfg.SecondAffineCore) (hshift : cfg.ShiftedCandidates) : cfg.AffineCandidates := by
  obtain ⟨V, hV, hVU, hcore⟩ := hcore
  obtain ⟨R, hR, hshift⟩ := hshift V hV hVU
  refine ⟨R, hR, ?_⟩
  intro ε hε
  obtain ⟨η₀, hη₀, hcore⟩ := hcore R hR ε hε
  let η : ℝ := min η₀ ε
  have hη : 0 < η := lt_min hη₀ hε
  have hη₀' : η ≤ η₀ := min_le_left _ _
  have hηε : η ≤ ε := min_le_right _ _
  apply ((hshift η hη).and_eventually hcore).mono
  rintro k ⟨⟨s, v, i, hs, hsR, hv, hvR, hsv, hbranch⟩, hk⟩
  have hN : 1 ≤ cfg.N k := by linarith only [h.scale k]
  refine ⟨s, v, i, hs, hsR, hv, hvR, hsv.trans hVU, ?_⟩
  rcases hbranch with hq | hz
  · exact Or.inl (hk s v i hs hsR hv hvR hsv (hq.mono_tolerance hN hη₀'))
  · exact Or.inr (hz.mono_tolerance hN hηε)

end Model

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction
