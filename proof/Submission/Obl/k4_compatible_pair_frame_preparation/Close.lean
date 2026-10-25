import Submission.Obl.k4_compatible_pair_frame_preparation.Finite
import Submission.Obl.k4_compatible_pair_frame_preparation.Seq
import Submission.Obl.k4_compatible_pair_frame_preparation.Thresholds

namespace Submission.Obl.k4_compatible_pair_frame_preparation

open MeasureTheory
open scoped ENNReal

/-- The remaining analytic estimate for the deterministic native frame. -/
def BandConstruction : Prop :=
  ∀ N W ω ν E P B f g
    (G : (k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal)
    L d, FrameData N W ω ν E P B f g L d →
  ∀ S a e u h : ℝ, 0 < a → 0 < e →
  ∀ (M D : ℕ) (depths : Finset ℝ), (0 : ℝ) ∈ depths → L ∈ depths →
    (∀ r ∈ depths, 0 ≤ r ∧ r ≤ L) →
    (∀ r ∈ Set.Icc (0 : ℝ) L, ∃ r' ∈ depths, r' ≤ r ∧ r ≤ r' + e) →
  ∀ (ε₀ : ℝ) (k : ℕ)
    (p : NativeSample True 4 (N k) (W k) (ω k) (ν k) (E k) (P k) (B k) f (g k) (G k)
      L S a e u h M D depths ε₀),
    frameSlack p.κ ≤ N k ^ (a + e) → (2 : ℝ) ^ 100 ≤ N k ^ (a + e) →
  ∀ (b : Fin p.toPrep.J) (ρ : ℝ) (U : Set (EuclideanSpace ℝ (Fin 3)))
    (F : EuclideanSpace ℝ (Fin 3) → ℝ), 0 < ρ → MeasurableSet U → Measurable F →
    ENNReal.ofReal ((2 : ℝ) ^ p.T) ^ 2 *
      ((ν k (p.toPrep.fγ b)).prod (volume.prod volume))
        (p.toPrep.bandPairs (N k) (frameSlack p.κ) b ρ U F) ≤
      ENNReal.ofReal (p.sigma * N k ^ (100 * (a + e)) *
        (max ρ (δ (N k) L) / δ (N k) L) ^ d) * volume U

/-- The finite construction and one real threshold give the sequence interface. -/
theorem frameStep_of_bandConstruction (hband : BandConstruction) : FrameStep := by
  refine ⟨100, by norm_num, ?_⟩
  intro N W ω ν E P B f g G L d hFD S a e u h ha he M D depths h0 hLmem hdep hcov
  have hFD' := hFD
  obtain ⟨hN, hNt, hL, hω, hωsum, hν, ⟨Mb, hB⟩, hE, hP, hmap, hd0, hd1, hprof⟩ := hFD'
  refine ⟨30 * (M + Mb + 10), max D 1, ?_⟩
  intro ε hε
  obtain ⟨ε₀, hε₀, hε₀le, N₀, hN₀⟩ := exists_sample_thresholds ha he hε
  refine ⟨ε₀, hε₀, N₀, ?_⟩
  intro k hNk hnat
  rw [nativeAt_iff] at hnat
  obtain ⟨p⟩ := hnat
  obtain ⟨hNk2, hX, hbudgets⟩ := hN₀ (N k) hNk
  obtain ⟨hκε, hκN, hκX, hκa⟩ := hbudgets p.κ p.κ_one p.κ_le
  letI : ∀ γ : Fin (W k), IsProbabilityMeasure (ν k γ) := fun γ => hν k γ
  let ts := p.testedSample_of_band hNk2 ha he (hB k) hκN hκX hκa hX hLmem
    (fun γ => hmap k γ L hL.le le_rfl) hκε hε₀le
    (hband N W ω ν E P B f g G L d hFD S a e u h ha he M D depths h0 hLmem hdep hcov
      ε₀ k p hκX hX)
  exact (Submission.Obl.k4_paired_test_normalization.NormalizationStep.sample_nonempty_iff
    False 4 (N k) (W k) (ω k) (ν k) (E k) (B k) L d (100 * (a + e)) h
      (30 * (M + Mb + 10)) (max D 1) ε).mp ⟨ts⟩

/-- The frozen statement follows from the analytic band estimate. -/
theorem preparation_of_bandConstruction (hband : BandConstruction) : FramePreparationStatement :=
  statement_of_frameStep (frameStep_of_bandConstruction hband)

end Submission.Obl.k4_compatible_pair_frame_preparation
