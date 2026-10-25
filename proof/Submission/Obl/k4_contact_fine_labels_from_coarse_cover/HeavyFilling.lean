-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/HeavyFilling.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.HeavyFineDensity
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.TimeAlignedFilling
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.FillingVolume

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

open Set Filter MeasureTheory MvPolynomial
open Submission.Lib.K4ContactNormalization (affineBase)

variable {α : Type*} [MeasurableSpace α] (p : Model α)

/-- A heavy original true-label state supplies the time-aligned volume
filling needed by the deterministic affine palette adapter. -/
theorem eventually_heavy_filling (hp : p.Valid)
    (H : ℕ → ℝ) (hH : ∀ k, 1 ≤ H k)
    (hHsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ p.N k ^ ε)
    {s : ℝ} (hs : 0 < s) :
    ∀ᶠ k in atTop, ∀ i : Fin (p.n k s), p.Label k s i →
      p.q k s ≤ 1 → p.q k s ≤ p.K k * p.g k s →
      ∀ C : Set (α × ℝ), MeasurableSet C →
      ENNReal.ofReal (p.N k ^ (-6 * s)) ≤ p.μ k C →
      ∀ τ : ℝ, 0 ≤ τ →
      ENNReal.ofReal τ * (ENNReal.ofReal (p.q k s) * p.ν k (p.A k s i)) ≤ p.μ k C →
      ∀ (L : Fin 4 → ℝ) (F : MvPolynomial (Fin 4) ℝ), F.totalDegree ≤ 2 →
      (∀ u ∈ C, p.GoodPoint k u) →
      (∀ u ∈ C, |p.x k u.1 u.2 3 - eval (p.x k u.1 u.2) (affineBase L)| ≤ H k) →
      (∀ u ∈ C, |eval (p.x k u.1 u.2) F| ≤ p.K k * p.a k s ∧
        |eval (p.x k u.1 u.2) (pderiv 3 F)| ≤ p.K k ∧
        |eval (p.x k u.1 u.2) (pderiv 3 (pderiv 3 F))| ≤ p.K k / p.a k s ∧
        (p.K k)⁻¹ ≤ |eval (p.x k u.1 u.2) (pderiv 3 F)|) →
      ∀ t₀ : ℝ, (∀ u ∈ C, p.base k u 0 ∈ Ico t₀ (t₀ + p.q k s)) →
      ∀ M : ℕ, 0 < M → p.N k ^ (-100 * s) / p.q k s ≤ (M : ℝ)⁻¹ →
      ∃ E : Set (Fin 3 → ℝ), MeasurableSet E ∧
        (∀ z ∈ E, z 0 ∈ Icc t₀ (t₀ + p.q k s)) ∧
        ENNReal.ofReal ((τ / (8640 * p.K k ^ 6)) * p.q k s ^ 4) ≤ volume E ∧
        ∀ z ∈ E, ∃ u ∈ C, ∀ e, |z e - p.base k u e| ≤ (M : ℝ)⁻¹ := by
  filter_upwards [eventually_heavy_fine_density p hp H hH hHsub hs] with k hk
  intro i hi hq1 hqg C hC hmass τ hτ hrelative L F hF hgood hclose hfit
    t₀ htime M hM hresolve
  have hN := Valid.N_pos p hp k
  have hK := Valid.K_pos p hp k
  have ha := Valid.a_pos p hp k s
  obtain ⟨E, hE, hEt, hmassE, hnear⟩ := exists_time_aligned_filling
    (p.μ k) (p.base k) C (p.q_pos k s) hq1
    (Real.rpow_pos_of_pos hN (-100 * s))
    (by positivity : 0 ≤ 320 * p.K k ^ 4 * p.a k s ^ p.d)
    M hM hresolve htime (hk C hC hmass L F hF hgood hclose hfit)
  exact ⟨E, hE, hEt,
    filling_volume_of_original_reference p hp hi hqg hτ (p.μ k C) (volume E) hrelative hmassE,
    hnear⟩

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model
