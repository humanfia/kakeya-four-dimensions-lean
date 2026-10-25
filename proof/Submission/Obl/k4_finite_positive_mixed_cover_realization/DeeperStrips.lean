import Submission.Obl.k4_finite_positive_mixed_cover_realization.Cover
import Submission.Obl.k4_finite_positive_mixed_cover_realization.Grid
import Submission.Obl.k4_finite_positive_mixed_cover_realization.DeepStrips

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open Submission.Lib.K4XInterface
open Submission.Obl.k4_finite_forest_width_selection
open scoped RealInnerProductSpace

/-- A deeper true label determines its thin strip in its actual ancestor's
normalized velocity coordinates. These parameters depend only on the label. -/
theorem PathData.Valid.relative_strip_table
    {W m Mp Dp i j : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ θ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → MeasureTheory.Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hNk : 1 ≤ Nk) (hij : i ≤ j)
    (hsep : 2 * θ ≤ p.nw j - p.nw i - 2 * δ₀ * L) :
    ∃ (normal : Fin p.C → Plane) (bias : Fin p.C → ℝ),
      (∀ d, ‖normal d‖ = 1) ∧
      ∀ d, p.lev d = j → ∀ l ∈ p.assigned d,
        |inner ℝ (((2 : ℝ) ^ p.T i)⁻¹ • Matrix.toEuclideanLin
          (p.frame (forestAncestor p.lev p.par d i))⁻¹
          (gv l - p.velocity (forestAncestor p.lev p.par d i))) (normal d) - bias d| ≤
            2 * p.κ * Nk ^ (-θ) := by
  classical
  have hex (d : Fin p.C) : ∃ (n : Plane) (β : ℝ), ‖n‖ = 1 ∧
      (p.lev d = j → ∀ l ∈ p.assigned d,
        |inner ℝ (((2 : ℝ) ^ p.T i)⁻¹ • Matrix.toEuclideanLin
          (p.frame (forestAncestor p.lev p.par d i))⁻¹
          (gv l - p.velocity (forestAncestor p.lev p.par d i))) n - β| ≤
            2 * p.κ * Nk ^ (-θ)) := by
    by_cases hd : p.lev d = j
    · let old := forestAncestor p.lev p.par d i
      have hOldLevel : p.lev old = i := (hp.ancestor d i (by omega)).1
      have hOld := (hp.narrowness old).1
      have hDeep := (hp.narrowness d).2
      rw [hOldLevel] at hOld
      rw [hd] at hDeep
      have hchart := hp.chart d
      rw [hd] at hchart
      obtain ⟨n, β, hn, hfit⟩ := gchart_relative_strip_of_narrowness hchart
        (show 0 < Nk by linarith) (hp.chart old).1 hOld hDeep
      refine ⟨n, β, hn, fun _ l hl => (hfit l hl).trans ?_⟩
      apply mul_le_mul_of_nonneg_left _ (by linarith [hp.one_le_slack])
      exact Real.rpow_le_rpow_of_exponent_le hNk (by linarith)
    · refine ⟨WithLp.toLp 2 ![1, 0], 0, ?_, fun hd' => (hd hd').elim⟩
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  choose normal bias hn hfit using hex
  exact ⟨normal, bias, hn, hfit⟩

/-- The original cover's room and positive path narrowness supply one deeper
true strip table, with a fixed power of the actual candidate gain. -/
theorem CoverData.Valid.deeper_strip_table
    {W m Mp Dp Mg Dg : ℕ} {p : PathData W} {c : CoverData p}
    {ℓ Nk L κ₁ δ₀ σ d₁ ρ gain ε : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → MeasureTheory.Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hc : c.Valid Nk L ω ν B d₁ ρ gain m Mg Dg ε)
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hs : FineGrid m s gain ρ) (hNk : 1 ≤ Nk) (hL : 0 < L)
    (hgain : 0 < gain) (hℓ : 0 ≤ ℓ) (hρ : 0 ≤ ρ)
    (hρ₁ : ρ ≤ 1 / 4) (hρℓ : 16 * ρ ≤ ℓ) (hδ : δ₀ ≤ ρ * gain) :
    ∃ (j : ℕ) (normal : Fin p.C → Plane) (bias : Fin p.C → ℝ),
      c.level < j ∧ j < m ∧ 0 < p.r j ∧ p.r j ≤ L ∧
      (∀ d, ‖normal d‖ = 1) ∧
      ∀ d, p.lev d = j → ∀ l ∈ p.assigned d,
        |inner ℝ (((2 : ℝ) ^ p.T c.level)⁻¹ • Matrix.toEuclideanLin
          (p.frame (forestAncestor p.lev p.par d c.level))⁻¹
          (gv l - p.velocity (forestAncestor p.lev p.par d c.level))) (normal d) - bias d| ≤
            2 * p.κ * Nk ^ (-ℓ * c.gain * L / 4) := by
  have hi := hc.1
  have hh := hc.2.1
  have hroom := hc.2.2.2.2.1
  have hh₀ : 0 < c.gain := hgain.trans_le hh
  have hρg : ρ * gain ≤ ρ * c.gain := mul_le_mul_of_nonneg_left hh hρ
  have hδh : δ₀ ≤ c.gain / 4 := by nlinarith
  obtain ⟨j, hj, hgap, hjupper⟩ := hs.deeper hL hgain hρ (by linarith) hδ hi hh
    (hp.level_bounds c.level hi).1 hroom
  have hsij : s c.level < s j := by nlinarith
  have hij : c.level < j := by
    by_contra h
    have hmono : StrictMonoOn s (Set.Iio m) := by
      apply strictMonoOn_of_lt_add_one Set.ordConnected_Iio
      intro a _ _ ha
      exact hs.1.2.2.1 a ha
    have hrev := hmono.monotoneOn hj hi (Nat.le_of_not_gt h)
    linarith
  have herrors_i := abs_le.mp (hp.level_bounds c.level hi).1
  have herrors_j := abs_le.mp (hp.level_bounds j hj).1
  have hrj : p.r j ≤ L := by
    have hδL := mul_le_mul_of_nonneg_right hδh hL.le
    have hsL := mul_le_mul_of_nonneg_right hjupper hL.le
    nlinarith
  have hsep := narrowness_gap hℓ hρ hρ₁ hρℓ hgain.le hh hL.le hδ hgap
    (hp.level_bounds c.level hi).2.2.2.2.1 (hp.level_bounds j hj).2.2.2.2.1
  obtain ⟨normal, bias, hn, hfit⟩ := hp.relative_strip_table hNk hij.le
    (show 2 * (ℓ * c.gain * L / 4) ≤ p.nw j - p.nw c.level - 2 * δ₀ * L by linarith)
  refine ⟨j, normal, bias, hij, hj, (hp.level_bounds j hj).2.1, hrj, hn, ?_⟩
  intro d hd l hl
  convert hfit d hd l hl using 1 <;> congr 2 <;> ring

end Submission.Obl.k4_finite_positive_mixed_cover_realization
