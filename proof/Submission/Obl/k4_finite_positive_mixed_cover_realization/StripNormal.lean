import Submission.Obl.k4_finite_positive_mixed_cover_realization.CoverFacts

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Submission.Lib.K4XInterface
open scoped RealInnerProductSpace

noncomputable def CoverData.unitNormal {W : ℕ} {p : PathData W} (c : CoverData p)
    (b : Fin c.n) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (c.normal b)

noncomputable def CoverData.normalizedVelocity {W : ℕ} {p : PathData W} (c : CoverData p)
    (b : Fin c.n) (l : Trajectory) : EuclideanSpace ℝ (Fin 2) :=
  ((2 : ℝ) ^ p.T c.level)⁻¹ •
    Matrix.toEuclideanLin (p.frame (c.old b))⁻¹ (gv l - p.velocity (c.old b))

section
variable {W m Mg Dg : ℕ} {p : PathData W} {c : CoverData p} {Nk L d₁ ρ gain ε : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory} {B : Fin W → ℝ}
    (hc : c.Valid Nk L ω ν B d₁ ρ gain m Mg Dg ε) (ht : c.time = false)

include hc ht

lemma CoverData.Valid.normal_unit (b : Fin c.n) : ‖c.unitNormal b‖ = 1 := by
  have h := (hc.2.2.2.2.2.2.1 b).2.2.2.2.2.2.2
  simp only [ht, Bool.false_eq_true, ↓reduceIte] at h
  have hsq : ‖c.unitNormal b‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact h.1
  nlinarith [norm_nonneg (c.unitNormal b)]

lemma CoverData.Valid.normal_fit (b : Fin c.n) (l : Trajectory) (hl : l ∈ c.assigned b) :
    |inner ℝ (c.normalizedVelocity b l) (c.unitNormal b) - c.bias b| ≤
      Nk ^ (4 * ρ * c.gain * L + 4 * ε) * Nk ^ (-c.gain * L) := by
  have h := (hc.2.2.2.2.2.2.1 b).2.2.2.2.2.2.2
  simp only [ht, Bool.false_eq_true, ↓reduceIte] at h
  have hfit := h.2.2.1 l hl
  change |(∑ e, c.normal b e * ((2 : ℝ) ^ p.T c.level)⁻¹ *
    (Matrix.toEuclideanLin (p.frame (c.old b))⁻¹ (gv l - p.velocity (c.old b))) e) - c.bias b| ≤ _
    at hfit
  convert hfit using 1
  congr 2
  simp only [CoverData.normalizedVelocity, CoverData.unitNormal,
    PiLp.inner_apply, PiLp.smul_apply, RCLike.inner_apply,
    conj_trivial, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit ht in
lemma CoverData.Valid.normalized_velocity_bound
    {Mp Dp : ℕ} {ℓ κ₁ δ₀ σ : ℝ} {E : Fin W → Set Incidence}
    {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (b : Fin c.n) (l : Trajectory) (hl : l ∈ c.assigned b) :
    ‖c.normalizedVelocity b l‖ ≤ 2 * p.κ := by
  have hvel := gchart_velocity (hp.chart (c.old b)) (hc.assigned_subset b hl)
  rw [hc.old_level b] at hvel
  dsimp only [CoverData.normalizedVelocity]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ((2 : ℝ) ^ p.T c.level)⁻¹)]
  calc
    _ ≤ ((2 : ℝ) ^ p.T c.level)⁻¹ * (2 * p.κ * (2 : ℝ) ^ p.T c.level) :=
      mul_le_mul_of_nonneg_left hvel (by positivity)
    _ = _ := by field_simp

end

end Submission.Obl.k4_finite_positive_mixed_cover_realization
