import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.QuadBounds
import Submission.Obl.k4_scalar_linear_critical_extremizers.Interfaces

namespace Submission.Obl.k4_scalar_angular_pair_agreement

open Set
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction

/-- A quadratic bound on a short interval extends to any containing interval, with
quadratic loss in the ratio of lengths. -/
theorem quadratic_extrapolation {g : ℝ → ℝ}
    (hg : ∃ a b c : ℝ, ∀ t, g t = a + b * t + c * t ^ 2)
    {s q₀ r q₁ E : ℝ} (hq₀ : 0 < q₀)
    (hsub : Icc s (s + q₀) ⊆ Icc r (r + q₁))
    (hbound : ∀ t ∈ Icc s (s + q₀), |g t| ≤ E)
    (t : ℝ) (ht : t ∈ Icc r (r + q₁)) :
    |g t| ≤ 48 * (q₁ / q₀) ^ 2 * E := by
  obtain ⟨a, b, c, hg⟩ := hg
  have hs : s ∈ Icc s (s + q₀) := ⟨le_rfl, by linarith⟩
  have he : s + q₀ ∈ Icc s (s + q₀) := ⟨by linarith, le_rfl⟩
  have hm : s + q₀ / 2 ∈ Icc s (s + q₀) := ⟨by linarith, by linarith⟩
  have hs' := hsub hs
  have he' := hsub he
  have hq : q₀ ≤ q₁ := by linarith [hs'.1, he'.2]
  have hq₁ : 0 < q₁ := hq₀.trans_le hq
  have hE : 0 ≤ E := (abs_nonneg _).trans (hbound s hs)
  have h₀ : |a + b * s + c * s ^ 2| ≤ E := by rw [← hg]; exact hbound s hs
  have h₁ : |a + b * (s + q₀ / 2) + c * (s + q₀ / 2) ^ 2| ≤ E := by
    rw [← hg]; exact hbound _ hm
  have h₂ : |a + b * (s + q₀) + c * (s + q₀) ^ 2| ≤ E := by
    rw [← hg]; exact hbound _ he
  have hkey := quad_three_point_bound (show 0 < q₀ / 2 by positivity)
    (show s + q₀ / 2 ≤ s + q₀ / 2 by rfl)
    (show s + q₀ / 2 + q₀ / 2 ≤ s + q₀ by linarith) h₀ h₁ h₂ t
  have hdist : |t - s| ≤ q₁ := abs_le.mpr ⟨by linarith [ht.1, he'.2], by linarith [ht.2, hs'.1]⟩
  have hR : |t - s| + (s + q₀ - s) ≤ 2 * q₁ := by linarith
  have hnum : 0 ≤ |t - s| + (s + q₀ - s) := by have := abs_nonneg (t - s); linarith
  rw [hg]
  calc
    _ ≤ 3 * E * ((|t - s| + (s + q₀ - s)) / (q₀ / 2)) ^ 2 := hkey
    _ ≤ 3 * E * ((2 * q₁) / (q₀ / 2)) ^ 2 := by gcongr
    _ = 48 * (q₁ / q₀) ^ 2 * E := by field_simp; ring

/-- An affine residual extends with linear loss in the ratio of lengths. -/
theorem affine_extrapolation {g : ℝ → ℝ}
    (hg : ∃ a b : ℝ, ∀ t, g t = a + b * t)
    {s q₀ r q₁ E : ℝ} (hq₀ : 0 < q₀)
    (hsub : Icc s (s + q₀) ⊆ Icc r (r + q₁))
    (hbound : ∀ t ∈ Icc s (s + q₀), |g t| ≤ E)
    (t : ℝ) (ht : t ∈ Icc r (r + q₁)) :
    |g t| ≤ (1 + 2 * q₁ / q₀) * E := by
  obtain ⟨a, b, hg⟩ := hg
  have hs : s ∈ Icc s (s + q₀) := ⟨le_rfl, by linarith⟩
  have he : s + q₀ ∈ Icc s (s + q₀) := ⟨by linarith, le_rfl⟩
  have hs' := hsub hs
  have he' := hsub he
  have hq : q₀ ≤ q₁ := by linarith [hs'.1, he'.2]
  have hq₁ : 0 < q₁ := hq₀.trans_le hq
  have hE : 0 ≤ E := (abs_nonneg _).trans (hbound s hs)
  have hdist : |t - s| ≤ q₁ := abs_le.mpr ⟨by linarith [ht.1, he'.2], by linarith [ht.2, hs'.1]⟩
  have hb : |b| ≤ 2 * E / q₀ := by
    apply (le_div_iff₀ hq₀).mpr
    calc
      |b| * q₀ = |b * q₀| := by rw [abs_mul, abs_of_pos hq₀]
      _ = |(a + b * (s + q₀)) - (a + b * s)| := by congr 1; ring
      _ ≤ |a + b * (s + q₀)| + |a + b * s| := abs_sub _ _
      _ ≤ 2 * E := by rw [← hg, ← hg]; linarith [hbound _ he, hbound _ hs]
  rw [hg]
  calc
    |a + b * t| = |(a + b * s) + b * (t - s)| := by congr 1; ring
    _ ≤ |a + b * s| + |b| * |t - s| := by simpa only [abs_mul] using abs_add_le (a + b * s) (b * (t - s))
    _ ≤ E + (2 * E / q₀) * q₁ := by gcongr; rw [← hg]; exact hbound s hs
    _ = (1 + 2 * q₁ / q₀) * E := by field_simp

open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- A scalar trajectory minus a quadratic predictor is quadratic in time. -/
theorem trajectory_residual_quadratic (l : ℕ × (Fin 5 → ℝ))
    (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2) :
    ∃ a b c : ℝ, ∀ t,
      x l t - MvPolynomial.eval ![t, y l t] P = a + b * t + c * t ^ 2 := by
  obtain ⟨a, b, c, hc⟩ := (isQuad2_eval P hP).line 0 1 (l.2 0) (l.2 1)
  refine ⟨l.2 2 - a, l.2 3 - b, l.2 4 - c, ?_⟩
  intro t
  have heval : MvPolynomial.eval ![t, y l t] P = a + b * t + c * t ^ 2 := by
    simpa [y, mul_comm] using hc t
  rw [heval]
  dsimp [x]
  ring

/-- Extrapolation applied to a scalar quadratic predictor residual. -/
theorem trajectory_predictor_extrapolation (l : ℕ × (Fin 5 → ℝ))
    (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    {s q₀ r q₁ E : ℝ} (hq₀ : 0 < q₀)
    (hsub : Icc s (s + q₀) ⊆ Icc r (r + q₁))
    (hbound : ∀ t ∈ Icc s (s + q₀),
      |x l t - MvPolynomial.eval ![t, y l t] P| ≤ E)
    (t : ℝ) (ht : t ∈ Icc r (r + q₁)) :
    |x l t - MvPolynomial.eval ![t, y l t] P| ≤ 48 * (q₁ / q₀) ^ 2 * E :=
  quadratic_extrapolation (trajectory_residual_quadratic l P hP) hq₀ hsub hbound t ht

/-- Extrapolation applied to the affine transverse trajectory residual. -/
theorem trajectory_affine_extrapolation (l : ℕ × (Fin 5 → ℝ)) (u v : ℝ)
    {s q₀ r q₁ E : ℝ} (hq₀ : 0 < q₀)
    (hsub : Icc s (s + q₀) ⊆ Icc r (r + q₁))
    (hbound : ∀ t ∈ Icc s (s + q₀), |y l t - u - t * v| ≤ E)
    (t : ℝ) (ht : t ∈ Icc r (r + q₁)) :
    |y l t - u - t * v| ≤ (1 + 2 * q₁ / q₀) * E := by
  apply affine_extrapolation (g := fun t => y l t - u - t * v) _ hq₀ hsub hbound t ht
  exact ⟨l.2 0 - u, l.2 1 - v, fun t => by dsimp [y]; ring⟩

end Submission.Obl.k4_scalar_angular_pair_agreement
