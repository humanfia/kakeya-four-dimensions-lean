import Mathlib
import Submission.Obl.k4_scalar_angular_pair_agreement.Dyadic
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.QuadBounds

/-!
# Extrapolation of chart fits from a fine block to its coarse block

A chart fit holds on a fine dyadic block `I T j` of length `2⁻ᵀ`.  Along a trajectory
the spatial residual is affine and the scalar residual quadratic in time, so both extend
to the coarse block `I T₁ b ⊇ I T j` with losses `1 + 2R` and `48 R²`, `R = 2 ^ (T - T₁)`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_angular_pair_agreement

open MeasureTheory Set
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction

/-- Quadratic extrapolation from a subinterval. -/
lemma quad_extrap {a b c s q0 s' q1 E : ℝ} (hq0 : 0 < q0) (hs : s' ≤ s)
    (hs1 : s + q0 ≤ s' + q1)
    (hE : ∀ t ∈ Icc s (s + q0), |a + b * t + c * t ^ 2| ≤ E) :
    ∀ t ∈ Icc s' (s' + q1), |a + b * t + c * t ^ 2| ≤ 48 * (q1 / q0) ^ 2 * E := by
  intro t ht
  have hE0 : 0 ≤ E := le_trans (abs_nonneg _) (hE s ⟨le_rfl, by linarith⟩)
  have hδ : 0 < q0 / 2 := by linarith
  have h := quad_three_point_bound (a := a) (b := b) (c := c) (A := E) hδ
    (x₁ := s) (x₂ := s + q0 / 2) (x₃ := s + q0) (by linarith) (by linarith)
    (hE s ⟨le_rfl, by linarith⟩) (hE _ ⟨by linarith, by linarith⟩)
    (hE _ ⟨by linarith, le_rfl⟩) t
  have hq01 : q0 ≤ q1 := by linarith
  have hts : |t - s| ≤ q1 := by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hratio : (|t - s| + (s + q0 - s)) / (q0 / 2) ≤ 4 * (q1 / q0) := by
    rw [div_le_iff₀ hδ]
    have : 4 * (q1 / q0) * (q0 / 2) = 2 * q1 := by field_simp; ring
    rw [this]; linarith
  have hnn : 0 ≤ (|t - s| + (s + q0 - s)) / (q0 / 2) := by
    apply div_nonneg _ hδ.le; have := abs_nonneg (t - s); linarith
  calc |a + b * t + c * t ^ 2| ≤ 3 * E * ((|t - s| + (s + q0 - s)) / (q0 / 2)) ^ 2 := h
    _ ≤ 3 * E * (4 * (q1 / q0)) ^ 2 := by gcongr
    _ = 48 * (q1 / q0) ^ 2 * E := by ring

/-- Affine extrapolation from a subinterval. -/
lemma affine_extrap {a b s q0 s' q1 E : ℝ} (hq0 : 0 < q0) (hs : s' ≤ s)
    (hs1 : s + q0 ≤ s' + q1)
    (hE : ∀ t ∈ Icc s (s + q0), |a + b * t| ≤ E) :
    ∀ t ∈ Icc s' (s' + q1), |a + b * t| ≤ (1 + 2 * (q1 / q0)) * E := by
  intro t ht
  have h0 := hE s ⟨le_rfl, by linarith⟩
  have h1 := hE (s + q0) ⟨by linarith, le_rfl⟩
  have hE0 : 0 ≤ E := le_trans (abs_nonneg _) h0
  have hb : |b| * q0 ≤ 2 * E := by
    have : b * q0 = (a + b * (s + q0)) - (a + b * s) := by ring
    rw [← abs_of_pos hq0, ← abs_mul, this]
    calc |(a + b * (s + q0)) - (a + b * s)| ≤ |a + b * (s + q0)| + |a + b * s| :=
          abs_sub _ _
      _ ≤ 2 * E := by linarith
  have hts : |t - s| ≤ q1 := by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hb' : |b| ≤ 2 * E / q0 := by rw [le_div_iff₀ hq0]; exact hb
  calc |a + b * t| = |(a + b * s) + b * (t - s)| := by ring_nf
    _ ≤ |a + b * s| + |b| * |t - s| := by rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ E + (2 * E / q0) * q1 := by gcongr
    _ = (1 + 2 * (q1 / q0)) * E := by field_simp

/-- The length ratio of a fine and a coarse dyadic block. -/
lemma ratio_eq {T T₁ : ℕ} (h : T₁ ≤ T) :
    ((2 : ℝ) ^ T₁)⁻¹ / ((2 : ℝ) ^ T)⁻¹ = (2 : ℝ) ^ (T - T₁) := by
  rw [two_pow_split h]
  have : (0 : ℝ) < (2 : ℝ) ^ T₁ := by positivity
  have : (0 : ℝ) < (2 : ℝ) ^ (T - T₁) := by positivity
  field_simp

lemma I_eq_Icc (T : ℕ) (j : Fin (2 ^ T)) :
    I T j = Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T)
      (((j : ℕ) : ℝ) / (2 : ℝ) ^ T + ((2 : ℝ) ^ T)⁻¹) := by
  unfold I; congr 1; rw [add_div, one_div]

/-- Quadratic extrapolation from a fine block to a coarse block containing it. -/
lemma quad_extrap_block {T T₁ : ℕ} (h : T₁ ≤ T) {jj : Fin (2 ^ T)} {b : Fin (2 ^ T₁)}
    (hsub : I T jj ⊆ I T₁ b) {g : ℝ → ℝ}
    (hg : ∃ a b' c : ℝ, ∀ t, g t = a + b' * t + c * t ^ 2) {E : ℝ}
    (hE : ∀ t ∈ I T jj, |g t| ≤ E) :
    ∀ t ∈ I T₁ b, |g t| ≤ 48 * ((2 : ℝ) ^ (T - T₁)) ^ 2 * E := by
  obtain ⟨a, b', c, hg⟩ := hg
  have hsub' := hsub
  rw [I_eq_Icc, I_eq_Icc] at hsub'
  have hne : ((jj : ℕ) : ℝ) / (2 : ℝ) ^ T ≤ ((jj : ℕ) : ℝ) / (2 : ℝ) ^ T + ((2 : ℝ) ^ T)⁻¹ := by
    have : (0 : ℝ) ≤ ((2 : ℝ) ^ T)⁻¹ := by positivity
    linarith
  rw [Set.Icc_subset_Icc_iff hne] at hsub'
  intro t ht
  rw [I_eq_Icc] at ht
  have key := quad_extrap (a := a) (b := b') (c := c) (by positivity) hsub'.1 hsub'.2
    (E := E) (fun t' ht' => by rw [← hg]; exact hE t' (by rw [I_eq_Icc]; exact ht')) t ht
  rw [hg, ← ratio_eq h]
  exact key

/-- Affine extrapolation from a fine block to a coarse block containing it. -/
lemma affine_extrap_block {T T₁ : ℕ} (h : T₁ ≤ T) {jj : Fin (2 ^ T)} {b : Fin (2 ^ T₁)}
    (hsub : I T jj ⊆ I T₁ b) {g : ℝ → ℝ}
    (hg : ∃ a b' : ℝ, ∀ t, g t = a + b' * t) {E : ℝ}
    (hE : ∀ t ∈ I T jj, |g t| ≤ E) :
    ∀ t ∈ I T₁ b, |g t| ≤ (1 + 2 * (2 : ℝ) ^ (T - T₁)) * E := by
  obtain ⟨a, b', hg⟩ := hg
  have hsub' := hsub
  rw [I_eq_Icc, I_eq_Icc] at hsub'
  have hne : ((jj : ℕ) : ℝ) / (2 : ℝ) ^ T ≤ ((jj : ℕ) : ℝ) / (2 : ℝ) ^ T + ((2 : ℝ) ^ T)⁻¹ := by
    have : (0 : ℝ) ≤ ((2 : ℝ) ^ T)⁻¹ := by positivity
    linarith
  rw [Set.Icc_subset_Icc_iff hne] at hsub'
  intro t ht
  rw [I_eq_Icc] at ht
  have key := affine_extrap (a := a) (b := b') (by positivity) hsub'.1 hsub'.2
    (E := E) (fun t' ht' => by rw [← hg]; exact hE t' (by rw [I_eq_Icc]; exact ht')) t ht
  rw [hg, ← ratio_eq h]
  exact key

/-- Along a trajectory the spatial residual of a chart is affine in time. -/
lemma y_residual_affine (l : ℕ × (Fin 5 → ℝ)) (u v : ℝ) :
    ∃ a b' : ℝ, ∀ t, y l t - u - t * v = a + b' * t :=
  ⟨l.2 0 - u, l.2 1 - v, fun t => by simp only [y]; ring⟩

/-- Along a trajectory the scalar residual of a quadratic predictor is quadratic in time. -/
lemma x_residual_quad (l : ℕ × (Fin 5 → ℝ)) (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) :
    ∃ a b' c : ℝ, ∀ t, x l t - MvPolynomial.eval ![t, y l t] P = a + b' * t + c * t ^ 2 := by
  obtain ⟨k, hk⟩ := isQuad2_eval P hP
  refine ⟨l.2 2 - (k 0 + k 2 * l.2 0 + k 5 * l.2 0 ^ 2),
    l.2 3 - (k 1 + k 2 * l.2 1 + k 4 * l.2 0 + 2 * k 5 * l.2 0 * l.2 1),
    l.2 4 - (k 3 + k 4 * l.2 1 + k 5 * l.2 1 ^ 2), fun t => ?_⟩
  have := hk t (y l t)
  simp only at this
  rw [this]
  simp only [x, y]
  ring

/-- Along a trajectory the difference of two quadratic predictors is quadratic in time. -/
lemma diff_along_line_quad (l : ℕ × (Fin 5 → ℝ)) (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) :
    ∃ a b' c : ℝ, ∀ t, MvPolynomial.eval ![t, y l t] P = a + b' * t + c * t ^ 2 := by
  obtain ⟨k, hk⟩ := isQuad2_eval P hP
  refine ⟨k 0 + k 2 * l.2 0 + k 5 * l.2 0 ^ 2,
    k 1 + k 2 * l.2 1 + k 4 * l.2 0 + 2 * k 5 * l.2 0 * l.2 1,
    k 3 + k 4 * l.2 1 + k 5 * l.2 1 ^ 2, fun t => ?_⟩
  have := hk t (y l t)
  simp only at this
  rw [this]
  simp only [y]
  ring

end Submission.Obl.k4_scalar_angular_pair_agreement
