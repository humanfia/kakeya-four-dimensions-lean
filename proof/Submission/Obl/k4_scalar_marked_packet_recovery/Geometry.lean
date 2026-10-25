import Mathlib
import Submission.Obl.k4_quadratic_selector_sweep.SignFibers

/-!
# Geometric part of the marked packet recovery

A noisy packet fits the trajectories of the jittered rounded coefficients `b₀ j + a`.
A common jitter `a` shifts every such trajectory by the same affine/quadratic profile, so it is
absorbed exactly into the centers and into the predictor:
`P'(t, y) = P(t, y + a₀ + t a₁) - (a₂ + t a₃ + t² a₄)`.
The remaining rounding error `|b - b₀| ≤ δ` is controlled by a three-point derivative bound for
the quadratic `y ↦ P(t, y)` on the packet strip.
-/

namespace Submission.Obl.k4_scalar_marked_packet_recovery

open MvPolynomial Filter

noncomputable section

/-- For fixed `t`, a polynomial of total degree at most two is a quadratic in `y`. -/
theorem eval_quadratic_rep (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2) (t : ℝ) :
    ∃ A₀ A₁ A₂ : ℝ, ∀ y : ℝ, eval ![t, y] P = A₀ + A₁ * y + A₂ * y ^ 2 := by
  classical
  refine ⟨∑ d ∈ P.support, if d 1 = 0 then P.coeff d * t ^ d 0 else 0,
    ∑ d ∈ P.support, if d 1 = 1 then P.coeff d * t ^ d 0 else 0,
    ∑ d ∈ P.support, if d 1 = 2 then P.coeff d * t ^ d 0 else 0, fun y => ?_⟩
  rw [eval_eq', Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d 0 + d 1 ≤ 2 := by
    have h := le_totalDegree hd
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at h
    omega
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h3 : d 1 = 0 ∨ d 1 = 1 ∨ d 1 = 2 := by omega
  rcases h3 with h | h | h <;> simp [h] <;> ring

/-- Three-point derivative bound for a quadratic which is bounded by `B` on `[c - β, c + β]`. -/
theorem quadratic_diff_le (A₀ A₁ A₂ c β B R y₁ y₂ : ℝ) (hβ : 0 < β)
    (hB : ∀ w ∈ Set.Icc (-1 : ℝ) 1, |A₀ + A₁ * (c + β * w) + A₂ * (c + β * w) ^ 2| ≤ B)
    (h₁ : |y₁ - c| ≤ R * β) (h₂ : |y₂ - c| ≤ R * β) :
    |(A₀ + A₁ * y₁ + A₂ * y₁ ^ 2) - (A₀ + A₁ * y₂ + A₂ * y₂ ^ 2)|
      ≤ |y₁ - y₂| * (B * (1 + 4 * R) / β) := by
  have hp := hB 1 ⟨by norm_num, le_rfl⟩
  have hm := hB (-1) ⟨le_rfl, by norm_num⟩
  have h0 := hB 0 ⟨by norm_num, by norm_num⟩
  set gp := A₀ + A₁ * (c + β * 1) + A₂ * (c + β * 1) ^ 2 with hgp
  set gm := A₀ + A₁ * (c + β * (-1)) + A₂ * (c + β * (-1)) ^ 2 with hgm
  set g0 := A₀ + A₁ * (c + β * 0) + A₂ * (c + β * 0) ^ 2 with hg0
  have hβ' : β ≠ 0 := hβ.ne'
  have key : (A₀ + A₁ * y₁ + A₂ * y₁ ^ 2) - (A₀ + A₁ * y₂ + A₂ * y₂ ^ 2)
      = (y₁ - y₂) * ((gp - gm) / (2 * β)
          + (gp + gm - 2 * g0) / (2 * β ^ 2) * (y₁ + y₂ - 2 * c)) := by
    rw [hgp, hgm, hg0]
    field_simp
    ring
  rw [key, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) h0
  have hsum : |y₁ + y₂ - 2 * c| ≤ 2 * R * β := by
    calc |y₁ + y₂ - 2 * c| = |(y₁ - c) + (y₂ - c)| := by ring_nf
      _ ≤ |y₁ - c| + |y₂ - c| := abs_add_le _ _
      _ ≤ R * β + R * β := add_le_add h₁ h₂
      _ = 2 * R * β := by ring
  have hd1 : |gp - gm| ≤ 2 * B := by
    calc |gp - gm| ≤ |gp| + |gm| := abs_sub _ _
      _ ≤ B + B := add_le_add hp hm
      _ = 2 * B := by ring
  have hd2 : |gp + gm - 2 * g0| ≤ 4 * B := by
    calc |gp + gm - 2 * g0| ≤ |gp| + |gm| + |2 * g0| := by
          calc |gp + gm - 2 * g0| ≤ |gp + gm| + |2 * g0| := abs_sub _ _
            _ ≤ |gp| + |gm| + |2 * g0| := by gcongr; exact abs_add_le _ _
      _ = |gp| + |gm| + 2 * |g0| := by rw [abs_mul]; norm_num
      _ ≤ B + B + 2 * B := by gcongr
      _ = 4 * B := by ring
  have h2β : 0 < 2 * β := by positivity
  have h2β2 : 0 < 2 * β ^ 2 := by positivity
  calc |(gp - gm) / (2 * β) + (gp + gm - 2 * g0) / (2 * β ^ 2) * (y₁ + y₂ - 2 * c)|
      ≤ |(gp - gm) / (2 * β)| + |(gp + gm - 2 * g0) / (2 * β ^ 2)| * |y₁ + y₂ - 2 * c| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ = |gp - gm| / (2 * β) + |gp + gm - 2 * g0| / (2 * β ^ 2) * |y₁ + y₂ - 2 * c| := by
        rw [abs_div, abs_div, abs_of_pos h2β, abs_of_pos h2β2]
    _ ≤ (2 * B) / (2 * β) + (4 * B) / (2 * β ^ 2) * (2 * R * β) := by
        gcongr
    _ = B * (1 + 4 * R) / β := by
        field_simp

/-- The predictor `P(t, y + a₀ + t a₁) - (a₂ + t a₃ + t² a₄)` which absorbs a common jitter `a`. -/
def shiftPoly (a : Fin 5 → ℝ) (P : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 2) ℝ :=
  bind₁ ![X 0, X 1 + C (a 0) + X 0 * C (a 1)] P - (C (a 2) + X 0 * C (a 3) + X 0 ^ 2 * C (a 4))

theorem eval_shiftPoly (a : Fin 5 → ℝ) (P : MvPolynomial (Fin 2) ℝ) (t y : ℝ) :
    eval ![t, y] (shiftPoly a P)
      = eval ![t, y + a 0 + t * a 1] P - (a 2 + t * a 3 + t ^ 2 * a 4) := by
  have hb : eval ![t, y] (bind₁ ![X 0, X 1 + C (a 0) + X 0 * C (a 1)] P)
      = eval ![t, y + a 0 + t * a 1] P := by
    change eval₂Hom (RingHom.id ℝ) ![t, y] (bind₁ ![X 0, X 1 + C (a 0) + X 0 * C (a 1)] P) = _
    rw [eval₂Hom_bind₁]
    change eval₂Hom (RingHom.id ℝ) _ P = eval₂Hom (RingHom.id ℝ) _ P
    congr 2
    funext i
    fin_cases i <;> simp
  simp only [shiftPoly, map_sub, hb, map_add, map_mul, map_pow, eval_X, eval_C]
  simp

theorem totalDegree_shiftPoly (a : Fin 5 → ℝ) (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) : (shiftPoly a P).totalDegree ≤ 2 := by
  have hv : ∀ i, (![X 0, X 1 + C (a 0) + X 0 * C (a 1)] i : MvPolynomial (Fin 2) ℝ).totalDegree
      ≤ 1 := by
    intro i
    fin_cases i
    · simp
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      refine (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans
        (max_le (by simp) (by simp))) ?_)
      exact (totalDegree_mul _ _).trans (by simp)
  have h1 := (k4_quadratic_selector_sweep.totalDegree_bind_affine _ hv P).trans hP
  have h2 : (C (a 2) + X 0 * C (a 3) + X 0 ^ 2 * C (a 4) : MvPolynomial (Fin 2) ℝ).totalDegree
      ≤ 2 := by
    refine (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans
      (max_le (by simp) ?_)) ?_)
    · exact (totalDegree_mul _ _).trans (by simp)
    · refine (totalDegree_mul _ _).trans ?_
      refine (add_le_add (totalDegree_pow _ _) le_rfl).trans ?_
      simp
  exact (totalDegree_sub _ _).trans (max_le h1 h2)

/-- The unrounding error budget: with `σ / Nη ≤ β` and `21 δ Nη³ ≤ σ Ns`, the rounding error `3δ`
and the predictor sensitivity over a `2δ` displacement fit under `Ns`. -/
theorem unrounding_budget {Nη Ns σ δ β : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hNη : 1 ≤ Nη)
    (hβ : σ / Nη ≤ β) (hδ : 0 ≤ δ) (h3 : 21 * δ * Nη * Nη * Nη ≤ σ * Ns) :
    3 * δ + 2 * δ * (Nη * (1 + 4 * (Nη + 1)) / β) ≤ Ns := by
  have hNη0 : 0 < Nη := by linarith
  have hβ0 : 0 < β := lt_of_lt_of_le (div_pos hσ0 hNη0) hβ
  have hinv : 1 / β ≤ Nη / σ := by
    have := one_div_le_one_div_of_le (div_pos hσ0 hNη0) hβ
    rwa [one_div_div] at this
  have hA : 0 ≤ Nη * (1 + 4 * (Nη + 1)) := by positivity
  have hle : Nη * (1 + 4 * (Nη + 1)) / β ≤ Nη * (1 + 4 * (Nη + 1)) * (Nη / σ) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hinv hA
  have hmain : 3 * δ + 2 * δ * (Nη * (1 + 4 * (Nη + 1)) * (Nη / σ)) ≤ Ns := by
    have e : 3 * δ + 2 * δ * (Nη * (1 + 4 * (Nη + 1)) * (Nη / σ))
        = (3 * δ * σ + 2 * δ * (Nη * (1 + 4 * (Nη + 1)) * Nη)) / σ := by
      field_simp
    rw [e, div_le_iff₀ hσ0]
    have hN3 : 1 ≤ Nη * Nη * Nη := by
      have := mul_le_mul hNη hNη zero_le_one hNη0.le
      nlinarith
    have k1 : δ * σ ≤ δ * (Nη * Nη * Nη) := mul_le_mul_of_nonneg_left (by linarith) hδ
    have k2 : δ * (Nη * Nη) ≤ δ * (Nη * Nη * Nη) := by
      apply mul_le_mul_of_nonneg_left _ hδ
      nlinarith
    nlinarith
  calc 3 * δ + 2 * δ * (Nη * (1 + 4 * (Nη + 1)) / β)
      ≤ 3 * δ + 2 * δ * (Nη * (1 + 4 * (Nη + 1)) * (Nη / σ)) := by
        have : 0 ≤ 2 * δ := by positivity
        gcongr
    _ ≤ Ns := hmain

/-- One noisy packet gives one original packet. The common jitter `a` is absorbed into the
centers `u - a 0`, `v - a 1` and into the predictor `shiftPoly a P`; an original coefficient
vector `b` within `δ` of a rounded vector `b₀` whose jittered trajectory `b₀ + a` satisfies the
noisy fits satisfies the original fits with the larger loss `Nε`. -/
theorem geometry_transfer {Nη Nε Ns σ δ β t₀ q u v : ℝ} {P : MvPolynomial (Fin 2) ℝ}
    {a : Fin 5 → ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (ha : ∀ e, 0 ≤ a e ∧ a e ≤ σ)
    (hβ : σ / Nη ≤ β) (ht₀ : 0 ≤ t₀) (hq : t₀ + q ≤ 1)
    (hNη : 1 ≤ Nη) (hNs : 0 ≤ Ns)
    (h1 : Nη + 3 ≤ Nε) (h2 : 2 * δ * Nη ≤ σ) (h3 : 21 * δ * Nη * Nη * Nη ≤ σ * Ns)
    (huv : |u| + |v| ≤ Nη) (hdeg : P.totalDegree ≤ 2)
    (hstrip : ∀ t ∈ Set.Icc t₀ (t₀ + q), ∀ w ∈ Set.Icc (-1 : ℝ) 1,
      |eval ![t, u + t * v + β * w] P| ≤ Nη) :
    |u - a 0| + |v - a 1| ≤ Nε ∧ (shiftPoly a P).totalDegree ≤ 2 ∧
    (∀ t ∈ Set.Icc t₀ (t₀ + q), ∀ w ∈ Set.Icc (-1 : ℝ) 1,
      |eval ![t, (u - a 0) + t * (v - a 1) + β * w] (shiftPoly a P)| ≤ Nε) ∧
    ∀ (b₀ b : Fin 5 → ℝ), (∀ e, |b e - b₀ e| ≤ δ) → ∀ t ∈ Set.Icc t₀ (t₀ + q),
      |(b₀ + a) 0 + t * (b₀ + a) 1 - u - t * v| ≤ Nη * β →
      |(b₀ + a) 2 + t * (b₀ + a) 3 + t ^ 2 * (b₀ + a) 4
          - eval ![t, (b₀ + a) 0 + t * (b₀ + a) 1] P| ≤ Nη * Ns →
      |b 0 + t * b 1 - (u - a 0) - t * (v - a 1)| ≤ Nε * β ∧
      |b 2 + t * b 3 + t ^ 2 * b 4 - eval ![t, b 0 + t * b 1] (shiftPoly a P)| ≤ Nε * Ns := by
  have hNη0 : 0 < Nη := by linarith
  have hβ0 : 0 < β := lt_of_lt_of_le (div_pos hσ0 hNη0) hβ
  have hσβ : σ ≤ Nη * β := by
    have := (div_le_iff₀ hNη0).1 hβ
    linarith [mul_comm β Nη]
  have ha1 : ∀ e, 0 ≤ a e ∧ a e ≤ 1 := fun e => ⟨(ha e).1, (ha e).2.trans hσ1⟩
  refine ⟨?_, totalDegree_shiftPoly a P hdeg, ?_, ?_⟩
  · have e0 := ha1 0
    have e1 := ha1 1
    calc |u - a 0| + |v - a 1| ≤ (|u| + |a 0|) + (|v| + |a 1|) :=
          add_le_add (abs_sub _ _) (abs_sub _ _)
      _ = (|u| + a 0) + (|v| + a 1) := by
          rw [abs_of_nonneg e0.1, abs_of_nonneg e1.1]
      _ ≤ Nε := by linarith
  · intro t ht w hw
    have ht0 : 0 ≤ t := le_trans ht₀ ht.1
    have ht1 : t ≤ 1 := by linarith [ht.2]
    rw [eval_shiftPoly]
    have e : (u - a 0) + t * (v - a 1) + β * w + a 0 + t * a 1 = u + t * v + β * w := by ring
    rw [e]
    have hs := hstrip t ht w hw
    have e2 := ha1 2
    have e3 := ha1 3
    have e4 := ha1 4
    have hta3 : t * a 3 ≤ 1 := by
      calc t * a 3 ≤ 1 * 1 := mul_le_mul ht1 e3.2 e3.1 zero_le_one
        _ = 1 := one_mul 1
    have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ ht0 ht1
    have hta4 : t ^ 2 * a 4 ≤ 1 := by
      calc t ^ 2 * a 4 ≤ 1 * 1 := mul_le_mul ht2 e4.2 e4.1 zero_le_one
        _ = 1 := one_mul 1
    have hnn : 0 ≤ a 2 + t * a 3 + t ^ 2 * a 4 := by
      have := mul_nonneg ht0 e3.1
      have := mul_nonneg (sq_nonneg t) e4.1
      linarith
    have hshift : |a 2 + t * a 3 + t ^ 2 * a 4| ≤ 3 := by
      rw [abs_of_nonneg hnn]
      linarith
    calc |eval ![t, u + t * v + β * w] P - (a 2 + t * a 3 + t ^ 2 * a 4)|
        ≤ |eval ![t, u + t * v + β * w] P| + |a 2 + t * a 3 + t ^ 2 * a 4| := abs_sub _ _
      _ ≤ Nη + 3 := add_le_add hs hshift
      _ ≤ Nε := h1
  · intro b₀ b hround t ht hy hx
    have ht0 : 0 ≤ t := le_trans ht₀ ht.1
    have ht1 : t ≤ 1 := by linarith [ht.2]
    have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) (hround 0)
    have h2δ : 2 * δ ≤ β := by
      have : 2 * δ * Nη ≤ β * Nη := by linarith
      exact le_of_mul_le_mul_right this hNη0
    set Y₁ := (b₀ + a) 0 + t * (b₀ + a) 1 with hY₁
    set Y₂ := b 0 + t * b 1 + a 0 + t * a 1 with hY₂
    have hY : |Y₂ - Y₁| ≤ 2 * δ := by
      have e : Y₂ - Y₁ = (b 0 - b₀ 0) + t * (b 1 - b₀ 1) := by
        rw [hY₁, hY₂]
        simp only [Pi.add_apply]
        ring
      rw [e]
      calc |(b 0 - b₀ 0) + t * (b 1 - b₀ 1)| ≤ |b 0 - b₀ 0| + |t * (b 1 - b₀ 1)| :=
            abs_add_le _ _
        _ = |b 0 - b₀ 0| + |t| * |b 1 - b₀ 1| := by rw [abs_mul]
        _ ≤ δ + 1 * δ := by
            gcongr
            · exact hround 0
            · rw [abs_of_nonneg ht0]; exact ht1
            · exact hround 1
        _ = 2 * δ := by ring
    have hyfit : |Y₂ - u - t * v| ≤ (Nη + 1) * β := by
      calc |Y₂ - u - t * v| = |(Y₂ - Y₁) + (Y₁ - u - t * v)| := by ring_nf
        _ ≤ |Y₂ - Y₁| + |Y₁ - u - t * v| := abs_add_le _ _
        _ ≤ 2 * δ + Nη * β := add_le_add hY hy
        _ ≤ (Nη + 1) * β := by linarith
    refine ⟨?_, ?_⟩
    · have e : b 0 + t * b 1 - (u - a 0) - t * (v - a 1) = Y₂ - u - t * v := by
        rw [hY₂]; ring
      rw [e]
      calc |Y₂ - u - t * v| ≤ (Nη + 1) * β := hyfit
        _ ≤ Nε * β := by
            apply mul_le_mul_of_nonneg_right _ hβ0.le
            linarith
    · rw [eval_shiftPoly]
      obtain ⟨A₀, A₁, A₂, hrep⟩ := eval_quadratic_rep P hdeg t
      have hBstrip : ∀ w ∈ Set.Icc (-1 : ℝ) 1,
          |A₀ + A₁ * ((u + t * v) + β * w) + A₂ * ((u + t * v) + β * w) ^ 2| ≤ Nη := by
        intro w hw
        rw [← hrep]
        exact hstrip t ht w hw
      have hc1 : |Y₁ - (u + t * v)| ≤ (Nη + 1) * β := by
        have : Y₁ - (u + t * v) = Y₁ - u - t * v := by ring
        rw [this]
        linarith
      have hc2 : |Y₂ - (u + t * v)| ≤ (Nη + 1) * β := by
        have : Y₂ - (u + t * v) = Y₂ - u - t * v := by ring
        rw [this]
        exact hyfit
      have hquad := quadratic_diff_le A₀ A₁ A₂ (u + t * v) β Nη (Nη + 1) Y₁ Y₂ hβ0 hBstrip hc1 hc2
      rw [← hrep, ← hrep] at hquad
      have e2 : b 2 + t * b 3 + t ^ 2 * b 4
            - (eval ![t, b 0 + t * b 1 + a 0 + t * a 1] P - (a 2 + t * a 3 + t ^ 2 * a 4))
          = ((b 2 - b₀ 2) + t * (b 3 - b₀ 3) + t ^ 2 * (b 4 - b₀ 4))
            + ((b₀ + a) 2 + t * (b₀ + a) 3 + t ^ 2 * (b₀ + a) 4 - eval ![t, Y₁] P)
            + (eval ![t, Y₁] P - eval ![t, Y₂] P) := by
        rw [hY₂]
        simp only [Pi.add_apply]
        ring
      rw [e2]
      have hfirst : |(b 2 - b₀ 2) + t * (b 3 - b₀ 3) + t ^ 2 * (b 4 - b₀ 4)| ≤ 3 * δ := by
        have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ ht0 ht1
        calc |(b 2 - b₀ 2) + t * (b 3 - b₀ 3) + t ^ 2 * (b 4 - b₀ 4)|
            ≤ |b 2 - b₀ 2| + |t * (b 3 - b₀ 3)| + |t ^ 2 * (b 4 - b₀ 4)| := abs_add_three _ _ _
          _ = |b 2 - b₀ 2| + |t| * |b 3 - b₀ 3| + |t ^ 2| * |b 4 - b₀ 4| := by
              rw [abs_mul, abs_mul]
          _ ≤ δ + 1 * δ + 1 * δ := by
              gcongr
              · exact hround 2
              · rw [abs_of_nonneg ht0]; exact ht1
              · exact hround 3
              · rw [abs_of_nonneg (sq_nonneg t)]; exact ht2
              · exact hround 4
          _ = 3 * δ := by ring
      have hfac : 0 ≤ Nη * (1 + 4 * (Nη + 1)) / β := by positivity
      have hthird : |eval ![t, Y₁] P - eval ![t, Y₂] P|
          ≤ 2 * δ * (Nη * (1 + 4 * (Nη + 1)) / β) := by
        calc |eval ![t, Y₁] P - eval ![t, Y₂] P|
            ≤ |Y₁ - Y₂| * (Nη * (1 + 4 * (Nη + 1)) / β) := hquad
          _ ≤ 2 * δ * (Nη * (1 + 4 * (Nη + 1)) / β) := by
              apply mul_le_mul_of_nonneg_right _ hfac
              rw [abs_sub_comm]
              exact hY
      have hkey := unrounding_budget hσ0 hσ1 hNη hβ hδ0 h3
      have hgap : Ns ≤ (Nε - Nη) * Ns := by
        have : 1 ≤ Nε - Nη := by linarith
        nlinarith
      calc |((b 2 - b₀ 2) + t * (b 3 - b₀ 3) + t ^ 2 * (b 4 - b₀ 4))
            + ((b₀ + a) 2 + t * (b₀ + a) 3 + t ^ 2 * (b₀ + a) 4 - eval ![t, Y₁] P)
            + (eval ![t, Y₁] P - eval ![t, Y₂] P)|
          ≤ |(b 2 - b₀ 2) + t * (b 3 - b₀ 3) + t ^ 2 * (b 4 - b₀ 4)|
            + |(b₀ + a) 2 + t * (b₀ + a) 3 + t ^ 2 * (b₀ + a) 4 - eval ![t, Y₁] P|
            + |eval ![t, Y₁] P - eval ![t, Y₂] P| := abs_add_three _ _ _
        _ ≤ 3 * δ + Nη * Ns + 2 * δ * (Nη * (1 + 4 * (Nη + 1)) / β) := by
            gcongr
        _ ≤ Nε * Ns := by nlinarith

/-- Elementary size facts at a base `N ≥ 2`. -/
theorem base_facts {N s m η : ℝ} (hN : 2 ≤ N) (hs : 0 < s) (hsm : s < m) (hη : 0 ≤ η) :
    1 ≤ N ^ η ∧ 0 < N ^ (-m) ∧ N ^ (-m) ≤ 1 ∧ 0 ≤ N ^ (-s) := by
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  refine ⟨Real.one_le_rpow hN1 hη, Real.rpow_pos_of_pos hN0 _, ?_, Real.rpow_nonneg hN0.le _⟩
  exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)

/-- The explicit conditions of `geometry_transfer` hold for all large `k`, when the input loss `η`
is below the output loss `ε` and at most one. -/
theorem eventually_geometry_conditions (N : ℕ → ℝ) (hN2 : ∀ k, 2 ≤ N k)
    (hNt : Tendsto N atTop atTop) {s m ε η : ℝ} (hs : 0 < s) (hsm : s < m)
    (hη : 0 < η) (hηε : η < ε) (hη1 : η ≤ 1) :
    ∀ᶠ k in atTop, N k ^ η + 3 ≤ N k ^ ε ∧
      2 * N k ^ (-10 * (m + s + 1)) * N k ^ η ≤ N k ^ (-m) ∧
      21 * N k ^ (-10 * (m + s + 1)) * N k ^ η * N k ^ η * N k ^ η
        ≤ N k ^ (-m) * N k ^ (-s) := by
  have hpow : ∀ a : ℝ, 0 < a → ∀ C : ℝ, ∀ᶠ k in atTop, C ≤ N k ^ a := fun a ha C =>
    ((tendsto_rpow_atTop ha).comp hNt).eventually (eventually_ge_atTop C)
  filter_upwards [hpow (ε - η) (by linarith) 4, hpow (9 * m + 10 * s + 10 - η) (by linarith) 2,
    hpow (9 * m + 9 * s + 10 - 3 * η) (by linarith) 21] with k hk1 hk2 hk3
  have hx : 0 < N k := by linarith [hN2 k]
  obtain ⟨hη1', hm0, -, hs0⟩ := base_facts (hN2 k) hs hsm hη.le
  refine ⟨?_, ?_, ?_⟩
  · have e : N k ^ ε = N k ^ (ε - η) * N k ^ η := by
      rw [← Real.rpow_add hx, sub_add_cancel]
    rw [e]
    nlinarith
  · have e : N k ^ (-10 * (m + s + 1)) * N k ^ η
        = N k ^ (-m) * N k ^ (-(9 * m + 10 * s + 10 - η)) := by
      rw [← Real.rpow_add hx, ← Real.rpow_add hx]
      congr 1
      ring
    have hinv : N k ^ (-(9 * m + 10 * s + 10 - η)) ≤ 2⁻¹ := by
      rw [Real.rpow_neg hx.le]
      exact inv_anti₀ (by norm_num) hk2
    rw [mul_assoc, e]
    nlinarith
  · have e : N k ^ (-10 * (m + s + 1)) * N k ^ η * N k ^ η * N k ^ η
        = N k ^ (-m) * N k ^ (-s) * N k ^ (-(9 * m + 9 * s + 10 - 3 * η)) := by
      rw [← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_add hx,
        ← Real.rpow_add hx]
      congr 1
      ring
    have hinv : N k ^ (-(9 * m + 9 * s + 10 - 3 * η)) ≤ 21⁻¹ := by
      rw [Real.rpow_neg hx.le]
      exact inv_anti₀ (by norm_num) hk3
    have hms : 0 ≤ N k ^ (-m) * N k ^ (-s) := by positivity
    rw [mul_assoc, mul_assoc, mul_assoc, ← mul_assoc (N k ^ (-10 * (m + s + 1))),
      ← mul_assoc (N k ^ (-10 * (m + s + 1)) * N k ^ η), e]
    nlinarith

end

end Submission.Obl.k4_scalar_marked_packet_recovery
