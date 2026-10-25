import Mathlib

/-!
# Whole-block bounds from selected-time density

Adapted from: here:o049

Original proof by session x0147 in k4_cap_class_terminal_charts/Remez.lean.
Three separated times and quadratic interpolation give a fixed cubic loss.
-/

namespace Submission.Lib.K4FinitePlankAtlases

open Set MeasureTheory

/-- Positive time measure supplies three separated interpolation times. -/
theorem exists_separated_time_triple (E : Set ℝ) {m : ℝ} (hm : 0 < m)
    (hvol : ENNReal.ofReal m ≤ volume E) :
    ∃ x₀ ∈ E, ∃ x₁ ∈ E, ∃ x₂ ∈ E,
      m / 6 ≤ |x₀ - x₁| ∧ m / 6 ≤ |x₀ - x₂| ∧ m / 6 ≤ |x₁ - x₂| := by
  have hpos : 0 < volume E := (ENNReal.ofReal_pos.mpr hm).trans_le hvol
  have hne : E.Nonempty := by
    by_contra he
    rw [Set.not_nonempty_iff_eq_empty.mp he, measure_empty] at hpos
    exact (lt_irrefl _ hpos)
  obtain ⟨x₀, hx₀⟩ := hne
  let d := m / 6
  have hd : 0 < d := by dsimp [d]; positivity
  have hlt₂ : ENNReal.ofReal (2 * d) < ENNReal.ofReal m :=
    (ENNReal.ofReal_lt_ofReal_iff hm).mpr (by dsimp [d]; linarith)
  have hlt₄ : ENNReal.ofReal (4 * d) < ENNReal.ofReal m :=
    (ENNReal.ofReal_lt_ofReal_iff hm).mpr (by dsimp [d]; linarith)
  obtain ⟨x₁, hx₁, h₀₁⟩ : ∃ x₁ ∈ E, x₁ ∉ Metric.ball x₀ d := by
    by_contra! he
    have h := hvol.trans (measure_mono he)
    rw [Real.volume_ball] at h
    exact (not_le_of_gt hlt₂) h
  obtain ⟨x₂, hx₂, h₂⟩ : ∃ x₂ ∈ E,
      x₂ ∉ Metric.ball x₀ d ∪ Metric.ball x₁ d := by
    by_contra! he
    have h := hvol.trans ((measure_mono he).trans (measure_union_le _ _))
    rw [Real.volume_ball, Real.volume_ball, ← ENNReal.ofReal_add (by positivity) (by positivity)] at h
    have heq : 2 * d + 2 * d = 4 * d := by ring
    rw [heq] at h
    exact (not_le_of_gt hlt₄) h
  have h₀₂ : x₂ ∉ Metric.ball x₀ d := fun h => h₂ (Or.inl h)
  have h₁₂ : x₂ ∉ Metric.ball x₁ d := fun h => h₂ (Or.inr h)
  refine ⟨x₀, hx₀, x₁, hx₁, x₂, hx₂, ?_, ?_, ?_⟩
  · simpa only [Metric.mem_ball, Real.dist_eq, abs_sub_comm, not_lt] using h₀₁
  · simpa only [Metric.mem_ball, Real.dist_eq, abs_sub_comm, not_lt] using h₀₂
  · simpa only [Metric.mem_ball, Real.dist_eq, abs_sub_comm, not_lt] using h₁₂

/-- A quadratic bound on any positive fraction of a time block extends to the
whole block with a fixed power loss. The time set need not be an interval. -/
theorem quadratic_whole_block_bound {f : ℝ → ℝ} (hf : ∃ a b c : ℝ, ∀ t : ℝ, f t = a * t ^ 2 + b * t + c)
    {s q m A : ℝ} (hq : 0 < q) (hm : 0 < m) (hA : 0 ≤ A)
    (E : Set ℝ) (hE : E ⊆ Icc s (s + q))
    (hvol : ENNReal.ofReal m ≤ volume E) (hbound : ∀ x ∈ E, |f x| ≤ A) :
    ∀ t ∈ Icc s (s + q), |f t| ≤ 648 * A * (q / m) ^ 3 := by
  obtain ⟨x₀, hx₀, x₁, hx₁, x₂, hx₂, hd₀₁, hd₀₂, hd₁₂⟩ :=
    exists_separated_time_triple E hm hvol
  intro t ht
  have hdist {x y : ℝ} (hx : x ∈ Icc s (s + q)) (hy : y ∈ Icc s (s + q)) :
      |x - y| ≤ q := abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
  let d := m / 6
  have hd : 0 < d := by dsimp [d]; positivity
  let Δ := (x₀ - x₁) * (x₀ - x₂) * (x₁ - x₂)
  have hden : d ^ 3 ≤ |Δ| := by
    calc
      _ = d * d * d := by ring
      _ ≤ |x₀ - x₁| * |x₀ - x₂| * |x₁ - x₂| := by gcongr
      _ = _ := by simp only [Δ, abs_mul]
  have hterm (x y z : ℝ) (hx : x ∈ E) (hy : y ∈ E) (hz : z ∈ E) :
      |f x * (t - y) * (t - z) * (y - z)| ≤ A * q ^ 3 := by
    calc
      _ = |f x| * |t - y| * |t - z| * |y - z| := by simp only [abs_mul]
      _ ≤ A * q * q * q := by
        gcongr
        · exact hbound x hx
        · exact hdist ht (hE hy)
        · exact hdist ht (hE hz)
        · exact hdist (hE hy) (hE hz)
      _ = _ := by ring
  have hidentity : f t * Δ =
      f x₀ * (t - x₁) * (t - x₂) * (x₁ - x₂) -
      f x₁ * (t - x₀) * (t - x₂) * (x₀ - x₂) +
      f x₂ * (t - x₀) * (t - x₁) * (x₀ - x₁) := by
    obtain ⟨a, b, c, hformula⟩ := hf
    simp only [hformula, Δ]
    ring
  have hnum : |f t * Δ| ≤ 3 * A * q ^ 3 := by
    rw [hidentity]
    apply (abs_add_le _ _).trans
    apply (add_le_add (abs_sub _ _) (le_refl _)).trans
    have h0 := hterm x₀ x₁ x₂ hx₀ hx₁ hx₂
    have h1 := hterm x₁ x₀ x₂ hx₁ hx₀ hx₂
    have h2 := hterm x₂ x₀ x₁ hx₂ hx₀ hx₁
    linarith
  have hmain : |f t| * d ^ 3 ≤ 3 * A * q ^ 3 := by
    calc
      _ ≤ |f t| * |Δ| := mul_le_mul_of_nonneg_left hden (abs_nonneg _)
      _ = |f t * Δ| := (abs_mul _ _).symm
      _ ≤ _ := hnum
  calc
    |f t| ≤ (3 * A * q ^ 3) / d ^ 3 := (le_div_iff₀ (pow_pos hd 3)).mpr hmain
    _ = _ := by dsimp [d]; field_simp <;> ring

/-- A trajectory seen for at least a `1/K` fraction of a block inherits the
whole-block quadratic bound with one fixed power of the common slack. -/
theorem quadratic_whole_block_of_time_density {f : ℝ → ℝ} (hf : ∃ a b c : ℝ, ∀ t : ℝ, f t = a * t ^ 2 + b * t + c)
    {s q K A : ℝ} (hq : 0 < q) (hK : 0 < K) (hA : 0 ≤ A)
    (E : Set ℝ) (hE : E ⊆ Icc s (s + q))
    (hvol : ENNReal.ofReal (q / K) ≤ volume E) (hbound : ∀ x ∈ E, |f x| ≤ A) :
    ∀ t ∈ Icc s (s + q), |f t| ≤ 648 * K ^ 3 * A := by
  have heq : q / (q / K) = K := by field_simp
  have h := quadratic_whole_block_bound hf hq (div_pos hq hK) hA E hE hvol hbound
  intro t ht
  simpa only [heq, mul_assoc, mul_comm A, mul_left_comm A] using h t ht

end Submission.Lib.K4FinitePlankAtlases
