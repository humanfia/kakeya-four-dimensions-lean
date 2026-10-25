import Submission.Obl.k4_finite_positive_prepared_models.Synthetic.ModelEH2

/-!
# Levels and label masses of the synthetic stage model

A scale `s ∈ [1/n, 1]` uses the level `lev s ≤ D`, whose scale is within `1/(n m₀)` below `s`.
A label's prior is exactly `2^(-e₁ Gh) · 2^(-T) · 2^(-Ux)`. Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_positive_prepared_models.Synthetic

open MeasureTheory Set

noncomputable section

namespace Par

variable (p : Par)

theorem lev_le (s : ℝ) : p.lev s ≤ p.D := min_le_left _ _

theorem lev_bounds {s : ℝ} (h1 : 1 / (p.n : ℝ) ≤ s) (h2 : s ≤ 1) :
    p.sc (p.lev s) ≤ s ∧ s ≤ p.sc (p.lev s) + 1 / (p.n * p.m₀) := by
  have hnm := p.nm₀_pos
  have hn := p.n_pos
  have hm := p.m₀_pos'
  set k := ⌊s * p.n * p.m₀⌋₊ with hk
  have hs0 : 0 ≤ s * p.n * p.m₀ := by
    have : 0 ≤ s := le_trans (by positivity) h1
    positivity
  have hk1 : (k : ℝ) ≤ s * p.n * p.m₀ := Nat.floor_le hs0
  have hk2 : s * p.n * p.m₀ < k + 1 := Nat.lt_floor_add_one _
  have hkm : p.m₀ ≤ k := by
    apply Nat.le_floor
    have : (1 : ℝ) / p.n * p.n * p.m₀ ≤ s * p.n * p.m₀ := by gcongr
    have e : (1 : ℝ) / p.n * p.n * p.m₀ = p.m₀ := by field_simp
    linarith
  have hkD : k - p.m₀ ≤ p.D := by
    have : k ≤ p.n * p.m₀ := by
      apply Nat.floor_le_of_le
      push_cast
      nlinarith
    unfold D
    have hn1 : 1 ≤ p.n := by have := p.hn; omega
    have : (p.n - 1) * p.m₀ = p.n * p.m₀ - p.m₀ := by
      rw [Nat.sub_mul, one_mul]
    omega
  have hlev : p.lev s = k - p.m₀ := by
    unfold lev; rw [← hk]; exact min_eq_right hkD
  have hsc : p.sc (p.lev s) = (k : ℝ) / (p.n * p.m₀) := by
    unfold sc
    rw [hlev, Nat.add_sub_cancel' hkm]
  rw [hsc]
  constructor
  · rw [div_le_iff₀ hnm]; linarith
  · rw [← add_div, le_div_iff₀ hnm]; linarith

theorem lev_mono {s t : ℝ} (h : s ≤ t) : p.lev s ≤ p.lev t := by
  unfold lev
  apply min_le_min_left
  apply Nat.sub_le_sub_right
  apply Nat.floor_le_floor
  have := p.nm₀_pos
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_right h (by positivity)

/-- The hidden index mass of a prefix. -/
theorem idx_prefix (d : ℕ) (hd : d ≤ p.D) (h : Fin (2 ^ (p.synth.e₁ * p.synth.Gh d))) :
    ((idx p.synth.M).prod U) {q : ℕ × ℝ | q.1 < p.synth.M ∧
        pre p.synth.e₁ p.synth.G (p.synth.Gh d) q.1 = (h : ℕ) ∧ q.2 ∈ Icc (0 : ℝ) 1} =
      ((2 : ENNReal) ^ (p.synth.e₁ * p.synth.Gh d))⁻¹ := by
  have hGh : p.synth.Gh d ≤ p.synth.G := p.synth.hGhG d hd
  set Dd := 2 ^ (p.synth.e₁ * (p.synth.G - p.synth.Gh d)) with hDd
  have hset : {q : ℕ × ℝ | q.1 < p.synth.M ∧
      pre p.synth.e₁ p.synth.G (p.synth.Gh d) q.1 = (h : ℕ) ∧ q.2 ∈ Icc (0 : ℝ) 1} =
      {i : ℕ | i < p.synth.M ∧ i / Dd = (h : ℕ)} ×ˢ Icc (0 : ℝ) 1 := by
    ext q; simp only [mem_ofPred_eq, mem_prod, pre, hDd]; tauto
  have hM : p.synth.M = 2 ^ (p.synth.e₁ * p.synth.Gh d) * Dd := by
    unfold Synth.M; rw [hDd, ← pow_add, ← mul_add, Nat.add_sub_cancel' hGh]
  have hDpos : 0 < Dd := by positivity
  have hcount : ({i : ℕ | i < p.synth.M ∧ i / Dd = (h : ℕ)} ∩ Iio p.synth.M) =
      Ico ((h : ℕ) * Dd) ((h : ℕ) * Dd + Dd) := by
    ext i
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Iio, mem_Ico]
    constructor
    · rintro ⟨⟨_, hi⟩, _⟩
      rw [← hi]
      exact ⟨Nat.div_mul_le_self i Dd, by have := Nat.lt_div_mul_add (a := i) hDpos; linarith⟩
    · rintro ⟨h1, h2⟩
      have hdiv : i / Dd = (h : ℕ) :=
        Nat.div_eq_of_lt_le h1 (by rw [Nat.add_mul, one_mul]; exact h2)
      have hiM : i < p.synth.M := by
        rw [hM]
        calc i < (h : ℕ) * Dd + Dd := h2
          _ = ((h : ℕ) + 1) * Dd := by ring
          _ ≤ 2 ^ (p.synth.e₁ * p.synth.Gh d) * Dd := Nat.mul_le_mul_right _ h.2
      exact ⟨⟨hiM, hdiv⟩, hiM⟩
  rw [hset, Measure.prod_prod, idx_apply, hcount]
  have hU : U (Icc (0 : ℝ) 1) = 1 := by simp [U]
  rw [hU, mul_one]
  have hcard : (Ico ((h : ℕ) * Dd) ((h : ℕ) * Dd + Dd)).encard = Dd := by
    rw [← Finset.coe_Ico, Set.encard_coe_eq_coe_finsetCard, Nat.card_Ico]
    simp
  rw [hcard, hM]
  push_cast
  have h1 : (2 : ENNReal) ^ (p.synth.e₁ * p.synth.Gh d) ≠ 0 := by positivity
  have h2 : (Dd : ENNReal) ≠ 0 := by exact_mod_cast hDpos.ne'
  have h3 : (Dd : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.mul_inv (Or.inl h1) (Or.inl (by simp)), mul_assoc, ENNReal.inv_mul_cancel h2 h3, mul_one]

/-- The transverse mass of a label. -/
theorem U_x2 (d : ℕ) (i2 : Fin (2 ^ p.synth.Ux d)) :
    U (Ico (((i2 : ℕ) : ℝ) / 2 ^ p.synth.Ux d) ((((i2 : ℕ) : ℝ) + 1) / 2 ^ p.synth.Ux d)) =
      ENNReal.ofReal (1 / 2 ^ p.synth.Ux d) := by
  have hp : (0 : ℝ) < 2 ^ p.synth.Ux d := by positivity
  have hsub : Ico (((i2 : ℕ) : ℝ) / 2 ^ p.synth.Ux d) ((((i2 : ℕ) : ℝ) + 1) / 2 ^ p.synth.Ux d) ⊆
      Icc 0 1 := by
    intro x hx
    refine ⟨le_trans (by positivity) hx.1, le_trans hx.2.le ?_⟩
    rw [div_le_one hp]
    have : (i2 : ℕ) + 1 ≤ 2 ^ p.synth.Ux d := i2.2
    exact_mod_cast this
  simp only [U]
  rw [Measure.restrict_apply measurableSet_Ico, inter_eq_left.mpr hsub, Real.volume_Ico]
  congr 1
  field_simp
  ring

end Par

end

end Submission.Obl.k4_finite_positive_prepared_models.Synthetic
