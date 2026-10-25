import Submission.Obl.k4_finite_positive_mixed_cover_realization.Grid

/-!
# Numerics of the time branch

`time_reference_shift`: a time cover realized at depth `r i + (θ/4) h L` with short blocks
costing `N ^ (κ₁ (θ/4) h L / 2)` over the old level `i` is an improvement over a deeper grid
level `i'`, at the requested gain `α * gain`, once `α ≤ θ/8` and `ρ ≤ κ₁ θ / 80`. The fine grid
supplies `i'`; its own time exponent pays the short-block refinement.

Also finite lower/upper bounds for families indexed by a finite type.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

/-- A positive real family over a finite type has a common positive lower bound. -/
theorem finite_pos_lower {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ i, c ≤ a i := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl _ => exact ⟨1, one_pos, le_rfl, fun i => isEmptyElim i⟩
  | inr _ =>
    obtain ⟨i₀, _, hmin⟩ := (Finset.univ : Finset ι).exists_min_image a Finset.univ_nonempty
    refine ⟨min 1 (a i₀), lt_min one_pos (ha i₀), min_le_left _ _, fun i => ?_⟩
    exact (min_le_right _ _).trans (hmin i (Finset.mem_univ i))

/-- A real family over a finite type has a common upper bound, at least any given value. -/
theorem finite_upper {ι : Type*} [Fintype ι] (a : ι → ℝ) (b : ℝ) :
    ∃ c : ℝ, b ≤ c ∧ ∀ i, a i ≤ c := by
  classical
  have hsum : 0 ≤ ∑ i, |a i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨max b 0 + ∑ i, |a i|, ?_, fun i => ?_⟩
  · have := le_max_left b 0
    linarith
  · have h1 : |a i| ≤ ∑ i, |a i| :=
      Finset.single_le_sum (f := fun i => |a i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 := le_abs_self (a i)
    have h3 := le_max_right b 0
    linarith

/-- **Reference-level shift.** The output of the time realization at depth at least
`r i + (θ/4) h L`, with `2 ^ T₂ ≤ 2 ^ T i * N ^ (κ₁ ((θ/4) h) L / 2)`, is a depth improvement
over a suitable grid level at gain `α * gain`. -/
theorem time_reference_shift {m : ℕ} {s r : ℕ → ℝ} {T : ℕ → ℕ}
    {gain ρ δ₀ L κ₁ θ α Nk h h' r₂ : ℝ} {T₂ i : ℕ}
    (hs : FineGrid m s gain ρ) (hL : 0 < L) (hN : 1 ≤ Nk) (hgain : 0 < gain)
    (hκ₁ : 0 < κ₁) (hκ₁1 : κ₁ ≤ 1) (hθ : 0 < θ) (hθ4 : θ ≤ 1 / 4)
    (hα : 0 < α) (hαθ : α ≤ θ / 8) (hρ : 0 < ρ) (hρθ : ρ ≤ κ₁ * θ / 80)
    (hδ₀ : 0 ≤ δ₀) (hδρ : δ₀ ≤ ρ * gain)
    (hlev : ∀ i, i < m → |r i - s i * L| ≤ δ₀ * L ∧
      Nk ^ ((κ₁ * s i - δ₀) * L) ≤ (2 : ℝ) ^ T i ∧ (2 : ℝ) ^ T i ≤ Nk ^ ((κ₁ * s i + δ₀) * L))
    (hi : i < m) (hgh : gain ≤ h) (hhh : h ≤ h') (hroom : r i + 2 * h' * L ≤ L)
    (hr₂ : r i + (θ / 4) * h * L ≤ r₂)
    (htime : (2 : ℝ) ^ T₂ ≤ (2 : ℝ) ^ T i * Nk ^ (κ₁ * ((θ / 4) * h) * L / 2)) :
    ∃ i', i' < m ∧ r i' + α * gain * L ≤ r₂ ∧
      (2 : ℝ) ^ T₂ ≤ (2 : ℝ) ^ T i' * Nk ^ (κ₁ * (α * gain) * L / 2) := by
  have hN0 : 0 < Nk := by linarith
  have hh : 0 < h := hgain.trans_le hgh
  obtain ⟨hdi, hTilo, hTihi⟩ := hlev i hi
  obtain ⟨hdi₁, hdi₂⟩ := abs_le.mp hdi
  have hκθ : κ₁ * θ ≤ θ := by
    have := mul_le_mul_of_nonneg_right hκ₁1 hθ.le
    linarith
  have hθ1 : θ / 4 ≤ 1 := by linarith
  -- elementary products
  have hαg : α * gain ≤ (θ / 8) * gain := mul_le_mul_of_nonneg_right hαθ hgain.le
  have hρg : ρ * gain ≤ (κ₁ * θ / 80) * gain := mul_le_mul_of_nonneg_right hρθ hgain.le
  have hθh : (θ / 4) * gain ≤ (θ / 4) * h := mul_le_mul_of_nonneg_left hgh (by positivity)
  have hθhh : (θ / 4) * h ≤ h := by
    have := mul_le_mul_of_nonneg_right hθ1 hh.le
    linarith
  have hκθg : (κ₁ * θ / 80) * gain ≤ (θ / 80) * gain := by
    have := mul_le_mul_of_nonneg_right hκθ hgain.le
    linarith
  have hθgain : α * gain + 2 * δ₀ ≤ (θ / 4) * gain := by linarith
  -- the target grid depth
  set y : ℝ := s i + (θ / 4) * h - α * gain - 2 * δ₀ with hy
  have hsmono : StrictMonoOn s (Set.Iio m) := by
    apply strictMonoOn_of_lt_add_one (Set.ordConnected_Iio)
    intro a _ ha hnext
    exact hs.1.2.2.1 a hnext
  have hs0 : s 0 ≤ s i := hsmono.monotoneOn hs.1.1 hi (Nat.zero_le _)
  have hyi : s i ≤ y := by rw [hy]; linarith
  have hy1 : y ≤ 1 := by
    have hh' : 0 < h' := hh.trans_le hhh
    have hδh' : δ₀ ≤ h' := by
      have : ρ * gain ≤ gain := by
        have := mul_le_mul_of_nonneg_right (show ρ ≤ 1 by linarith) hgain.le
        linarith
      linarith
    have hsiL : s i * L ≤ (1 - 2 * h' + δ₀) * L := by linarith
    have hsi' : s i ≤ 1 - 2 * h' + δ₀ := le_of_mul_le_mul_right hsiL hL
    have hαg0 : 0 ≤ α * gain := (mul_pos hα hgain).le
    rw [hy]
    linarith
  obtain ⟨i', hi', hsi'y, hysi'⟩ := hs.predecessor (by positivity) (hs0.trans hyi) hy1
  obtain ⟨hdi', hTi'lo, hTi'hi⟩ := hlev i' hi'
  obtain ⟨hdi'₁, hdi'₂⟩ := abs_le.mp hdi'
  refine ⟨i', hi', ?_, ?_⟩
  · -- depth
    have hyL : s i' * L ≤ y * L := mul_le_mul_of_nonneg_right hsi'y hL.le
    have hyL' : y * L = s i * L + (θ / 4) * h * L - α * gain * L - 2 * δ₀ * L := by
      rw [hy]; ring
    linarith
  · -- time
    have hlow : s i + (θ / 4) * h - α * gain - 2 * δ₀ - ρ * gain ≤ s i' := by
      have : y - ρ * gain ≤ s i' := by linarith
      rw [hy] at this
      exact this
    have key : κ₁ * s i + δ₀ + κ₁ * ((θ / 4) * h) / 2 ≤
        κ₁ * s i' - δ₀ + κ₁ * (α * gain) / 2 := by
      have hk := mul_le_mul_of_nonneg_left hlow hκ₁.le
      have hθh8 : κ₁ * ((θ / 8) * gain) ≤ κ₁ * ((θ / 8) * h) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgh (by positivity)) hκ₁.le
      have hαg' : κ₁ * (α * gain) ≤ κ₁ * ((θ / 8) * gain) :=
        mul_le_mul_of_nonneg_left hαg hκ₁.le
      have hδ1 : κ₁ * δ₀ ≤ δ₀ := by
        have := mul_le_mul_of_nonneg_right hκ₁1 hδ₀
        linarith
      have hρg1 : κ₁ * (ρ * gain) ≤ ρ * gain := by
        have := mul_le_mul_of_nonneg_right hκ₁1 (mul_nonneg hρ.le hgain.le)
        linarith
      have h5 : 5 * (ρ * gain) ≤ κ₁ * ((θ / 16) * gain) := by
        have : (κ₁ * θ / 80) * gain = κ₁ * ((θ / 16) * gain) / 5 := by ring
        linarith
      have e1 : κ₁ * (s i + (θ / 4) * h - α * gain - 2 * δ₀ - ρ * gain) =
          κ₁ * s i + 2 * (κ₁ * ((θ / 8) * h)) - κ₁ * (α * gain) - 2 * (κ₁ * δ₀) -
            κ₁ * (ρ * gain) := by ring
      have e2 : κ₁ * ((θ / 4) * h) / 2 = κ₁ * ((θ / 8) * h) := by ring
      have e3 : κ₁ * ((θ / 8) * gain) = κ₁ * ((θ / 16) * gain) * 2 := by ring
      rw [e1] at hk
      rw [e2]
      linarith
    have hexp : (κ₁ * s i + δ₀) * L + κ₁ * ((θ / 4) * h) * L / 2 ≤
        (κ₁ * s i' - δ₀) * L + κ₁ * (α * gain) * L / 2 := by
      have := mul_le_mul_of_nonneg_right key hL.le
      have e4 : (κ₁ * s i + δ₀ + κ₁ * ((θ / 4) * h) / 2) * L =
          (κ₁ * s i + δ₀) * L + κ₁ * ((θ / 4) * h) * L / 2 := by ring
      have e5 : (κ₁ * s i' - δ₀ + κ₁ * (α * gain) / 2) * L =
          (κ₁ * s i' - δ₀) * L + κ₁ * (α * gain) * L / 2 := by ring
      linarith
    calc (2 : ℝ) ^ T₂ ≤ (2 : ℝ) ^ T i * Nk ^ (κ₁ * ((θ / 4) * h) * L / 2) := htime
      _ ≤ Nk ^ ((κ₁ * s i + δ₀) * L) * Nk ^ (κ₁ * ((θ / 4) * h) * L / 2) :=
          mul_le_mul_of_nonneg_right hTihi (by positivity)
      _ = Nk ^ ((κ₁ * s i + δ₀) * L + κ₁ * ((θ / 4) * h) * L / 2) := by
          rw [Real.rpow_add hN0]
      _ ≤ Nk ^ ((κ₁ * s i' - δ₀) * L + κ₁ * (α * gain) * L / 2) :=
          Real.rpow_le_rpow_of_exponent_le hN hexp
      _ = Nk ^ ((κ₁ * s i' - δ₀) * L) * Nk ^ (κ₁ * (α * gain) * L / 2) := by
          rw [Real.rpow_add hN0]
      _ ≤ (2 : ℝ) ^ T i' * Nk ^ (κ₁ * (α * gain) * L / 2) :=
          mul_le_mul_of_nonneg_right hTi'lo (by positivity)

end Submission.Obl.k4_finite_positive_mixed_cover_realization
