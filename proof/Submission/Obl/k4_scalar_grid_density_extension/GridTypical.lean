import Submission.Obl.k4_native_grid_profile_extension.Profiles.TypicalDensity
import Submission.Obl.k4_native_grid_profile_extension.Profiles.ProfileGrid
import Submission.Obl.k4_native_grid_profile_extension.Profiles.DensityRefinement

/-!
# Typical density exponents under approximate refinement

The accepted o086 extension theorems assume nested observations, so that a finer
density is almost everywhere at most the coarser one. For the scalar bins
`⌊x / N ^ (-r)⌋` at different depths this fails; it holds up to a factor `N ^ ε`
outside power-small sets. The statements here are the corresponding versions:
extension of typical exponents from a dense grid, uniqueness of typical exponents,
and the increment bounds of limiting exponents.
-/

noncomputable section

namespace Submission.Obl.k4_scalar_grid_density_extension

open Set Filter MeasureTheory
open scoped Topology ENNReal
open Submission.Obl.k4_native_grid_profile_extension.Profiles

theorem ofReal_rpow_mul_rpow {N : ℝ} (hN : 0 < N) (a b : ℝ) :
    ENNReal.ofReal (N ^ a) * ENNReal.ofReal (N ^ b) = ENNReal.ofReal (N ^ (a + b)) := by
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _), ← Real.rpow_add hN]

theorem ofReal_rpow_le_ofReal_rpow {N : ℝ} (hN : 1 ≤ N) {a b : ℝ} (h : a ≤ b) :
    ENNReal.ofReal (N ^ a) ≤ ENNReal.ofReal (N ^ b) :=
  ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hN h)

/-- Comparison of powers of a base larger than one, inside `ENNReal`. -/
theorem le_of_ofReal_rpow_le {N : ℝ} (hN : 1 < N) {a b : ℝ}
    (h : ENNReal.ofReal (N ^ a) ≤ ENNReal.ofReal (N ^ b)) : a ≤ b := by
  have hb : 0 < N ^ b := Real.rpow_pos_of_pos (by linarith) _
  have h' := (ENNReal.ofReal_le_ofReal_iff hb.le).mp h
  exact (Real.rpow_le_rpow_left_iff hN).mp h'

/-- Dividing an inequality by a positive real power. -/
theorem le_ofReal_rpow_of_mul_le {N : ℝ} (hN : 0 < N) {a b : ℝ} {X Y : ℝ≥0∞}
    (hXY : ENNReal.ofReal (N ^ (-a)) * X ≤ Y) (hY : Y ≤ ENNReal.ofReal (N ^ b)) :
    X ≤ ENNReal.ofReal (N ^ (b + a)) := by
  have hc0 : ENNReal.ofReal (N ^ (-a)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hN _)).ne'
  have hc1 : ENNReal.ofReal (N ^ (-a)) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc
    X = ENNReal.ofReal (N ^ a) * (ENNReal.ofReal (N ^ (-a)) * X) := by
      rw [← mul_assoc, ofReal_rpow_mul_rpow hN, add_neg_cancel, Real.rpow_zero,
        ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (N ^ a) * ENNReal.ofReal (N ^ b) := mul_le_mul' le_rfl (hXY.trans hY)
    _ = ENNReal.ofReal (N ^ (b + a)) := by rw [ofReal_rpow_mul_rpow hN, add_comm]

theorem measure_union_le₃ {β : Type*} [MeasurableSpace β] (μ : Measure β) (A B C : Set β) :
    μ (A ∪ B ∪ C) ≤ μ A + μ B + μ C := by
  calc μ (A ∪ B ∪ C) ≤ μ (A ∪ B) + μ C := measure_union_le _ _
    _ ≤ μ A + μ B + μ C := by gcongr; exact measure_union_le _ _

theorem measure_union_le₄ {β : Type*} [MeasurableSpace β] (μ : Measure β) (A B C D : Set β) :
    μ (A ∪ B ∪ C ∪ D) ≤ μ A + μ B + μ C + μ D := by
  calc μ (A ∪ B ∪ C ∪ D) ≤ μ (A ∪ B ∪ C) + μ D := measure_union_le _ _
    _ ≤ μ A + μ B + μ C + μ D := by gcongr; exact measure_union_le₃ _ _ _ _

theorem typical_powerSmall {α : ℕ → Type*} [∀ k, MeasurableSpace (α k)]
    {N : ℕ → ℝ} {μ : (k : ℕ) → Measure (α k)} {d : (k : ℕ) → α k → ℝ≥0∞} {e : ℝ}
    (h : HasTypicalDensity N μ d e) (τ : ℝ) (hτ : 0 < τ) :
    IsPowerSmall N (fun k => μ k {x | d k x < ENNReal.ofReal (N k ^ (-e - τ)) ∨
      ENNReal.ofReal (N k ^ (-e + τ)) < d k x}) := h τ hτ

/-- Typical exponents are unique as soon as the total mass is not power-small. -/
theorem typical_exponent_unique {α : ℕ → Type*} [∀ k, MeasurableSpace (α k)]
    (N : ℕ → ℝ) (hN₂ : ∀ k, 2 ≤ N k) (hN : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (α k)) (d : (k : ℕ) → α k → ℝ≥0∞) {e e' : ℝ}
    (hmass : ¬ IsPowerSmall N (fun k => μ k univ))
    (he : HasTypicalDensity N μ d e) (he' : HasTypicalDensity N μ d e') : e = e' := by
  by_contra hne
  wlog hlt : e < e' generalizing e e'
  · exact this he' he (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
  let τ : ℝ := (e' - e) / 3
  have hτ : 0 < τ := by dsimp [τ]; linarith
  apply hmass
  apply ((typical_powerSmall he τ hτ).add hN (typical_powerSmall he' τ hτ)).mono
  apply Eventually.of_forall
  intro k
  have hN1 : 1 < N k := by linarith [hN₂ k]
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro p _
  by_contra hp
  simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hp
  obtain ⟨⟨h₁, _⟩, ⟨_, h₄⟩⟩ := hp
  have := le_of_ofReal_rpow_le hN1 (h₁.trans h₄)
  dsimp [τ] at this
  linarith

/-- Approximate antitonicity extends typical exponents from a dense grid to every
depth, for a continuous limiting profile. -/
theorem hasTypicalDensity_of_dense_approx {α : ℕ → Type*}
    [∀ k, MeasurableSpace (α k)]
    (N : ℕ → ℝ) (hN₁ : ∀ k, 1 ≤ N k) (hN : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (α k))
    (g : ℝ → (k : ℕ) → α k → ℝ≥0∞) (f : ℝ → ℝ) (hf : Continuous f)
    (grid : Set ℝ) (hgrid : Dense grid)
    (htypical : ∀ r ∈ grid, HasTypicalDensity N μ (g r) (f r))
    (hmono : ∀ r s : ℝ, r ≤ s → ∀ ε : ℝ, 0 < ε → IsPowerSmall N (fun k =>
      μ k {x | g r k x < ENNReal.ofReal (N k ^ (-ε)) * g s k x})) :
    ∀ r : ℝ, HasTypicalDensity N μ (g r) (f r) := by
  intro r τ hτ
  have hτ₄ : 0 < τ / 4 := by positivity
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuousAt_iff.mp (hf.continuousAt (x := r)) (τ / 4) hτ₄
  obtain ⟨lo, hloGrid, hlo⟩ := hgrid.exists_between (show r - δ < r by linarith)
  obtain ⟨hi, hhiGrid, hhi⟩ := hgrid.exists_between (show r < r + δ by linarith)
  have hfl : |f lo - f r| < τ / 4 := by
    simpa only [Real.dist_eq] using hfδ (show dist lo r < δ by
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hlo.2)]
      linarith [hlo.1])
  have hfh : |f hi - f r| < τ / 4 := by
    simpa only [Real.dist_eq] using hfδ (show dist hi r < δ by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hhi.1)]
      linarith [hhi.2])
  let bad : ℝ → (k : ℕ) → Set (α k) := fun q k =>
    {x | g q k x < ENNReal.ofReal (N k ^ (-f q - τ / 4)) ∨
      ENNReal.ofReal (N k ^ (-f q + τ / 4)) < g q k x}
  have hsmallLo : IsPowerSmall N (fun k => μ k (bad lo k)) := htypical lo hloGrid (τ / 4) hτ₄
  have hsmallHi : IsPowerSmall N (fun k => μ k (bad hi k)) := htypical hi hhiGrid (τ / 4) hτ₄
  have hM₁ := hmono lo r hlo.2.le (τ / 4) hτ₄
  have hM₂ := hmono r hi hhi.1.le (τ / 4) hτ₄
  apply (((hsmallLo.add hN hsmallHi).add hN hM₁).add hN hM₂).mono
  apply Eventually.of_forall
  intro k
  have hNk : 0 < N k := by linarith [hN₁ k]
  refine le_trans (measure_mono ?_) (measure_union_le₄ _ _ _ _ _)
  intro x hbad
  by_contra hx
  simp only [mem_union, not_or] at hx
  obtain ⟨⟨⟨hxl, hxh⟩, hx₁⟩, hx₂⟩ := hx
  simp only [bad, mem_ofPred_eq, not_or, not_lt] at hxl hxh hx₁ hx₂
  rcases hbad with hbad | hbad
  · -- lower bound through the finer depth `hi`
    have hlow : ENNReal.ofReal (N k ^ (-(τ / 4))) * ENNReal.ofReal (N k ^ (-f hi - τ / 4)) ≤
        g r k x := (mul_le_mul' le_rfl hxh.1).trans hx₂
    rw [ofReal_rpow_mul_rpow hNk] at hlow
    have : ENNReal.ofReal (N k ^ (-f r - τ)) ≤ ENNReal.ofReal (N k ^ (-(τ / 4) + (-f hi - τ / 4))) :=
      ofReal_rpow_le_ofReal_rpow (hN₁ k) (by linarith [(abs_lt.mp hfh).2])
    exact (not_lt_of_ge (this.trans hlow)) hbad
  · -- upper bound through the coarser depth `lo`
    have hup := le_ofReal_rpow_of_mul_le hNk hx₁ hxl.2
    have : ENNReal.ofReal (N k ^ (-f lo + τ / 4 + τ / 4)) ≤ ENNReal.ofReal (N k ^ (-f r + τ)) :=
      ofReal_rpow_le_ofReal_rpow (hN₁ k) (by linarith [(abs_lt.mp hfl).1])
    exact (not_lt_of_ge (hup.trans this)) hbad

/-- The compact-interval version of `hasTypicalDensity_of_dense_approx`. -/
theorem hasTypicalDensity_on_Icc_of_grid_approx {α : ℕ → Type*}
    [∀ k, MeasurableSpace (α k)]
    (N : ℕ → ℝ) (hN₁ : ∀ k, 1 ≤ N k) (hN : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (α k))
    (g : ℝ → (k : ℕ) → α k → ℝ≥0∞) (f : ℝ → ℝ) (hf : Continuous f)
    {a b : ℝ} (hab : a ≤ b) (grid : Set ℝ)
    (hgrid : closure grid = Icc a b) (ha : a ∈ grid) (hb : b ∈ grid)
    (htypical : ∀ r ∈ grid, HasTypicalDensity N μ (g r) (f r))
    (hmono : ∀ r ∈ Icc a b, ∀ s ∈ Icc a b, r ≤ s → ∀ ε : ℝ, 0 < ε →
      IsPowerSmall N (fun k => μ k {x | g r k x < ENNReal.ofReal (N k ^ (-ε)) * g s k x})) :
    ∀ r ∈ Icc a b, HasTypicalDensity N μ (g r) (f r) := by
  let clip : ℝ → ℝ := fun r => (projIcc a b hab r : ℝ)
  have hclip : Continuous clip := continuous_subtype_val.comp continuous_projIcc
  have hclipmono : Monotone clip := fun r s hrs => monotone_projIcc hab hrs
  have hclipmem (r : ℝ) : clip r ∈ Icc a b := (projIcc a b hab r).property
  have hclipself (r : ℝ) (hr : r ∈ Icc a b) : clip r = r :=
    congrArg Subtype.val (projIcc_of_mem hab hr)
  have hbase : ∀ r ∈ grid ∪ Iic a ∪ Ici b,
      HasTypicalDensity N μ (g (clip r)) (f (clip r)) := by
    intro r hr
    rcases hr with (hr | hr) | hr
    · have hr' : r ∈ Icc a b := hgrid ▸ subset_closure hr
      rw [hclipself r hr']
      exact htypical r hr
    · have hc : clip r = a := congrArg Subtype.val (projIcc_of_le_left hab hr)
      rw [hc]
      exact htypical a ha
    · have hc : clip r = b := congrArg Subtype.val (projIcc_of_right_le hab hr)
      rw [hc]
      exact htypical b hb
  have hall := hasTypicalDensity_of_dense_approx N hN₁ hN μ
    (fun r => g (clip r)) (fun r => f (clip r)) (hf.comp hclip)
    (grid ∪ Iic a ∪ Ici b) (dense_interval_grid_with_tails hgrid) hbase
    (fun r s hrs => hmono (clip r) (hclipmem r) (clip s) (hclipmem s) (hclipmono hrs))
  intro r hr
  simpa only [hclipself r hr] using hall r

/-- Joint typical profiles extend from a product grid to the rectangle. -/
theorem hasTypicalDensity_on_rectangle_of_grid_approx {α : ℕ → Type*}
    [∀ k, MeasurableSpace (α k)]
    (N : ℕ → ℝ) (hN₁ : ∀ k, 1 ≤ N k) (hN : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (α k))
    (g : ℝ × ℝ → (k : ℕ) → α k → ℝ≥0∞) (f : ℝ × ℝ → ℝ) (hf : Continuous f)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (gridR gridU : Set ℝ)
    (hgridR : closure gridR = Icc a b) (ha : a ∈ gridR) (hb : b ∈ gridR)
    (hgridU : closure gridU = Icc c d) (hc : c ∈ gridU) (hd : d ∈ gridU)
    (htypical : ∀ r ∈ gridR, ∀ u ∈ gridU, HasTypicalDensity N μ (g (r, u)) (f (r, u)))
    (hmonoR : ∀ u ∈ Icc c d, ∀ r ∈ Icc a b, ∀ s ∈ Icc a b, r ≤ s → ∀ ε : ℝ, 0 < ε →
      IsPowerSmall N (fun k => μ k {x | g (r, u) k x < ENNReal.ofReal (N k ^ (-ε)) * g (s, u) k x}))
    (hmonoU : ∀ r ∈ Icc a b, ∀ u ∈ Icc c d, ∀ v ∈ Icc c d, u ≤ v → ∀ ε : ℝ, 0 < ε →
      IsPowerSmall N (fun k => μ k {x | g (r, u) k x < ENNReal.ofReal (N k ^ (-ε)) * g (r, v) k x})) :
    ∀ r ∈ Icc a b, ∀ u ∈ Icc c d, HasTypicalDensity N μ (g (r, u)) (f (r, u)) := by
  have hrows : ∀ u ∈ gridU, ∀ r ∈ Icc a b,
      HasTypicalDensity N μ (g (r, u)) (f (r, u)) := by
    intro u hu
    have hu' : u ∈ Icc c d := hgridU ▸ subset_closure hu
    exact hasTypicalDensity_on_Icc_of_grid_approx N hN₁ hN μ (fun r => g (r, u))
      (fun r => f (r, u)) (hf.comp (continuous_id.prodMk continuous_const))
      hab gridR hgridR ha hb (fun r hr => htypical r hr u hu) (hmonoR u hu')
  intro r hr
  exact hasTypicalDensity_on_Icc_of_grid_approx N hN₁ hN μ (fun u => g (r, u))
    (fun u => f (r, u)) (hf.comp (continuous_const.prodMk continuous_id))
    hcd gridU hgridU hc hd (fun u hu => hrows u hu r hr) (hmonoU r hr)

/-- Increment bounds of typical exponents from approximate monotonicity and the
refinement low tail. -/
theorem density_exponent_increment_approx {α : ℕ → Type*}
    [∀ k, MeasurableSpace (α k)]
    (N : ℕ → ℝ) (hN₂ : ∀ k, 2 ≤ N k) (hN : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (α k))
    (coarse fine : (k : ℕ) → α k → ℝ≥0∞) (e₀ e₁ Δ : ℝ)
    (hmass : ¬ IsPowerSmall N (fun k => μ k Set.univ))
    (hcoarse : HasTypicalDensity N μ coarse e₀)
    (hfine : HasTypicalDensity N μ fine e₁)
    (hmono : ∀ ε : ℝ, 0 < ε → IsPowerSmall N (fun k =>
      μ k {x | coarse k x < ENNReal.ofReal (N k ^ (-ε)) * fine k x}))
    (htail : ∀ ε : ℝ, 0 < ε → IsPowerSmall N (fun k =>
      μ k {x | fine k x < ENNReal.ofReal (N k ^ (-(Δ + ε))) * coarse k x})) :
    0 ≤ e₁ - e₀ ∧ e₁ - e₀ ≤ Δ := by
  constructor
  · by_contra! hneg
    let τ : ℝ := (e₀ - e₁) / 4
    have hτ : 0 < τ := by dsimp [τ]; linarith
    apply hmass
    apply (((typical_powerSmall hcoarse τ hτ).add hN (typical_powerSmall hfine τ hτ)).add hN (hmono τ hτ)).mono
    apply Eventually.of_forall
    intro k
    have hN1 : 1 < N k := by linarith [hN₂ k]
    have hNk : 0 < N k := by linarith
    refine le_trans (measure_mono ?_) (measure_union_le₃ _ _ _ _)
    intro x _
    by_contra hx
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hx
    obtain ⟨⟨⟨_, hc₂⟩, ⟨hf₁, _⟩⟩, hm⟩ := hx
    have h : ENNReal.ofReal (N k ^ (-τ)) * ENNReal.ofReal (N k ^ (-e₁ - τ)) ≤
        ENNReal.ofReal (N k ^ (-e₀ + τ)) := ((mul_le_mul' le_rfl hf₁).trans hm).trans hc₂
    rw [ofReal_rpow_mul_rpow hNk] at h
    have := le_of_ofReal_rpow_le hN1 h
    dsimp [τ] at this
    linarith
  · by_contra! hgap
    let τ : ℝ := (e₁ - e₀ - Δ) / 8
    have hτ : 0 < τ := by dsimp [τ]; linarith
    apply hmass
    apply (((typical_powerSmall hcoarse τ hτ).add hN (typical_powerSmall hfine τ hτ)).add hN
      (htail (2 * τ) (by positivity))).mono
    apply Eventually.of_forall
    intro k
    have hN1 : 1 < N k := by linarith [hN₂ k]
    have hNk : 0 < N k := by linarith
    refine le_trans (measure_mono ?_) (measure_union_le₃ _ _ _ _)
    intro x _
    by_contra hx
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hx
    obtain ⟨⟨⟨hc₁, _⟩, ⟨_, hf₂⟩⟩, ht⟩ := hx
    have h : ENNReal.ofReal (N k ^ (-(Δ + 2 * τ))) * ENNReal.ofReal (N k ^ (-e₀ - τ)) ≤
        ENNReal.ofReal (N k ^ (-e₁ + τ)) := ((mul_le_mul' le_rfl hc₁).trans ht).trans hf₂
    rw [ofReal_rpow_mul_rpow hNk] at h
    have := le_of_ofReal_rpow_le hN1 h
    dsimp [τ] at this
    linarith

end Submission.Obl.k4_scalar_grid_density_extension
