-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceEH2
import Submission.Obl.k4_finite_affine_parent_sources.Original

/-!
# Raw ceilings of a parent-normalised model from original density masks

On the low-density part `{g ∘ obs ≤ M}` of an original law whose observation has density `g`,
the observation has density at most `M` (accepted `map_restrict_observation_cap_le`). A model
`muE` of a parent frame built on such a prepared set has, at every model hidden width `a`, the
raw ceiling `|det D| / ν(A₀) · (2 δ a / fine + 2) · M`. With the parent's saturation floor
`ν(A₀) ≥ N^(-f r₀) |det Q| / κ`, an exact-determinant frame and the linear profile, this is at
most `κ (4 N^h + 2) N^(τ + 2 δ₀ L) · N^(-d u L s)` when the original width sits within `h` of
the composed depth.

Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set

noncomputable section

/-- The low-density part of an observed law has the observation ceiling. -/
theorem raw_ceiling_of_density_mask {ν : Measure (ℕ × (Fin 6 → ℝ))}
    {E S : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B w : ℝ}
    {g : EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal} (hg : Measurable g)
    (hlaw : ((ν.prod volume).restrict E).map (obs B w) = (volume.prod Measure.count).withDensity g)
    (M : ENNReal) (hS : S ⊆ E ∩ {p | g (obs B w p) ≤ M}) :
    ((ν.prod volume).restrict S).map (obs B w) ≤ M • (volume.prod Measure.count) := by
  have hobs : Measurable (obs B w) :=
    Submission.Obl.k4_remainder_pure_profile_normalization.Normalization.measurable_obs B w
  have hG : MeasurableSet {p : (ℕ × (Fin 6 → ℝ)) × ℝ | g (obs B w p) ≤ M} :=
    measurableSet_le (hg.comp hobs) measurable_const
  have h1 : (ν.prod volume).restrict S ≤
      ((ν.prod volume).restrict E).restrict {p | g (obs B w p) ≤ M} := by
    rw [Measure.restrict_restrict hG]
    have hsub : S ⊆ {p | g (obs B w p) ≤ M} ∩ E := fun p hp => ⟨(hS hp).2, (hS hp).1⟩
    exact Measure.restrict_mono hsub le_rfl
  exact (Measure.map_mono h1 hobs).trans
    (Submission.Lib.K4ListedExceptions.map_restrict_observation_cap_le _ _ _ hobs g hg hlaw M)

/-- The frozen dyadic width is within a factor two above `N^(-r)`. -/
theorem δ_bounds {N : ℝ} (hN : 1 < N) (r : ℝ) :
    N ^ (-r) ≤ δ N r ∧ δ N r < 2 * N ^ (-r) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : 0 < Real.log N := Real.log_pos hN
  set x := r * Real.log N / Real.log 2 with hx
  have hNr : N ^ (-r) = (2 : ℝ) ^ (-x) := by
    rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos (by norm_num), hx]
    field_simp
  have hδ : δ N r = (2 : ℝ) ^ (-(⌊x⌋ : ℝ)) := by
    show (2 : ℝ) ^ (-(⌊r * Real.log N / Real.log 2⌋ : ℤ)) = _
    rw [← hx, zpow_neg, Real.rpow_neg (by norm_num), Real.rpow_intCast]
  rw [hNr, hδ]
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  constructor
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  · have : (2 : ℝ) ^ (-(⌊x⌋ : ℝ)) < (2 : ℝ) ^ (-x + 1) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    rwa [Real.rpow_add (by norm_num), Real.rpow_one, mul_comm] at this

/-- **Model raw ceiling on a density mask.** -/
theorem pframe_raw_ceiling (Φ : PFrame) (hq : 0 < Φ.F.q) (hD : IsUnit Φ.F.D.det)
    (Bw δp : ℝ) (hδp : 0 < δp) (hsc : Φ.sc = Bw / δp)
    (ν : Measure (ℕ × (Fin 6 → ℝ))) (A₀ : Set (ℕ × (Fin 6 → ℝ)))
    (hA₀ : 0 < ν A₀) (hA₀t : ν A₀ ≠ ⊤)
    {E S : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {fine : ℝ} (hfine : 0 < fine)
    {g : EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal} (hg : Measurable g)
    (hlaw : ((ν.prod volume).restrict E).map (obs Bw fine) =
      (volume.prod Measure.count).withDensity g)
    {Mr : ℝ} (hMr : 0 ≤ Mr) (hS : S ⊆ E ∩ {p | g (obs Bw fine p) ≤ ENNReal.ofReal Mr})
    {a : ℝ} (ha : 0 < a) :
    (muE ν A₀ Φ.F.t₀ Φ.F.q S).map (obsS Φ.eb a) ≤
      ENNReal.ofReal (|Φ.F.D.det| / (ν A₀).toReal * (2 * (δp * a) / fine + 2) * Mr) •
        (volume.prod Measure.count) := by
  have hcap := raw_ceiling_of_density_mask hg hlaw (ENNReal.ofReal Mr) hS
  have h := muE_raw_ceiling Φ hq hD δp Bw a hδp.ne' hsc (mul_pos hδp ha) ν A₀ S hfine _ hcap
  have hν₀ : 0 < (ν A₀).toReal := ENNReal.toReal_pos hA₀.ne' hA₀t
  have hscal : (ν A₀)⁻¹ * ENNReal.ofReal |Φ.F.D.det| *
      (ENNReal.ofReal (2 * (δp * a) / fine + 2) * ENNReal.ofReal Mr) =
      ENNReal.ofReal (|Φ.F.D.det| / (ν A₀).toReal * (2 * (δp * a) / fine + 2) * Mr) := by
    have hinv : (ν A₀)⁻¹ = ENNReal.ofReal ((ν A₀).toReal)⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos hν₀, ENNReal.ofReal_toReal hA₀t]
    have hr : 0 ≤ 2 * (δp * a) / fine + 2 := by positivity
    rw [hinv, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hr,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rwa [hscal] at h

/-- **The numeric form of the model raw ceiling.** -/
theorem raw_ceiling_numeric {Nk κ detQ detD ν₀ δp a fine h τ δ₀ L d u s fp fj : ℝ}
    (hNk : 1 < Nk) (hκ : 1 ≤ κ) (hdetQ : 0 < detQ) (hdet : detD ≤ detQ)
    (hν₀ : Nk ^ (-fp) * detQ / κ ≤ ν₀) (ha : 0 < a) (hfine : 0 < fine) (hδp : 0 < δp)
    (hratio : δp * a ≤ 2 * Nk ^ h * fine) (hh : 0 ≤ h)
    (hprof : fp + d * (u * s) - 2 * (δ₀ * L) ≤ fj) :
    detD / ν₀ * (2 * (δp * a) / fine + 2) * Nk ^ (-fj + τ) ≤
      κ * (4 * Nk ^ h + 2) * Nk ^ (τ + 2 * (δ₀ * L)) * Nk ^ (-(d * (u * s))) := by
  have hNk0 : 0 < Nk := by linarith
  have hpos : 0 < Nk ^ (-fp) * detQ / κ := by positivity
  have hν₀p : 0 < ν₀ := lt_of_lt_of_le hpos hν₀
  have hdetD0 : detD / ν₀ ≤ detQ / (Nk ^ (-fp) * detQ / κ) := by
    rcases le_or_gt detD 0 with h0 | h0
    · calc detD / ν₀ ≤ 0 := div_nonpos_of_nonpos_of_nonneg h0 hν₀p.le
        _ ≤ _ := by positivity
    · calc detD / ν₀ ≤ detQ / ν₀ := div_le_div_of_nonneg_right hdet hν₀p.le
        _ ≤ detQ / (Nk ^ (-fp) * detQ / κ) := div_le_div_of_nonneg_left hdetQ.le hpos hν₀
  have hsimp : detQ / (Nk ^ (-fp) * detQ / κ) = κ * Nk ^ fp := by
    rw [Real.rpow_neg hNk0.le]
    field_simp
  have hr : 2 * (δp * a) / fine + 2 ≤ 4 * Nk ^ h + 2 := by
    have : 2 * (δp * a) / fine ≤ 4 * Nk ^ h := by
      rw [div_le_iff₀ hfine]; nlinarith
    linarith
  have hr0 : 0 ≤ 2 * (δp * a) / fine + 2 := by positivity
  have hexp : Nk ^ fp * Nk ^ (-fj + τ) ≤ Nk ^ (τ + 2 * (δ₀ * L)) * Nk ^ (-(d * (u * s))) := by
    rw [← Real.rpow_add hNk0, ← Real.rpow_add hNk0]
    exact Real.rpow_le_rpow_of_exponent_le hNk.le (by linarith)
  have hM0 : 0 ≤ Nk ^ (-fj + τ) := by positivity
  have hfirst : detD / ν₀ ≤ κ * Nk ^ fp := hdetD0.trans hsimp.le
  have hκf : 0 ≤ κ * Nk ^ fp := by positivity
  calc detD / ν₀ * (2 * (δp * a) / fine + 2) * Nk ^ (-fj + τ)
      ≤ κ * Nk ^ fp * (4 * Nk ^ h + 2) * Nk ^ (-fj + τ) := by
        apply mul_le_mul_of_nonneg_right _ hM0
        calc detD / ν₀ * (2 * (δp * a) / fine + 2)
            ≤ κ * Nk ^ fp * (2 * (δp * a) / fine + 2) :=
              mul_le_mul_of_nonneg_right hfirst hr0
          _ ≤ κ * Nk ^ fp * (4 * Nk ^ h + 2) := mul_le_mul_of_nonneg_left hr hκf
    _ = κ * (4 * Nk ^ h + 2) * (Nk ^ fp * Nk ^ (-fj + τ)) := by ring
    _ ≤ κ * (4 * Nk ^ h + 2) * (Nk ^ (τ + 2 * (δ₀ * L)) * Nk ^ (-(d * (u * s)))) := by
        gcongr
    _ = _ := by ring

end

end Submission.Obl.k4_finite_affine_parent_sources
