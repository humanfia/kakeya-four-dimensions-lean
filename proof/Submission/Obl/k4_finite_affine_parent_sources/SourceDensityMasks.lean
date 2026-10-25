-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceRawCeilings

/-!
# Density masks at a fixed depth grid and the pure ceilings of a source model

`densMask` keeps the incidences whose original observation density is at most
`N^(-f r + τ)` at every depth `r` of a fixed finite grid. Its complement is covered by the
exceptional sets of the frozen concentration hypothesis. On a prepared set inside the mask, the
parent-normalised model has, at every model hidden width `(N^(uL))^(-s)` whose composed depth
`r₀ + u L s` lies within one grid mesh `h` below a grid depth, the raw ceiling
`κ (4 N^h + 2) N^(τ + 2 δ₀ L) (N^(uL))^(-d s)`.

Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set

noncomputable section

/-- The density mask of one world at the grid depths `r j`. -/
def densMask {G : ℕ} (g : ℝ → EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal) (Bw Nk τ : ℝ)
    (f : ℝ → ℝ) (r : Fin G → ℝ) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  ⋂ j, {p | g (r j) (obs Bw (δ Nk (r j)) p) ≤ ENNReal.ofReal (Nk ^ (-f (r j) + τ))}

theorem measurableSet_densMask {G : ℕ} {g : ℝ → EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal}
    {r : Fin G → ℝ} (hg : ∀ j, Measurable (g (r j))) (Bw Nk τ : ℝ) (f : ℝ → ℝ) :
    MeasurableSet (densMask g Bw Nk τ f r) := by
  refine MeasurableSet.iInter fun j => ?_
  exact measurableSet_le ((hg j).comp
    (Submission.Obl.k4_remainder_pure_profile_normalization.Normalization.measurable_obs _ _))
    measurable_const

/-- The complement of the mask lies in the union of the upper exceptional sets. -/
theorem densMask_compl_subset {G : ℕ} (g : ℝ → EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal)
    (Bw Nk τ : ℝ) (f : ℝ → ℝ) (r : Fin G → ℝ) :
    (densMask g Bw Nk τ f r)ᶜ ⊆ ⋃ j, {p | g (r j) (obs Bw (δ Nk (r j)) p) <
      ENNReal.ofReal (Nk ^ (-f (r j) - τ)) ∨
      ENNReal.ofReal (Nk ^ (-f (r j) + τ)) < g (r j) (obs Bw (δ Nk (r j)) p)} := by
  intro p hp
  simp only [densMask, mem_compl_iff, mem_iInter, not_forall, mem_ofPred_eq, not_le] at hp
  obtain ⟨j, hj⟩ := hp
  exact mem_iUnion.mpr ⟨j, Or.inr hj⟩

/-- **Mass of the masked-out incidences.** -/
theorem densMask_loss {W G : ℕ} (ω : Fin W → ℝ) (μ : Fin W → Measure ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (g : Fin W → ℝ → EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal) (B : Fin W → ℝ) (Nk τ : ℝ)
    (f : ℝ → ℝ) (r : Fin G → ℝ) :
    (∑ w, ENNReal.ofReal (ω w) * μ w (densMask (g w) (B w) Nk τ f r)ᶜ) ≤
      ∑ j, ∑ w, ENNReal.ofReal (ω w) * μ w {p | g w (r j) (obs (B w) (δ Nk (r j)) p) <
        ENNReal.ofReal (Nk ^ (-f (r j) - τ)) ∨
        ENNReal.ofReal (Nk ^ (-f (r j) + τ)) < g w (r j) (obs (B w) (δ Nk (r j)) p)} := by
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [← Finset.mul_sum]
  gcongr
  exact (measure_mono (densMask_compl_subset (g w) (B w) Nk τ f r)).trans
    (measure_iUnion_fintype_le _ _)

/-- **Pure ceiling of a parent-normalised model on a density mask**, at one model width. -/
theorem pframe_pure_ceiling {G : ℕ} (Φ : PFrame) (hq : 0 < Φ.F.q) (hD : IsUnit Φ.F.D.det)
    {Nk Bw rp κ detQ τ δ₀ L d u s h : ℝ} (hNk : 1 < Nk) (hsc : Φ.sc = Bw / δ Nk rp)
    (hκ : 1 ≤ κ) (hdetQ : 0 < detQ) (hdet : |Φ.F.D.det| ≤ detQ)
    (ν : Measure (ℕ × (Fin 6 → ℝ))) (A₀ : Set (ℕ × (Fin 6 → ℝ))) (hA₀t : ν A₀ ≠ ⊤)
    {f : ℝ → ℝ} (hfloor : ENNReal.ofReal (Nk ^ (-f rp) * detQ / κ) ≤ ν A₀)
    {E S : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {g : ℝ → EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal}
    {r : Fin G → ℝ} (hg : ∀ j, Measurable (g (r j)))
    (hlaw : ∀ j, ((ν.prod volume).restrict E).map (obs Bw (δ Nk (r j))) =
      (volume.prod Measure.count).withDensity (g (r j)))
    (hS : S ⊆ E ∩ densMask g Bw Nk τ f r)
    (hd : 0 ≤ d) (hs : 0 ≤ s) (hh : 0 ≤ h)
    (j : Fin G) (hj1 : rp + u * L * s ≤ r j) (hj2 : r j ≤ rp + u * L * s + h)
    (hprof : f rp + d * (r j - rp) - 2 * (δ₀ * L) ≤ f (r j)) :
    (muE ν A₀ Φ.F.t₀ Φ.F.q S).map (obsS Φ.eb (Nk ^ (-(u * L * s)))) ≤
      ENNReal.ofReal (κ * (4 * Nk ^ h + 2) * Nk ^ (τ + 2 * (δ₀ * L)) *
        Nk ^ (-(d * (u * L * s)))) • (volume.prod Measure.count) := by
  have hNk0 : 0 < Nk := by linarith
  have hδp := δ_bounds hNk rp
  have hδj := δ_bounds hNk (r j)
  have hδp0 : 0 < δ Nk rp := lt_of_lt_of_le (Real.rpow_pos_of_pos hNk0 _) hδp.1
  have hδj0 : 0 < δ Nk (r j) := lt_of_lt_of_le (Real.rpow_pos_of_pos hNk0 _) hδj.1
  have ha : 0 < Nk ^ (-(u * L * s)) := Real.rpow_pos_of_pos hNk0 _
  have hA₀ : 0 < ν A₀ := lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) hfloor
  have hSj : S ⊆ E ∩ {p | g (r j) (obs Bw (δ Nk (r j)) p) ≤
      ENNReal.ofReal (Nk ^ (-f (r j) + τ))} := by
    intro p hp
    obtain ⟨hpE, hpM⟩ := hS hp
    exact ⟨hpE, mem_iInter.mp hpM j⟩
  have hcap := pframe_raw_ceiling Φ hq hD Bw (δ Nk rp) hδp0 hsc ν A₀ hA₀ hA₀t hδj0 (hg j)
    (hlaw j) (by positivity) hSj ha
  -- the numeric bound
  have hν₀ : Nk ^ (-f rp) * detQ / κ ≤ (ν A₀).toReal := by
    have := ENNReal.toReal_mono hA₀t hfloor
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hratio : δ Nk rp * Nk ^ (-(u * L * s)) ≤ 2 * Nk ^ h * δ Nk (r j) := by
    have h1 : δ Nk rp * Nk ^ (-(u * L * s)) ≤ 2 * Nk ^ (-rp) * Nk ^ (-(u * L * s)) :=
      mul_le_mul_of_nonneg_right hδp.2.le ha.le
    have h2 : Nk ^ (-rp) * Nk ^ (-(u * L * s)) ≤ Nk ^ h * Nk ^ (-r j) := by
      rw [← Real.rpow_add hNk0, ← Real.rpow_add hNk0]
      exact Real.rpow_le_rpow_of_exponent_le hNk.le (by linarith)
    have h3 : Nk ^ h * Nk ^ (-r j) ≤ Nk ^ h * δ Nk (r j) :=
      mul_le_mul_of_nonneg_left hδj.1 (by positivity)
    nlinarith
  have hprof' : f rp + d * (u * L * s) - 2 * (δ₀ * L) ≤ f (r j) := by
    have : d * (u * L * s) ≤ d * (r j - rp) := mul_le_mul_of_nonneg_left (by linarith) hd
    linarith
  have hnum := raw_ceiling_numeric (τ := τ) hNk hκ hdetQ hdet hν₀ ha hδj0 hδp0 hratio hh hprof'
  refine hcap.trans (Measure.le_iff'.mpr fun U => ?_)
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hnum) _

end

end Submission.Obl.k4_finite_affine_parent_sources
