/- Adapted from this LOT tree, obligation o077, x0250, commit 6b0e9a0.
Interface originally from o077 session x0266; other original provenance follows. -/

import Submission.Obl.k4_dyadic_crop_affine_laws.ScaleBounds
import Submission.Obl.k4_dyadic_crop_affine_laws.UniformSlopeCeiling
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.SlopeCeiling

namespace Submission.Obl.k4_dyadic_crop_affine_laws

open MeasureTheory Set
open scoped ENNReal

lemma Crop_eq_cropTrajectoryEquiv_symm {a : ℝ} (ha : 0 < a) (q : Fin 4 → ℤ) :
    Crop a q = (Framework.cropTrajectoryEquiv a ha.ne'
      ![a * (q 0 : ℝ), a * (q 1 : ℝ)] ![a * (q 2 : ℝ), a * (q 3 : ℝ)]).symm := by
  funext l
  apply (Framework.cropTrajectoryEquiv a ha.ne'
    ![a * (q 0 : ℝ), a * (q 1 : ℝ)] ![a * (q 2 : ℝ), a * (q 3 : ℝ)]).injective
  rw [MeasurableEquiv.apply_symm_apply, Framework.cropTrajectoryEquiv_apply]
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> simp [Crop] <;> field_simp [ha.ne'] <;> ring

/-- Exact conditional crop relations and mass homogeneity give a common slope
ceiling with exponent `β-2u₀`. No density-typicality assertion is used here. -/
theorem slopeCeiling_of_cropRelations
    (N Λ₀ : ℕ → ℝ) (ν₀ : ℕ → Measure Line) (E₀ : ℕ → Set Inc) (u₀ β : ℝ)
    (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure Line) (E : (k : ℕ) → Fin (W k) → Set Inc)
    (p : (k : ℕ) → Fin (W k) → ℝ) (q : (k : ℕ) → Fin (W k) → (Fin 4 → ℤ))
    (ρ : ℕ → ℝ) (hN₂ : ∀ k, 2 ≤ N k) (hN : Filter.Tendsto N Filter.atTop Filter.atTop)
    (hprob : ∀ k, IsProbabilityMeasure (ν₀ k))
    (hcrop : CropRelations N ν₀ E₀ u₀ β W ω ν E p q ρ)
    (hceil : SlopeCeiling ν₀ Λ₀)
    (hΛ : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, Λ₀ k ≤ N k ^ ε) :
    ∃ Λ : ℕ → ℝ,
      (∀ k γ (Z : Set (EuclideanSpace ℝ (Fin 3))), ν k γ
        {l | (WithLp.toLp 2 ![l.2 3, l.2 4, l.2 5] : EuclideanSpace ℝ (Fin 3)) ∈ Z} ≤
          ENNReal.ofReal (Λ k) * volume Z) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, Λ k ≤ N k ^ (β - 2 * u₀ + ε)) := by
  classical
  let Λ : ℕ → ℝ := fun k => maxWorldCeiling Finset.univ (p k) (Scale N k u₀) (Λ₀ k)
  refine ⟨Λ, ?_, ?_⟩
  · intro k γ Z
    letI : IsProbabilityMeasure (ν₀ k) := hprob k
    obtain ⟨hp, hpeq, hν, _⟩ := hcrop.2.1 k γ
    have ha := scale_pos N k u₀
    let A := Cell (Scale N k u₀) (q k γ)
    have hAfin : ν₀ k A ≠ ∞ := measure_ne_top _ _
    have hp_eq : ENNReal.ofReal (p k γ) = ν₀ k A := by
      rw [hpeq, ENNReal.ofReal_toReal hAfin]
    have hA : ν₀ k A ≠ 0 := by
      rw [← hp_eq]
      exact ENNReal.ofReal_ne_zero_iff.mpr hp
    have hcond : ν k γ = Framework.conditionedPrior (ν₀ k) A
        (Framework.cropTrajectoryEquiv (Scale N k u₀) ha.ne'
          ![Scale N k u₀ * (q k γ 0 : ℝ), Scale N k u₀ * (q k γ 1 : ℝ)]
          ![Scale N k u₀ * (q k γ 2 : ℝ), Scale N k u₀ * (q k γ 3 : ℝ)]).symm := by
      simpa only [Framework.conditionedPrior, Crop_eq_cropTrajectoryEquiv_symm ha,
        hp_eq] using hν
    rw [hcond]
    have hc := Framework.conditioned_crop_slope_bound_real (ν₀ k) A hA hAfin
      (Scale N k u₀) ha
      ![Scale N k u₀ * (q k γ 0 : ℝ), Scale N k u₀ * (q k γ 1 : ℝ)]
      ![Scale N k u₀ * (q k γ 2 : ℝ), Scale N k u₀ * (q k γ 3 : ℝ)]
      (Λ₀ k) (fun T => hceil k T) Z
    refine hc.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    rw [← hpeq]
    exact le_maxWorldCeiling Finset.univ (p k) (Scale N k u₀) (Λ₀ k) (Finset.mem_univ γ)
  · have hgrowth := maxWorldCeiling_hasUpperExponent N (fun k => Scale N k u₀) Λ₀ hN₂ hN
      W (fun _ => Finset.univ) p u₀ β
      (fun k => scale_sq_le_four_rpow N k u₀ (by linarith [hN₂ k])) hΛ (by
        intro ε hε
        filter_upwards [hcrop.2.2.2.2 ε hε] with k hk
        intro γ _
        exact (hk γ).1)
    intro ε hε
    simpa only [Λ, show -2 * u₀ + β = β - 2 * u₀ by ring] using hgrowth ε hε

end Submission.Obl.k4_dyadic_crop_affine_laws
