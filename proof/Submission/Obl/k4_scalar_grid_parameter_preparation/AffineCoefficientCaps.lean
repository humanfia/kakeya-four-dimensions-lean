/- Adapted from this LOT tree, o092, session x0317, commit d881f97f20e4.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/AffineCoefficientCaps.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.CoefficientPriorCaps

/-! Affine-prior ceilings obtained by summing coarse hidden-coefficient bins. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped Classical BigOperators ENNReal

theorem affine_coefficient_prior_cap {X : Type*} [MeasurableSpace X]
    (θ : Measure X) (a : X → Fin 5 → ℝ) (ξ ζ B : ℝ)
    (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) (hB : 1 ≤ B)
    (hbounded : ∀ᵐ l ∂θ, ∀ e, |a l e| ≤ B)
    (π : Measure ℝ) (U : ℝ≥0∞) (q c : ℤ)
    (hcap : ∀ z : Fin 5 → ℤ, θ {l | scalarMixedCoefficientTag ξ ζ (a l) = z} ≤
      U * π (scalarVelocityBin ξ (z 1))) :
    θ {l | (⌊a l 0 / ξ⌋ : ℤ) = q ∧ a l 1 ∈ scalarVelocityBin ξ c} ≤
      ENNReal.ofReal ((6 * B / ζ) ^ 3) * U * π (scalarVelocityBin ξ c) := by
  have hB₀ : 0 ≤ B := zero_le_one.trans hB
  obtain ⟨hfinite,hcount⟩ := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    (Set.Icc (-B) B) (by linarith : 0 ≤ 2 * B) hζ 0 (by
      intro x hx y hy
      rw [Real.dist_eq]
      exact abs_le.mpr ⟨by linarith [hx.1,hy.2],by linarith [hx.2,hy.1]⟩)
  simp only [sub_zero] at hfinite hcount
  let D : Finset ℤ := hfinite.toFinset
  let Q : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun _ => D)
  have hD (x : ℝ) (hx : |x| ≤ B) : (⌊x / ζ⌋ : ℤ) ∈ D :=
    hfinite.mem_toFinset.mpr ⟨x,abs_le.mp hx,rfl⟩
  have hDcard : (D.card : ℝ) ≤ 6 * B / ζ := by
    rw [← Set.ncard_eq_toFinset_card _ hfinite]
    have hratio : 1 ≤ B / ζ := (one_le_div hζ).mpr (hζ₁.trans hB)
    apply hcount.trans
    calc
      _ = 4 * (B / ζ) + 2 := by ring
      _ ≤ 6 * (B / ζ) := by linarith
      _ = _ := by ring
  have hQcard : (Q.card : ℝ) ≤ (6 * B / ζ) ^ 3 := by
    have he : Q.card = D.card ^ 3 := by simp [Q]
    rw [he,Nat.cast_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hDcard 3
  let full : (Fin 3 → ℤ) → Fin 5 → ℤ := fun b => ![q,c,b 0,b 1,b 2]
  have hcover : {l | (⌊a l 0 / ξ⌋ : ℤ) = q ∧ a l 1 ∈ scalarVelocityBin ξ c} ≤ᵐ[θ]
      ⋃ b ∈ Q, {l | scalarMixedCoefficientTag ξ ζ (a l) = full b} := by
    filter_upwards [hbounded] with l hl hC
    let b : Fin 3 → ℤ := ![⌊a l 2 / ζ⌋,⌊a l 3 / ζ⌋,⌊a l 4 / ζ⌋]
    have hb : b ∈ Q := by
      apply Fintype.mem_piFinset.mpr
      intro e
      fin_cases e <;> exact hD _ (hl _)
    refine Set.mem_iUnion₂.mpr ⟨b,hb,?_⟩
    have hc : (⌊a l 1 / ξ⌋ : ℤ) = c := hC.2
    ext e
    fin_cases e <;> simp [scalarMixedCoefficientTag,full,b,hC.1,hc]
  calc
    _ ≤ θ (⋃ b ∈ Q, {l | scalarMixedCoefficientTag ξ ζ (a l) = full b}) := measure_mono_ae hcover
    _ ≤ ∑ b ∈ Q, θ {l | scalarMixedCoefficientTag ξ ζ (a l) = full b} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _b ∈ Q, U * π (scalarVelocityBin ξ c) := Finset.sum_le_sum fun b _ => by
      simpa only [full,Matrix.cons_val_one,Matrix.cons_val_zero] using hcap (full b)
    _ = (Q.card : ℝ≥0∞) * U * π (scalarVelocityBin ξ c) := by
      simp only [Finset.sum_const,nsmul_eq_mul,mul_assoc]
    _ ≤ _ := by
      gcongr
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hQcard

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
