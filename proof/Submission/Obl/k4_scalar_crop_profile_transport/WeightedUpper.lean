import Submission.Obl.k4_dyadic_crop_typicality.Assembly
import Submission.Obl.k4_scalar_grid_density_extension.GridExtension

noncomputable section

namespace Submission.Obl.k4_scalar_crop_profile_transport

open MeasureTheory Set Filter
open scoped ENNReal
open k4_native_grid_profile_extension.Profiles

/-- Conditional upper tails have the scalar density correction after weighting. -/
theorem weighted_upper_of_finite_tail {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (N : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hlim : Tendsto N atTop atTop)
    (W : ℕ → ℕ) (p ω : (k : ℕ) → Fin (W k) → ℝ) (ρ : ℕ → ℝ)
    (μ₀ : ℕ → Measure X) (μ : (k : ℕ) → Fin (W k) → Measure Y)
    (old : ℕ → X → ENNReal) (current : (k : ℕ) → Fin (W k) → Y → ENNReal)
    (u₀ α e : ℝ)
    (hω : ∀ k γ, ω k γ = p k γ / ρ k)
    (hpclass : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ γ,
      N k ^ (-α - ε) ≤ p k γ ∧ p k γ ≤ N k ^ (-α + ε))
    (hρsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, (ρ k)⁻¹ ≤ N k ^ ε)
    (htyp : HasTypicalDensity N μ₀ old e)
    (hfinite : ∀ k (hi δ : ℝ), 0 < hi → 0 < δ → δ ≤ 1 →
      (∑ γ, ENNReal.ofReal (p k γ) * μ k γ
        {y | ENNReal.ofReal ((N k ^ (-u₀) / p k γ) * hi / δ) < current k γ y}) ≤
      μ₀ k {x | ENNReal.ofReal hi < old k x} + ENNReal.ofReal (32 * δ)) :
    ∀ τ : ℝ, 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      (∑ γ, ENNReal.ofReal (ω k γ) * μ k γ
        {y | ENNReal.ofReal (N k ^ (-(e + u₀ - α) + τ)) < current k γ y}) ≤
        ENNReal.ofReal (N k ^ (-c)) := by
  intro τ hτ
  let η := τ / 4
  have hη : 0 < η := by dsimp [η]; positivity
  let B₀ : ℕ → Set X := fun k => {x | ENNReal.ofReal (N k ^ (-e + η)) < old k x}
  have hsmallOld : IsPowerSmall N (fun k => μ₀ k (B₀ k)) := by
    have hboth : IsPowerSmall N (fun k => μ₀ k
        {x | old k x < ENNReal.ofReal (N k ^ (-e - η)) ∨
          ENNReal.ofReal (N k ^ (-e + η)) < old k x}) := htyp η hη
    apply hboth.mono
    exact Eventually.of_forall fun k => measure_mono (fun x hx => Or.inr hx)
  have hsmallError : IsPowerSmall N (fun k => ENNReal.ofReal (32 * N k ^ (-η))) :=
    k4_scalar_grid_density_extension.isPowerSmall_of_le_const_mul N hlim 32 η hη _
      (Eventually.of_forall fun _ => le_rfl)
  have hsmall := k4_dyadic_crop_typicality.powerSmall_mul_subpower
    (fun k => by linarith [hN k]) hρsub (hsmallOld.add hlim hsmallError)
  apply hsmall.mono
  filter_upwards [hpclass η hη] with k hpk
  have hNk : 0 < N k := by linarith [hN k]
  have hNk₁ : 1 ≤ N k := by linarith [hN k]
  let B : Fin (W k) → Set Y := fun γ =>
    {y | ENNReal.ofReal (N k ^ (-(e + u₀ - α) + τ)) < current k γ y}
  let C : Fin (W k) → Set Y := fun γ =>
    {y | ENNReal.ofReal ((N k ^ (-u₀) / p k γ) * N k ^ (-e + η) / N k ^ (-η)) <
      current k γ y}
  have hp (γ : Fin (W k)) : 0 < p k γ :=
    (Real.rpow_pos_of_pos hNk _).trans_le (hpk γ).1
  have hratio (γ : Fin (W k)) : N k ^ (-u₀) / p k γ ≤ N k ^ (α - u₀ + η) := by
    calc
      _ ≤ N k ^ (-u₀) / N k ^ (-α - η) :=
        div_le_div₀ (Real.rpow_nonneg hNk.le _) le_rfl (Real.rpow_pos_of_pos hNk _) (hpk γ).1
      _ = _ := by rw [← Real.rpow_sub hNk]; congr 1; ring
  have hBC (γ : Fin (W k)) : B γ ⊆ C γ := by
    intro y hy
    dsimp only [B, C, mem_ofPred_eq] at hy ⊢
    apply lt_of_le_of_lt _ hy
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ N k ^ (α - u₀ + η) * N k ^ (-e + η) / N k ^ (-η) := by
        gcongr
        exact hratio γ
      _ ≤ _ := by
        rw [← Real.rpow_add hNk, ← Real.rpow_sub hNk]
        apply Real.rpow_le_rpow_of_exponent_le hNk₁
        dsimp [η]
        linarith
  have hδ : N k ^ (-η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hNk₁ (by linarith)
  calc
    (∑ γ, ENNReal.ofReal (ω k γ) * μ k γ (B γ)) =
        ENNReal.ofReal ((ρ k)⁻¹) * (∑ γ, ENNReal.ofReal (p k γ) * μ k γ (B γ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro γ _
      rw [hω, div_eq_mul_inv, ENNReal.ofReal_mul (hp γ).le]
      ac_rfl
    _ ≤ ENNReal.ofReal ((ρ k)⁻¹) * (∑ γ, ENNReal.ofReal (p k γ) * μ k γ (C γ)) := by
      gcongr with γ
      exact hBC γ
    _ ≤ ENNReal.ofReal ((ρ k)⁻¹) *
        (μ₀ k (B₀ k) + ENNReal.ofReal (32 * N k ^ (-η))) :=
      mul_le_mul' le_rfl (hfinite k _ _ (Real.rpow_pos_of_pos hNk _)
        (Real.rpow_pos_of_pos hNk _) hδ)

end Submission.Obl.k4_scalar_crop_profile_transport
