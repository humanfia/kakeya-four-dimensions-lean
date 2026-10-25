import Submission.Obl.k4_dyadic_crop_affine_laws.ScaleBounds
import Submission.Obl.k4_native_grid_profile_extension.Profiles.TypicalDensity

noncomputable section

namespace Submission.Obl.k4_dyadic_crop_typicality

open MeasureTheory Filter Set
open scoped ENNReal
open Submission.Obl.k4_dyadic_crop_affine_laws
open Submission.Obl.k4_native_grid_profile_extension.Profiles

lemma ratio_exponents (N : ℕ → ℝ) (hN₂ : ∀ k, 2 ≤ N k)
    (hN : Tendsto N atTop atTop) (W : ℕ → ℕ)
    (p : (k : ℕ) → Fin (W k) → ℝ) (u₀ β : ℝ)
    (hp : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ γ,
      N k ^ (-β - ε) ≤ p k γ ∧ p k γ ≤ N k ^ (-β + ε)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ γ,
      N k ^ (β - 2 * u₀ - ε) ≤ Scale N k u₀ ^ 2 / p k γ ∧
      Scale N k u₀ ^ 2 / p k γ ≤ N k ^ (β - 2 * u₀ + ε) := by
  intro ε hε
  have hlarge : ∀ᶠ k in atTop, 4 ≤ N k ^ (ε / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < ε / 2)).comp hN).eventually
      (eventually_ge_atTop 4)
  filter_upwards [hp (ε / 2) (by positivity), hlarge] with k hpk h4 γ
  have hNk : 0 < N k := by linarith [hN₂ k]
  have hNk₁ : 1 ≤ N k := by linarith [hN₂ k]
  have hpγ : 0 < p k γ := (Real.rpow_pos_of_pos hNk _).trans_le (hpk γ).1
  have hsq : N k ^ (-2 * u₀) ≤ Scale N k u₀ ^ 2 := by
    have h := rpow_le_scale N k u₀ hNk
    have he : (N k ^ (-u₀)) ^ 2 = N k ^ (-2 * u₀) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNk.le]
      congr 1
      ring
    rw [← he]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hNk.le _) h 2
  constructor
  · calc
      N k ^ (β - 2 * u₀ - ε) ≤ N k ^ (β - 2 * u₀ - ε / 2) :=
        Real.rpow_le_rpow_of_exponent_le hNk₁ (by linarith)
      _ = N k ^ (-2 * u₀) / N k ^ (-β + ε / 2) := by
        rw [← Real.rpow_sub hNk]
        congr 1
        ring
      _ ≤ Scale N k u₀ ^ 2 / p k γ :=
        div_le_div₀ (sq_nonneg _) hsq hpγ (hpk γ).2
  · calc
      Scale N k u₀ ^ 2 / p k γ ≤
          (4 * N k ^ (-2 * u₀)) / N k ^ (-β - ε / 2) :=
        div_le_div₀ (by positivity) (scale_sq_le_four_rpow N k u₀ hNk)
          (Real.rpow_pos_of_pos hNk _) (hpk γ).1
      _ ≤ (N k ^ (ε / 2) * N k ^ (-2 * u₀)) / N k ^ (-β - ε / 2) := by
        gcongr
      _ = N k ^ (β - 2 * u₀ + ε) := by
        rw [← Real.rpow_add hNk, ← Real.rpow_sub hNk]
        congr 1
        ring

lemma powerSmall_mul_subpower {N R : ℕ → ℝ} (hN₁ : ∀ k, 1 ≤ N k)
    (hR : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, R k ≤ N k ^ ε)
    {a : ℕ → ENNReal} (ha : IsPowerSmall N a) :
    IsPowerSmall N (fun k => ENNReal.ofReal (R k) * a k) := by
  obtain ⟨c, hc, ha⟩ := ha
  refine ⟨c / 2, by positivity, ?_⟩
  filter_upwards [ha, hR (c / 2) (by positivity)] with k hak hRk
  calc
    ENNReal.ofReal (R k) * a k ≤
        ENNReal.ofReal (N k ^ (c / 2)) * ENNReal.ofReal (N k ^ (-c)) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hRk) hak
    _ = ENNReal.ofReal (N k ^ (-(c / 2))) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith [hN₁ k]) _),
        ← Real.rpow_add (by linarith [hN₁ k])]
      congr 2
      ring

/-- Finite crop tail estimates imply weighted typicality. All dependence on the
number of worlds disappears through the exact weights `p / rho`. -/
theorem typical_of_finite_tails {α χ : Type*} [MeasurableSpace α] [MeasurableSpace χ]
    (N : ℕ → ℝ) (hN₂ : ∀ k, 2 ≤ N k) (hN : Tendsto N atTop atTop)
    (W : ℕ → ℕ) (p ω : (k : ℕ) → Fin (W k) → ℝ) (ρ : ℕ → ℝ)
    (μ₀ : ℕ → Measure α) (μ : (k : ℕ) → Fin (W k) → Measure χ)
    (old : ℕ → α → ENNReal) (current : (k : ℕ) → Fin (W k) → χ → ENNReal)
    (u₀ β e : ℝ) (_hρ : ∀ k, 0 < ρ k)
    (hω : ∀ k γ, ω k γ = p k γ / ρ k)
    (hp : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ γ,
      N k ^ (-β - ε) ≤ p k γ ∧ p k γ ≤ N k ^ (-β + ε))
    (hρsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, (ρ k)⁻¹ ≤ N k ^ ε)
    (htyp : HasTypicalDensity N μ₀ old e)
    (hfinite : ∀ k (lo hi δ : ℝ), 0 < lo → 0 < hi → 0 < δ → δ ≤ 1 →
      (∑ γ, ENNReal.ofReal (p k γ) * (μ k γ)
        {x | current k γ x < ENNReal.ofReal ((Scale N k u₀ ^ 2 / p k γ) * δ * lo) ∨
          ENNReal.ofReal ((Scale N k u₀ ^ 2 / p k γ) * hi / δ) < current k γ x}) ≤
      (μ₀ k) {x | old k x < ENNReal.ofReal lo ∨ ENNReal.ofReal hi < old k x} +
        ENNReal.ofReal (32 * δ)) :
    ∀ τ : ℝ, 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      (∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ)
        {x | current k γ x < ENNReal.ofReal (N k ^ (-(e + 2 * u₀ - β) - τ)) ∨
          ENNReal.ofReal (N k ^ (-(e + 2 * u₀ - β) + τ)) < current k γ x}) ≤
        ENNReal.ofReal (N k ^ (-c)) := by
  intro τ hτ
  let η : ℝ := τ / 4
  have hη : 0 < η := by dsimp [η]; positivity
  let badOld : ℕ → Set α := fun k =>
    {x | old k x < ENNReal.ofReal (N k ^ (-e - η)) ∨
      ENNReal.ofReal (N k ^ (-e + η)) < old k x}
  have hsmallOld : IsPowerSmall N (fun k => μ₀ k (badOld k)) := htyp η hη
  have hsmallError : IsPowerSmall N (fun k => ENNReal.ofReal (32 * N k ^ (-η))) := by
    refine ⟨η / 2, by positivity, ?_⟩
    have hlarge : ∀ᶠ k in atTop, 32 ≤ N k ^ (η / 2) :=
      ((tendsto_rpow_atTop (by positivity : 0 < η / 2)).comp hN).eventually
        (eventually_ge_atTop 32)
    filter_upwards [hlarge] with k hk
    apply ENNReal.ofReal_le_ofReal
    calc
      32 * N k ^ (-η) ≤ N k ^ (η / 2) * N k ^ (-η) :=
        mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg (by linarith [hN₂ k]) _)
      _ = N k ^ (-(η / 2)) := by
        rw [← Real.rpow_add (by linarith [hN₂ k])]
        congr 1
        ring
  have hsmall := powerSmall_mul_subpower (fun k => by linarith [hN₂ k]) hρsub
    (hsmallOld.add hN hsmallError)
  apply hsmall.mono
  filter_upwards [ratio_exponents N hN₂ hN W p u₀ β hp η hη,
    hp 1 (by norm_num)] with k hratio hpk
  have hNk : 0 < N k := by linarith [hN₂ k]
  have hNk₁ : 1 ≤ N k := by linarith [hN₂ k]
  let B : Fin (W k) → Set χ := fun γ =>
    {x | current k γ x < ENNReal.ofReal (N k ^ (-(e + 2 * u₀ - β) - τ)) ∨
      ENNReal.ofReal (N k ^ (-(e + 2 * u₀ - β) + τ)) < current k γ x}
  let C : Fin (W k) → Set χ := fun γ =>
    {x | current k γ x <
        ENNReal.ofReal ((Scale N k u₀ ^ 2 / p k γ) * N k ^ (-η) * N k ^ (-e - η)) ∨
      ENNReal.ofReal ((Scale N k u₀ ^ 2 / p k γ) * N k ^ (-e + η) / N k ^ (-η)) <
        current k γ x}
  have hBC : ∀ γ, B γ ⊆ C γ := by
    intro γ x hx
    have hlow : N k ^ (-(e + 2 * u₀ - β) - τ) ≤
        (Scale N k u₀ ^ 2 / p k γ) * N k ^ (-η) * N k ^ (-e - η) := by
      calc
        _ ≤ N k ^ (β - 2 * u₀ - η) * N k ^ (-η) * N k ^ (-e - η) := by
          rw [← Real.rpow_add hNk, ← Real.rpow_add hNk]
          apply Real.rpow_le_rpow_of_exponent_le hNk₁
          dsimp [η]
          linarith
        _ ≤ _ := by gcongr; exact (hratio γ).1
    have hhigh : (Scale N k u₀ ^ 2 / p k γ) * N k ^ (-e + η) / N k ^ (-η) ≤
        N k ^ (-(e + 2 * u₀ - β) + τ) := by
      calc
        _ ≤ N k ^ (β - 2 * u₀ + η) * N k ^ (-e + η) / N k ^ (-η) := by
          gcongr
          exact (hratio γ).2
        _ ≤ _ := by
          rw [← Real.rpow_add hNk, ← Real.rpow_sub hNk]
          apply Real.rpow_le_rpow_of_exponent_le hNk₁
          dsimp [η]
          linarith
    rcases hx with hx | hx
    · exact Or.inl (hx.trans_le (ENNReal.ofReal_le_ofReal hlow))
    · exact Or.inr ((ENNReal.ofReal_le_ofReal hhigh).trans_lt hx)
  have hδ : N k ^ (-η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hNk₁ (by linarith)
  calc
    (∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ) (B γ)) =
        ENNReal.ofReal ((ρ k)⁻¹) * (∑ γ, ENNReal.ofReal (p k γ) * (μ k γ) (B γ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro γ _
      rw [hω, div_eq_mul_inv, ENNReal.ofReal_mul
        (le_of_lt ((Real.rpow_pos_of_pos hNk _).trans_le (hpk γ).1))]
      ac_rfl
    _ ≤ ENNReal.ofReal ((ρ k)⁻¹) * (∑ γ, ENNReal.ofReal (p k γ) * (μ k γ) (C γ)) := by
      gcongr with γ
      exact hBC γ
    _ ≤ ENNReal.ofReal ((ρ k)⁻¹) *
        ((μ₀ k) (badOld k) + ENNReal.ofReal (32 * N k ^ (-η))) :=
      mul_le_mul' le_rfl (hfinite k _ _ _ (Real.rpow_pos_of_pos hNk _)
        (Real.rpow_pos_of_pos hNk _) (Real.rpow_pos_of_pos hNk _) hδ)

end Submission.Obl.k4_dyadic_crop_typicality
