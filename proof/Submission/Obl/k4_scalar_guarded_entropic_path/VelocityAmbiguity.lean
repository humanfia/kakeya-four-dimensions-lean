import Submission.Obl.k4_scalar_guarded_entropic_path.Info.Canonical
import Submission.Lib.K4QuadraticSublevel

/-! A fine master velocity bin and a bounded affine change permit only
four local bins. The finite range is formed on the unchanged common law. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path

open Set MeasureTheory

noncomputable section

theorem abs_sub_le_of_floor_eq {x y δ : ℝ} (hδ : 0 < δ)
    (hfloor : (⌊x / δ⌋ : ℤ) = ⌊y / δ⌋) : |x - y| ≤ δ := by
  have hx₁ := Int.floor_le (x / δ)
  have hx₂ := Int.lt_floor_add_one (x / δ)
  have hy₁ := Int.floor_le (y / δ)
  have hy₂ := Int.lt_floor_add_one (y / δ)
  rw [← hfloor] at hy₁ hy₂
  have hdiv : |x / δ - y / δ| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    |x - y| = δ * |x / δ - y / δ| := by
      have heq : x - y = δ * (x / δ - y / δ) := by field_simp
      conv_lhs => rw [heq, abs_mul, abs_of_pos hδ]
    _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hdiv hδ.le
    _ = δ := mul_one _

theorem exists_four_velocity_bins {Ω J : Type*} (E : Set Ω)
    (world : Ω → J) (master localVelocity : Ω → ℝ) {δ₀ δ H : ℝ}
    (hδ₀ : 0 < δ₀) (hδ : 0 < δ) (hH : 0 ≤ H) (hscale : H * δ₀ ≤ δ)
    (hlip : ∀ x ∈ E, ∀ y ∈ E, world x = world y →
      |localVelocity x - localVelocity y| ≤ H * |master x - master y|)
    (j : J) (z₀ : ℤ) :
    ∃ S : Finset ℤ, S.card ≤ 4 ∧ ∀ x ∈ E, world x = j → (⌊master x / δ₀⌋ : ℤ) = z₀ →
      (⌊localVelocity x / δ⌋ : ℤ) ∈ S := by
  classical
  let A := {x | x ∈ E ∧ world x = j ∧ (⌊master x / δ₀⌋ : ℤ) = z₀}
  have hdiam : ∀ a ∈ localVelocity '' A, ∀ b ∈ localVelocity '' A, dist a b ≤ δ := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [Real.dist_eq]
    calc
      _ ≤ H * |master x - master y| := hlip x hx.1 y hy.1 (hx.2.1.trans hy.2.1.symm)
      _ ≤ H * δ₀ := mul_le_mul_of_nonneg_left
        (abs_sub_le_of_floor_eq hδ₀ (hx.2.2.trans hy.2.2.symm)) hH
      _ ≤ δ := hscale
  obtain ⟨hfinite, hcard⟩ := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    (localVelocity '' A) hδ.le hδ 0 hdiam
  have hfour : (((fun v : ℝ => (⌊v / δ⌋ : ℤ)) '' (localVelocity '' A)).ncard : ℝ) ≤ 4 := by
    simpa only [sub_zero, mul_div_cancel_right₀ 2 hδ.ne', show (2 : ℝ) + 2 = 4 by norm_num]
      using hcard
  have hfinite' : (((fun v : ℝ => (⌊v / δ⌋ : ℤ)) '' (localVelocity '' A))).Finite := by
    simpa only [sub_zero] using hfinite
  refine ⟨hfinite'.toFinset, ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card _ hfinite']
    exact_mod_cast hfour
  · intro x hx hw hv
    exact hfinite'.mem_toFinset.mpr ⟨localVelocity x, ⟨x, ⟨hx, hw, hv⟩, rfl⟩, rfl⟩

theorem exists_four_velocity_bins_ae {Ω J : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (E : Set Ω) (hE : ∀ᵐ x ∂P, x ∈ E)
    (world : Ω → J) (master localVelocity : Ω → ℝ) (code : Ω → ℤ)
    {δ₀ δ H : ℝ} (hδ₀ : 0 < δ₀) (hδ : 0 < δ) (hH : 0 ≤ H) (hscale : H * δ₀ ≤ δ)
    (hlip : ∀ x ∈ E, ∀ y ∈ E, world x = world y →
      |localVelocity x - localVelocity y| ≤ H * |master x - master y|)
    (hcode : ∀ᵐ x ∂P, code x = (⌊localVelocity x / δ⌋ : ℤ)) (j : J) (z₀ : ℤ) :
    ∃ S : Finset ℤ, S.card ≤ 4 ∧ ∀ᵐ x ∂P,
      world x = j → (⌊master x / δ₀⌋ : ℤ) = z₀ → code x ∈ S := by
  obtain ⟨S, hcard, hS⟩ := exists_four_velocity_bins E world master localVelocity
    hδ₀ hδ hH hscale hlip j z₀
  refine ⟨S, hcard, ?_⟩
  filter_upwards [hE, hcode] with x hx hc hw hv
  rw [hc]
  exact hS x hx hw hv

end

end Submission.Obl.k4_scalar_guarded_entropic_path
