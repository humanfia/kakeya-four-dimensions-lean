-- Adapted from this LOT tree, o232 `k4_finite_positive_prepared_models`, session x0807,
-- branch x0807 at commit 96b53fe05c6301b6463738f96ea23d9c511248b2.
-- Source: Submission/Obl/k4_finite_positive_prepared_models/RelativeBlocks.lean (namespace renamed to `Submission.Obl.k4_finite_affine_candidate_return`).
import Submission.Obl.k4_finite_affine_candidate_return.EStages
import Submission.Lib.K4ChartLifting.Normalize

namespace Submission.Obl.k4_finite_affine_candidate_return

open Set

/-- A nested old dyadic block has an actual dyadic label in unit parent
time. The equality concerns the whole closed block, including endpoints. -/
theorem exists_relative_time_block
    {T₀ T₁ : ℕ} (hT : T₀ ≤ T₁) (j₀ : Fin (2 ^ T₀)) (j₁ : Fin (2 ^ T₁))
    (hlo : (j₀ : ℝ) / (2 : ℝ) ^ T₀ ≤ (j₁ : ℝ) / (2 : ℝ) ^ T₁)
    (hhi : ((j₁ : ℝ) + 1) / (2 : ℝ) ^ T₁ ≤ ((j₀ : ℝ) + 1) / (2 : ℝ) ^ T₀) :
    ∃ j : Fin (2 ^ (T₁ - T₀)), ∀ t : ℝ,
      t ∈ IS T₁ j₁ ↔
        (t - (j₀ : ℝ) / (2 : ℝ) ^ T₀) / (((2 : ℝ) ^ T₀)⁻¹) ∈ IS (T₁ - T₀) j := by
  let U := T₁ - T₀
  have hTU : T₀ + U = T₁ := Nat.add_sub_of_le hT
  have hpow : (2 : ℝ) ^ T₁ = (2 : ℝ) ^ T₀ * (2 : ℝ) ^ U := by rw [← pow_add, hTU]
  have hq₀ : (0 : ℝ) < (2 : ℝ) ^ T₀ := by positivity
  have hqU : (0 : ℝ) < (2 : ℝ) ^ U := by positivity
  have hnorm (x : ℝ) : x / (2 : ℝ) ^ T₁ = (x / (2 : ℝ) ^ U) / (2 : ℝ) ^ T₀ := by
    rw [hpow]
    field_simp
  have hloR : (j₀ : ℝ) * (2 : ℝ) ^ U ≤ (j₁ : ℝ) := by
    rw [hnorm] at hlo
    exact (le_div_iff₀ hqU).mp ((div_le_div_iff_of_pos_right hq₀).mp hlo)
  have hhiR : (j₁ : ℝ) + 1 ≤ ((j₀ : ℝ) + 1) * (2 : ℝ) ^ U := by
    rw [hnorm] at hhi
    exact (div_le_iff₀ hqU).mp ((div_le_div_iff_of_pos_right hq₀).mp hhi)
  have hloN : (j₀ : ℕ) * 2 ^ U ≤ (j₁ : ℕ) := by exact_mod_cast hloR
  have hhiN : (j₁ : ℕ) + 1 ≤ ((j₀ : ℕ) + 1) * 2 ^ U := by exact_mod_cast hhiR
  rw [Nat.add_mul, one_mul] at hhiN
  let j : Fin (2 ^ U) := ⟨(j₁ : ℕ) - (j₀ : ℕ) * 2 ^ U, by omega⟩
  have hj : (j₀ : ℕ) * 2 ^ U + (j : ℕ) = (j₁ : ℕ) := by dsimp only [j]; omega
  refine ⟨j, fun t => ?_⟩
  have h := Submission.Lib.K4ChartLifting.mem_timeBlock_liftBlock j₀ j t
  change t ∈ IS (T₀ + U) (Submission.Lib.K4ChartLifting.liftBlock j₀ j) ↔
    (t - (j₀ : ℝ) / (2 : ℝ) ^ T₀) / (1 / (2 : ℝ) ^ T₀) ∈ IS U j at h
  have hblock : IS (T₀ + U) (Submission.Lib.K4ChartLifting.liftBlock j₀ j) = IS T₁ j₁ := by
    simp only [IS, Submission.Lib.K4ChartLifting.liftBlock, hj, hTU]
  rw [hblock] at h
  simpa only [one_div] using h

/-- The same parent normalization preserves every true nesting relation. -/
theorem normalized_time_subset
    (t₀ q : ℝ) (hq : q ≠ 0) (I J I' J' : Set ℝ)
    (hI : ∀ t, t ∈ I ↔ (t - t₀) / q ∈ I')
    (hJ : ∀ t, t ∈ J ↔ (t - t₀) / q ∈ J') (hsub : I ⊆ J) : I' ⊆ J' := by
  intro t ht
  have heq : (t₀ + q * t - t₀) / q = t := by field_simp; ring
  have htI : t₀ + q * t ∈ I := (hI _).mpr (by rwa [heq])
  have htJ := (hJ _).mp (hsub htI)
  rwa [heq] at htJ

/-- Equality of whole closed time blocks determines both actual
endpoints under the common affine time normalization. -/
theorem affine_interval_endpoints
    (t₀ q a b c d : ℝ) (hq : 0 < q) (hab : a ≤ b) (hcd : c ≤ d)
    (hI : ∀ t : ℝ, t ∈ Icc a b ↔ (t - t₀) / q ∈ Icc c d) :
    a = t₀ + q * c ∧ b = t₀ + q * d := by
  have hnorm (t : ℝ) : (t₀ + q * t - t₀) / q = t := by field_simp; ring
  constructor
  · apply le_antisymm
    · exact ((hI _).mpr (by rw [hnorm]; exact ⟨le_rfl, hcd⟩)).1
    · have h := (le_div_iff₀ hq).mp ((hI a).mp ⟨le_rfl, hab⟩).1
      linarith
  · apply le_antisymm
    · have h := (div_le_iff₀ hq).mp ((hI b).mp ⟨hab, le_rfl⟩).2
      linarith
    · exact ((hI _).mpr (by rw [hnorm]; exact ⟨hcd, le_rfl⟩)).2

/-- Whole-block correspondence restores the original dyadic time
length exactly, even when the source interface gives only membership
equivalence rather than an explicit difference of dyadic exponents. -/
theorem relative_time_length
    (t₀ q : ℝ) (hq : 0 < q) (Told Tnative : ℕ) (jold : ℕ)
    (jnative : Fin (2 ^ Tnative))
    (hI : ∀ t : ℝ,
      t ∈ Icc ((jold : ℝ) / (2 : ℝ) ^ Told)
        (((jold : ℝ) + 1) / (2 : ℝ) ^ Told) ↔
      (t - t₀) / q ∈ IS Tnative jnative) :
    q / (2 : ℝ) ^ Tnative = ((2 : ℝ) ^ Told)⁻¹ := by
  have hpow (T : ℕ) : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  have hends := affine_interval_endpoints t₀ q
    ((jold : ℝ) / (2 : ℝ) ^ Told) (((jold : ℝ) + 1) / (2 : ℝ) ^ Told)
    ((jnative : ℝ) / (2 : ℝ) ^ Tnative) (((jnative : ℝ) + 1) / (2 : ℝ) ^ Tnative)
    hq (div_le_div_of_nonneg_right (by linarith) (hpow Told).le)
    (div_le_div_of_nonneg_right (by linarith) (hpow Tnative).le) hI
  have hdiff : q * (((jnative : ℝ) + 1) / (2 : ℝ) ^ Tnative -
      (jnative : ℝ) / (2 : ℝ) ^ Tnative) =
      ((jold : ℝ) + 1) / (2 : ℝ) ^ Told - (jold : ℝ) / (2 : ℝ) ^ Told := by
    linarith only [hends.1, hends.2]
  convert hdiff using 1 <;> ring

end Submission.Obl.k4_finite_affine_candidate_return
