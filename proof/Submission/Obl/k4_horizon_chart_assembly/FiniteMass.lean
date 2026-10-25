import Submission.Obl.k4_horizon_chart_assembly.WeightedMass
import Submission.Obl.k4_horizon_chart_assembly.SplitInterfaces

namespace Submission.Obl.k4_horizon_chart_assembly

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

/-- Extend a family on the actual finite blocks and labels to all formal
indices; the fallback keeps out-of-range residuals empty. -/
def extendNativeGroup {α : Type*} {J : ℕ} {S : Finset ((Fin 2 → ℤ) × ℤ)}
    (z : α) (F : Fin J × ↥S → α) (j : ℕ) (Γ : (Fin 2 → ℤ) × ℤ) : α := by
  classical
  exact if hj : j < J then if hΓ : Γ ∈ S then F (⟨j, hj⟩, ⟨Γ, hΓ⟩) else z else z

theorem extendNativeGroup_apply {α : Type*} {J : ℕ} {S : Finset ((Fin 2 → ℤ) × ℤ)}
    (z : α) (F : Fin J × ↥S → α) (j : Fin J) (Γ : ↥S) :
    extendNativeGroup z F j.val Γ.val = F (j, Γ) := by
  classical
  simp only [extendNativeGroup, dif_pos j.isLt, dif_pos Γ.property]

/-- Reindexing the finite world mass sum has no loss. -/
theorem sum_extendNativeGroup {α : Type*} [AddCommMonoid α] {J : ℕ}
    {S : Finset ((Fin 2 → ℤ) × ℤ)} (F : Fin J × ↥S → α) :
    (∑ j ∈ Finset.range J, ∑ Γ ∈ S, extendNativeGroup 0 F j Γ) = ∑ g, F g := by
  classical
  rw [Finset.sum_range]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_coe_sort]
  exact Finset.sum_congr rfl (fun Γ _ => extendNativeGroup_apply 0 F j Γ)

/-- The native cellwise multiplicity has the stated universal cubic bound. -/
theorem nativeMultiplicity_le {K : ℝ} (hK : 1 ≤ K) :
    nativeMultiplicity K ≤ 26499 * K ^ 3 := by
  have hK₀ : 0 ≤ K := by linarith
  have h1 : (4 * K + 7) ^ 2 ≤ (11 * K) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h2 : 212 * K + 7 ≤ 219 * K := by linarith
  calc
    _ ≤ (11 * K) ^ 2 * (219 * K) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = _ := by ring

/-- A fixed lower mesh power suffices for cellwise decoding at every sample. -/
theorem decoding_mesh_bound {H q a : ℝ} {D : ℕ}
    (hH : 2 ≤ H) (hq : 0 ≤ q) (hqa : 8 * q ≤ a) (hD : H ^ 17 ≤ (D : ℝ)) :
    4131 * H * (3 * H + 1) ^ 2 * (q / D) ≤ a := by
  have hH₀ : 0 < H := by linarith
  have hD₀ : 0 < (D : ℝ) := (pow_pos hH₀ 17).trans_le hD
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hH 14
  norm_num at hp
  have hcoef : 4131 * H * (3 * H + 1) ^ 2 ≤ 8 * (D : ℝ) := by
    calc
      _ ≤ 4131 * H * (4 * H) ^ 2 := by
        gcongr
        linarith
      _ = 66096 * H ^ 3 := by ring
      _ ≤ (8 * H ^ 14) * H ^ 3 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 8 * H ^ 17 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hD (by norm_num)
  calc
    _ = (4131 * H * (3 * H + 1) ^ 2) * q / D := by ring
    _ ≤ (8 * (D : ℝ)) * q / D :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hq) hD₀.le
    _ = 8 * q := by field_simp
    _ ≤ _ := hqa

/-- The light-mass term uses the original whole world cells exactly. -/
theorem weighted_worldLight_eq {W D : ℕ} (ω : Fin W → ℝ)
    (ν : Fin W → Measure Trajectory) (E : Fin W → Set Incidence) (B : Fin W → ℝ)
    (a q θ : ℝ) :
    (∑ γ, ENNReal.ofReal (ω γ) * ((ν γ).prod volume) (worldLight (ν γ) (E γ) (B γ) a q θ D)) =
      lightMass W ω ν E B a (q / D) θ := by
  apply Finset.sum_congr rfl
  intro γ _
  congr 2
  have heq := lightSet_eq_worldCell (ν γ) (E γ) (B γ) a θ (q / D) (q / D)
  have hpow : θ * (q / (D : ℝ)) * (q / D) ^ 2 = θ * (q / D) ^ 3 := by ring
  simpa only [lightMass, worldLight, hpow] using heq.symm

/-- The per-world balance sums with its original probability weights. -/
theorem weighted_world_mass_balance {W D : ℕ} (ω : Fin W → ℝ)
    (ν : Fin W → Measure Trajectory) (E : Fin W → Set Incidence) (B : Fin W → ℝ)
    (a q θ σ loss : ℝ) (Sel : Fin W → ENNReal)
    (hω₀ : ∀ γ, 0 ≤ ω γ) (hω₁ : ∑ γ, ω γ = 1)
    (hworld : ∀ γ, ((ν γ).prod volume) (E γ) ≤ Sel γ +
      ((ν γ).prod volume) (worldLight (ν γ) (E γ) (B γ) a q θ D) + ENNReal.ofReal σ +
      ENNReal.ofReal loss * ((ν γ).prod volume) (E γ)) :
    (∑ γ, ENNReal.ofReal (ω γ) * ((ν γ).prod volume) (E γ)) ≤
      (∑ γ, ENNReal.ofReal (ω γ) * Sel γ) +
      lightMass W ω ν E B a (q / D) θ + ENNReal.ofReal σ +
      ENNReal.ofReal loss * (∑ γ, ENNReal.ofReal (ω γ) * ((ν γ).prod volume) (E γ)) := by
  have hsumω : (∑ γ, ENNReal.ofReal (ω γ)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun γ _ => hω₀ γ), hω₁, ENNReal.ofReal_one]
  calc
    _ ≤ ∑ γ, ENNReal.ofReal (ω γ) * (Sel γ +
        ((ν γ).prod volume) (worldLight (ν γ) (E γ) (B γ) a q θ D) + ENNReal.ofReal σ +
        ENNReal.ofReal loss * ((ν γ).prod volume) (E γ)) :=
      Finset.sum_le_sum (fun γ _ => mul_le_mul_right (hworld γ) _)
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib]
      rw [weighted_worldLight_eq, ← Finset.sum_mul, hsumω, one_mul]
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun γ _ => by ring)

end
end Submission.Obl.k4_horizon_chart_assembly
