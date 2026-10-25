import Submission.Obl.k4_scalar_grid_density_extension.GridTypical

/-! Typical profiles under uniformly controlled power factors. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_native_grid_profile_extension.Profiles
open Submission.Obl.k4_scalar_grid_density_extension

/-- Multiplication by a quantity of exponent `a`, uniformly on retained
incidences, subtracts `a` from the typical density exponent. -/
theorem typical_of_power_comparison {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (N : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (μ : (k : ℕ) → Measure (Ω k))
    (old current : (k : ℕ) → Ω k → ENNReal) (e a : ℝ)
    (hold : HasTypicalDensity N μ old e)
    (hcompare : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ᵐ x ∂μ k,
      ENNReal.ofReal (N k ^ (a - ε)) * old k x ≤ current k x ∧
      current k x ≤ ENNReal.ofReal (N k ^ (a + ε)) * old k x) :
    HasTypicalDensity N μ current (e - a) := by
  intro τ hτ
  have hτ3 : 0 < τ / 3 := by positivity
  obtain ⟨c, hc, hev⟩ := hold (τ / 3) hτ3
  refine ⟨c, hc, ?_⟩
  filter_upwards [hev, hcompare (τ / 3) hτ3] with k hk hcmp
  have hNk : 0 < N k := by linarith [hN k]
  have hlow : ENNReal.ofReal (N k ^ (-(e - a) - τ)) ≤
      ENNReal.ofReal (N k ^ (a - τ / 3)) * ENNReal.ofReal (N k ^ (-e - τ / 3)) := by
    rw [ofReal_rpow_mul_rpow hNk]
    apply ofReal_rpow_le_ofReal_rpow (hN k)
    linarith
  have hhigh : ENNReal.ofReal (N k ^ (a + τ / 3)) *
      ENNReal.ofReal (N k ^ (-e + τ / 3)) ≤ ENNReal.ofReal (N k ^ (-(e - a) + τ)) := by
    rw [ofReal_rpow_mul_rpow hNk]
    apply ofReal_rpow_le_ofReal_rpow (hN k)
    linarith
  refine le_trans (measure_mono_ae ?_) hk
  filter_upwards [hcmp] with x hx hbad
  by_contra hnot
  simp only [not_or, not_lt] at hnot
  rcases hbad with hbad | hbad
  · exact (not_lt_of_ge (hlow.trans ((mul_le_mul' le_rfl hnot.1).trans hx.1)) hbad).elim
  · exact (not_lt_of_ge (hx.2.trans ((mul_le_mul' le_rfl hnot.2).trans hhigh)) hbad).elim

/-- The joint laws of a finite world family can be treated as one incidence law
while retaining the world label. -/
noncomputable def worldLaw {Ω : Type*} [MeasurableSpace Ω] {W : ℕ}
    (ω : Fin W → ENNReal) (μ : Fin W → Measure Ω) : Measure (Fin W × Ω) :=
  ∑ b, ω b • (μ b).map (fun p => (b, p))

theorem worldLaw_apply {Ω : Type*} [MeasurableSpace Ω] {W : ℕ}
    (ω : Fin W → ENNReal) (μ : Fin W → Measure Ω) (A : Set (Fin W × Ω)) :
    worldLaw ω μ A = ∑ b, ω b * μ b {p | (b, p) ∈ A} := by
  simp only [worldLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [(measurableEmbedding_prodMk_left b).map_apply]
  rfl

theorem worldLaw_univ {Ω : Type*} [MeasurableSpace Ω] {W : ℕ}
    (ω : Fin W → ENNReal) (μ : Fin W → Measure Ω) :
    worldLaw ω μ univ = ∑ b, ω b * μ b univ := by
  rw [worldLaw_apply]
  simp only [Set.mem_univ, Set.ofPred_true]


/-- Power-small relative-comparison exceptions do not change a typical profile,
apart from the fixed power factor. -/
theorem typical_of_power_tails {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (N : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (Ω k))
    (old current : (k : ℕ) → Ω k → ENNReal) (e a : ℝ)
    (hold : HasTypicalDensity N μ old e)
    (hlo : ∀ ε : ℝ, 0 < ε → IsPowerSmall N (fun k =>
      μ k {x | current k x < ENNReal.ofReal (N k ^ (a - ε)) * old k x}))
    (hhi : ∀ ε : ℝ, 0 < ε → IsPowerSmall N (fun k =>
      μ k {x | ENNReal.ofReal (N k ^ (a + ε)) * old k x < current k x})) :
    HasTypicalDensity N μ current (e - a) := by
  intro τ hτ
  have hτ3 : 0 < τ / 3 := by positivity
  let A : (k : ℕ) → Set (Ω k) := fun k =>
    {x | old k x < ENNReal.ofReal (N k ^ (-e - τ / 3)) ∨
      ENNReal.ofReal (N k ^ (-e + τ / 3)) < old k x}
  let L : (k : ℕ) → Set (Ω k) := fun k =>
    {x | current k x < ENNReal.ofReal (N k ^ (a - τ / 3)) * old k x}
  let H : (k : ℕ) → Set (Ω k) := fun k =>
    {x | ENNReal.ofReal (N k ^ (a + τ / 3)) * old k x < current k x}
  have hA : IsPowerSmall N (fun k => μ k (A k)) := hold (τ / 3) hτ3
  apply ((hA.add hNt (hlo (τ / 3) hτ3)).add hNt (hhi (τ / 3) hτ3)).mono
  apply Eventually.of_forall
  intro k
  have hNk : 0 < N k := by linarith [hN k]
  have hlow : ENNReal.ofReal (N k ^ (-(e - a) - τ)) ≤
      ENNReal.ofReal (N k ^ (a - τ / 3)) * ENNReal.ofReal (N k ^ (-e - τ / 3)) := by
    rw [ofReal_rpow_mul_rpow hNk]
    apply ofReal_rpow_le_ofReal_rpow (hN k)
    linarith
  have hhigh : ENNReal.ofReal (N k ^ (a + τ / 3)) *
      ENNReal.ofReal (N k ^ (-e + τ / 3)) ≤ ENNReal.ofReal (N k ^ (-(e - a) + τ)) := by
    rw [ofReal_rpow_mul_rpow hNk]
    apply ofReal_rpow_le_ofReal_rpow (hN k)
    linarith
  refine le_trans (measure_mono ?_) (measure_union_le₃ (μ k) (A k) (L k) (H k))
  intro x hx
  by_cases hAx : x ∈ A k
  · exact Or.inl (Or.inl hAx)
  by_cases hLx : x ∈ L k
  · exact Or.inl (Or.inr hLx)
  by_cases hHx : x ∈ H k
  · exact Or.inr hHx
  simp only [A, L, H, mem_ofPred_eq, not_or, not_lt] at hAx hLx hHx
  rcases hx with hx | hx
  · exact (not_lt_of_ge (hlow.trans ((mul_le_mul' le_rfl hAx.1).trans hLx)) hx).elim
  · exact (not_lt_of_ge (hHx.trans ((mul_le_mul' le_rfl hAx.2).trans hhigh)) hx).elim

/-- Almost-sure statements can be checked in each original world separately. -/
theorem ae_worldLaw {Ω : Type*} [MeasurableSpace Ω] {W : ℕ}
    (ω : Fin W → ENNReal) (μ : Fin W → Measure Ω) (P : Fin W × Ω → Prop)
    (hP : ∀ b, ∀ᵐ p ∂μ b, P (b, p)) : ∀ᵐ z ∂worldLaw ω μ, P z := by
  rw [ae_iff, worldLaw_apply]
  apply Finset.sum_eq_zero
  intro b _
  have hz : μ b {p | ¬ P (b, p)} = 0 := by simpa only [ae_iff] using hP b
  change ω b * μ b {p | ¬ P (b, p)} = 0
  rw [hz, mul_zero]

/-- Probability weights and subprobability selected laws give total mass at
most one. -/
theorem worldLaw_mass_le_one {Ω : Type*} [MeasurableSpace Ω] {W : ℕ}
    (ω : Fin W → ENNReal) (μ : Fin W → Measure Ω)
    (hω : ∑ b, ω b ≤ 1) (hm : ∀ b, μ b univ ≤ 1) : worldLaw ω μ univ ≤ 1 := by
  rw [worldLaw_univ]
  calc
    _ ≤ ∑ b, ω b * 1 := Finset.sum_le_sum fun b _ => mul_le_mul' le_rfl (hm b)
    _ ≤ 1 := by simpa only [mul_one] using hω

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
