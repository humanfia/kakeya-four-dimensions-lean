/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarSimulation/SwitchCoefficientCurl.lean at ccb7071c.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511,
Submission/Obl/k4_scalar_mesh_projection/SwitchCoefficientCurl.lean.
-/

import Submission.Lib.K4ScalarCoreTools.Simulation.BaseSublevel
import Submission.Lib.K4ScalarCoreTools.Simulation.SwitchGlobalMass

namespace Submission.Lib.K4ScalarCoreTools.Simulation.Switching

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4ScalarSwitching.Switching
open Submission.Lib.K4PolynomialPotential

/-- Quantitative coefficient conservativity from the actual original
joint path law. The start/control law stays fixed, all successful paths
stay unnormalized, and every loss is a degree-dependent fixed power. -/
theorem exists_global_coefficient_curl_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : MvPolynomial (Fin 2) ℝ),
      A.totalDegree ≤ D → B.totalDegree ≤ D →
      ∀ K L M p area ε : ℝ, 1 ≤ K → 1 ≤ L → 1 ≤ M →
        0 < p → p ≤ 1 → 0 ≤ area → 0 ≤ ε →
        ∀ (Θ : Type*) [MeasurableSpace Θ] (ν : Measure Θ) [IsProbabilityMeasure ν]
          (μ : Measure (Θ × (Fin 4 → ℝ))) (S : Set (Θ × (Fin 4 → ℝ)))
          (x : Θ → Fin 2 → ℝ) (v : Θ → Fin 4 → ℝ) (X₀ : Θ → ℝ)
          (ι : Type*) (F : Finset ι) (E : Θ → ι → Set (Fin 2 → ℝ)) (c : Θ → ι → ℝ),
          Measurable x → MeasurableSet S → ν.map x ≤ ENNReal.ofReal M • volume →
          μ ≤ ENNReal.ofReal L • (ν.prod volume) → ENNReal.ofReal p ≤ μ S →
          (∀ z ∈ S, z.2 ∈ Icc (-1 : Fin 4 → ℝ) 1) →
          (∀ z ∈ S, x z.1 ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧
            (∀ i, |v z.1 i| ≤ K) ∧ 1 / K ≤ |v z.1 1 - v z.1 0| ∧
              1 / K ≤ |v z.1 3 - v z.1 2|) →
          (∀ θ, ∀ i ∈ F, MeasurableSet (E θ i)) →
          (∀ θ, (∑ i ∈ F, volume (E θ i)) ≤ ENNReal.ofReal area) →
          (∀ z ∈ S, ∃ i ∈ F, switchedBaseEndpoint (x z.1) (v z.1) z.2 ∈ E z.1 i ∧
            |X₀ z.1 + eval z.2 (brokenHeight A B (x z.1) (v z.1)) - c z.1 i| ≤ ε) →
          ∀ e : Fin 2 →₀ ℕ, |(pderiv 0 B - pderiv 1 A).coeff e| ≤
            C * K ^ 4 * L ^ (6 * D + 1) * M ^ (2 * D) * area * ε / p ^ (6 * D + 1) := by
  obtain ⟨Cbase, hCbase, hdiscard⟩ := exists_base_polynomial_discard_constant D
  obtain ⟨Cpath, hCpath, hmassBound⟩ := exists_global_switching_mass_constant D
  let nb := 2 * D
  let ni := 4 * D
  let Fb : ℝ := (64 * ((D : ℝ) + 1)) ^ nb
  let Fi : ℝ := (512 * ((D : ℝ) + 1)) ^ ni
  have hFb : 0 < Fb := by dsimp [Fb]; positivity
  have hFi : 0 < Fi := by dsimp [Fi]; positivity
  let C : ℝ := 512 * Cbase * Cpath * Fb * Fi * 64 ^ nb * 4 ^ ni * ((D : ℝ) + 2)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro A B hA hB K L M p area ε hK hL hM hp hp1 harea hε
    Θ _ ν _ μ S x v X₀ ι F E c hx hS hbase hdom hmass hbox hdata hE hareaSum hcover e
  have hKp : 0 < K := by linarith
  have hLp : 0 < L := by linarith
  have hMp : 0 < M := by linarith
  let P := pderiv 0 B - pderiv 1 A
  have hP : P.totalDegree ≤ D := by
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · exact (totalDegree_pderiv_le B 0).trans ((Nat.sub_le _ _).trans hB)
    · exact (totalDegree_pderiv_le A 1).trans ((Nat.sub_le _ _).trans hA)
  let k := |P.coeff e|
  by_cases hz : k = 0
  · change k ≤ _
    rw [hz]
    dsimp [C]
    positivity
  have hk : 0 < k := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hz)
  let ηb := p / (64 * L * M)
  let ηi := p / (4 * L)
  have hηb : 0 < ηb := div_pos hp (by positivity)
  have hηi : 0 < ηi := div_pos hp (by positivity)
  have hηb1 : ηb ≤ 1 := by
    dsimp [ηb]
    apply (div_le_one (by positivity)).mpr
    nlinarith
  have hηi1 : ηi ≤ 1 := by dsimp [ηi]; apply (div_le_one (by positivity)).mpr; linarith
  let σ := k * ηb ^ nb / (2 * Cbase * Fb)
  have hσ : 0 < σ := by dsimp [σ]; positivity
  let κ := σ / (8 * K ^ 4)
  have hκ : 0 < κ := div_pos hσ (by positivity)
  have hskew : 8 * K ^ 4 * κ = σ := by dsimp [κ]; field_simp
  have hbad : ν {θ | x θ ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧
      |eval (x θ) (pderiv 0 B - pderiv 1 A)| ≤ 8 * K ^ 4 * κ} ≤
        ENNReal.ofReal (M * ηb) := by
    have h := hdiscard P hP e k ηb hk hηb hηb1 le_rfl Θ ν x (ENNReal.ofReal M) hx hbase
    rw [hskew]
    simpa only [← ENNReal.ofReal_mul hMp.le] using h
  let threshold := κ * ηi ^ ni / (2 * Cpath * Fi)
  have hthreshold : 0 < threshold := by dsimp [threshold]; positivity
  have hmass' := hmassBound A B hA hB K L κ ηi ε area (M * ηb) hK hLp.le
    hκ hηi hηi1 hε harea (mul_nonneg hMp.le hηb.le)
    Θ ν μ S x v X₀ ι F E c hx hS hdom hbox hdata hbad hE hareaSum hcover
  have hreal : p ≤ L * (16 * (M * ηb) + ηi +
      8 * ((D : ℝ) + 2) * area * ε / threshold) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hmass.trans hmass')
  have hbudget : L * (16 * (M * ηb) + ηi) = p / 2 := by
    dsimp [ηb, ηi]
    field_simp
    <;> ring
  have hhalf : p / 2 ≤ (8 * L * ((D : ℝ) + 2) * area * ε) / threshold := by
    have hid : L * (16 * (M * ηb) + ηi + 8 * ((D : ℝ) + 2) * area * ε / threshold) =
        L * (16 * (M * ηb) + ηi) + (8 * L * ((D : ℝ) + 2) * area * ε) / threshold := by ring
    rw [hid, hbudget] at hreal
    linarith
  have hmul := (le_div_iff₀ hthreshold).mp hhalf
  let den : ℝ := 32 * Cbase * Cpath * Fb * Fi * K ^ 4
  have hden : 0 < den := by dsimp [den]; positivity
  have hmul' := mul_le_mul_of_nonneg_right hmul hden.le
  have hcancel : p / 2 * threshold * den = p * k * ηb ^ nb * ηi ^ ni / 2 := by
    dsimp [threshold, κ, σ, den]
    field_simp
    <;> ring
  rw [hcancel] at hmul'
  have hpower : k * p * ηb ^ nb * ηi ^ ni ≤
      512 * Cbase * Cpath * Fb * Fi * K ^ 4 * L * ((D : ℝ) + 2) * area * ε := by
    dsimp [den] at hmul'
    nlinarith
  have hsc := mul_le_mul_of_nonneg_right hpower
    (mul_nonneg (pow_nonneg (by positivity : 0 ≤ 64 * L * M) nb)
      (pow_nonneg (by positivity : 0 ≤ 4 * L) ni))
  have hsum : nb + ni = 6 * D := by dsimp [nb, ni]; omega
  have hleft : k * p * ηb ^ nb * ηi ^ ni * ((64 * L * M) ^ nb * (4 * L) ^ ni) =
      k * p ^ (6 * D + 1) := by
    dsimp [ηb, ηi]
    rw [← hsum, pow_succ, pow_add, div_pow, div_pow]
    field_simp
    <;> ring
  rw [hleft] at hsc
  change k ≤ _
  apply (le_div_iff₀ (pow_pos hp _)).mpr
  convert hsc using 1
  dsimp only [C]
  rw [← hsum, pow_succ, pow_add, mul_pow, mul_pow, mul_pow]
  ring

end Submission.Lib.K4ScalarCoreTools.Simulation.Switching
