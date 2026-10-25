/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarSimulation/SwitchMassCurl.lean at ccb7071c.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit 778c2ed,
Submission/Obl/k4_scalar_mesh_projection/SwitchMassCurl.lean.
-/

import Submission.Lib.K4ScalarCoreTools.Simulation.SwitchSupport

namespace Submission.Lib.K4ScalarCoreTools.Simulation.Switching

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4ScalarSwitching.Switching

/-- A positive original path mass, its Lebesgue ceiling and its finite
endpoint support force a quantitative curl bound. All losses are fixed
powers, with constants depending only on the polynomial degree. -/
theorem exists_original_path_mass_curl_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : MvPolynomial (Fin 2) ℝ),
      A.totalDegree ≤ D → B.totalDegree ≤ D →
      ∀ (x : Fin 2 → ℝ) (v : Fin 4 → ℝ) (K L p area ε X₀ : ℝ),
        1 ≤ K → 1 ≤ L → 0 < p → p ≤ 1 → 0 ≤ area → 0 ≤ ε →
        (∀ i, |v i| ≤ K) → 1 / K ≤ |v 1 - v 0| → 1 / K ≤ |v 3 - v 2| →
        ∀ (ι : Type*) (μ : Measure (Fin 4 → ℝ)) (S : Set (Fin 4 → ℝ))
          (F : Finset ι) (E : ι → Set (Fin 2 → ℝ)) (c : ι → ℝ),
          μ ≤ ENNReal.ofReal L • volume → ENNReal.ofReal p ≤ μ S →
          MeasurableSet S → S ⊆ Icc (-1 : Fin 4 → ℝ) 1 →
          (∀ i ∈ F, MeasurableSet (E i)) →
          (∑ i ∈ F, volume (E i)) ≤ ENNReal.ofReal area →
          (∀ δ ∈ S, ∃ i ∈ F, switchedBaseEndpoint x v δ ∈ E i ∧
            |X₀ + eval δ (brokenHeight A B x v) - c i| ≤ ε) →
          |eval x (pderiv 0 B - pderiv 1 A)| ≤
            C * K ^ 4 * L ^ (4 * D + 1) * area * ε / p ^ (4 * D + 1) := by
  obtain ⟨C₀, hC₀, hvolume⟩ := exists_switching_support_volume_constant D
  let n := 4 * D
  let F₀ : ℝ := (512 * ((D : ℝ) + 1)) ^ n
  have hF₀ : 0 < F₀ := by dsimp [F₀]; positivity
  let C : ℝ := 512 * C₀ * F₀ * 2 ^ n * ((D : ℝ) + 2)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro A B hA hB x v K L p area ε X₀ hK hL hp hp1 harea hε hv hI hJ
    ι μ S F E c hdom hmass hS hbox hE hbase hcover
  have hKp : 0 < K := by linarith
  have hLp : 0 < L := by linarith
  let curl := |eval x (pderiv 0 B - pderiv 1 A)|
  by_cases hz : curl = 0
  · change curl ≤ _
    rw [hz]
    dsimp [C]
    positivity
  have hcurlp : 0 < curl := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hz)
  let κ := curl / (16 * K ^ 4)
  have hκ : 0 < κ := div_pos hcurlp (by positivity)
  have hlarge : 8 * K ^ 4 * κ < curl := by
    have hid : 8 * K ^ 4 * κ = curl / 2 := by
      dsimp [κ]
      field_simp
      <;> ring
    rw [hid]
    linarith
  let η := p / (2 * L)
  have hη : 0 < η := div_pos hp (by positivity)
  have hη1 : η ≤ 1 := by dsimp [η]; apply (div_le_one (by positivity)).mpr; linarith
  let threshold := κ * η ^ n / (2 * C₀ * F₀)
  have hthreshold : 0 < threshold := by dsimp [threshold]; positivity
  have hvol := hvolume A B hA hB x v K 1 κ η ε X₀ hK zero_lt_one
    hκ hη hη1 hε hv hI hJ hlarge ι S F E c hS hbox hE hcover
  have hvol' : volume S ≤ ENNReal.ofReal η + ENNReal.ofReal (2 : ℝ) *
      ENNReal.ofReal area * ENNReal.ofReal (4 * ((D : ℝ) + 2) * ε / threshold) := by
    apply hvol.trans
    dsimp only [threshold, F₀, n]
    simp only [one_pow, one_mul, mul_one]
    gcongr
  have hdomS : μ S ≤ ENNReal.ofReal L * volume S := by
    simpa only [Measure.smul_apply, smul_eq_mul] using Measure.le_iff.mp hdom S hS
  have hmass' := hmass.trans (hdomS.trans (mul_le_mul_of_nonneg_left hvol' bot_le))
  rw [← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ)),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * area),
    ← ENNReal.ofReal_add hη.le (by positivity), ← ENNReal.ofReal_mul hLp.le] at hmass'
  have hreal : p ≤ L * (η + 2 * area * (4 * ((D : ℝ) + 2) * ε / threshold)) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hmass'
  have hLη : L * η = p / 2 := by dsimp [η]; field_simp
  have hhalf : p / 2 ≤ (8 * L * ((D : ℝ) + 2) * area * ε) / threshold := by
    have hid : L * (η + 2 * area * (4 * ((D : ℝ) + 2) * ε / threshold)) =
        L * η + (8 * L * ((D : ℝ) + 2) * area * ε) / threshold := by ring
    rw [hid, hLη] at hreal
    linarith
  have hmul := (le_div_iff₀ hthreshold).mp hhalf
  have hden : 0 < 2 * C₀ * F₀ := by positivity
  have hmul' := mul_le_mul_of_nonneg_right hmul hden.le
  have hcancel : p / 2 * threshold * (2 * C₀ * F₀) = p * κ * η ^ n / 2 := by
    dsimp [threshold]
    field_simp
  rw [hcancel] at hmul'
  have hpower : κ * p * η ^ n ≤ 32 * C₀ * F₀ * L * ((D : ℝ) + 2) * area * ε := by
    nlinarith
  have hscale := mul_le_mul_of_nonneg_right hpower (pow_nonneg (by positivity : 0 ≤ 2 * L) n)
  have hleft : κ * p * η ^ n * (2 * L) ^ n = κ * p ^ (n + 1) := by
    dsimp [η]
    rw [div_pow, pow_succ]
    field_simp
  rw [hleft] at hscale
  have hκbound : κ ≤
      (32 * C₀ * F₀ * 2 ^ n * ((D : ℝ) + 2) * L ^ (n + 1) * area * ε) / p ^ (n + 1) := by
    apply (le_div_iff₀ (pow_pos hp _)).mpr
    convert hscale using 1 <;> rw [mul_pow, pow_succ] <;> ring
  have hcurl : curl = 16 * K ^ 4 * κ := by dsimp [κ]; field_simp
  change curl ≤ _
  rw [hcurl]
  apply (mul_le_mul_of_nonneg_left hκbound (by positivity : 0 ≤ 16 * K ^ 4)).trans_eq
  dsimp [C, n]
  ring

end Submission.Lib.K4ScalarCoreTools.Simulation.Switching
