/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit 2e65ac82f715df53d854782d6e862452630b9dde,
Submission/Obl/k4_scalar_mesh_projection/StarRecovery.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Submission.Lib.K4ScalarActualSwitching.StarSupport
import Submission.Lib.K4ScalarActualSwitching.PaletteConditioning
import Submission.Lib.K4ScalarActualSwitching.OriginalBaseArea

namespace Submission.Lib.K4ScalarActualSwitching

open Submission.Lib.K4ScalarSwitching

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

theorem star_good_separated {Ω : Type*} (control : Ω → ℝ) (r : ℝ)
    (z : (Ω × Ω) × (Ω × Ω)) (hz : z ∉ starBad control r) :
    Pairwise (fun i j : Fin 4 => r ≤ |control (starSample z i) - control (starSample z j)|) := by
  have h (k : Fin 6) : r ≤ |control (starPair k z).1 - control (starPair k z).2| := by
    apply not_lt.mp
    intro hk
    apply hz
    exact mem_iUnion.mpr ⟨k, hk⟩
  have h₀ := h 0
  have h₁ := h 1
  have h₂ := h 2
  have h₃ := h 3
  have h₄ := h 4
  have h₅ := h 5
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [starSample, starPair, abs_sub_comm]

/-- A measurable jet event containing every separated conditional star
has positive area charged against the unchanged original base ceiling.
No measurable choice of the four line witnesses is required. -/
theorem conditional_star_base_area {Ω Q B : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace Q] [StandardBorelSpace Q] [Countable Q] [MeasurableSingletonClass Q]
    [MeasurableSpace B]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (state : Ω → Q) (hstate : Measurable state)
    (control : Ω → ℝ) (hcontrol : Measurable control)
    (π : Measure ℝ) (K p : ENNReal) (r : ℝ)
    (hrect : ∀ q (A : Set ℝ), MeasurableSet A →
      μ {ω | state ω = q ∧ control ω ∈ A} ≤ K * μ (state ⁻¹' {q}) * π A)
    (hthin : ∀ w : ℝ, π {v | |v - w| < r} ≤ p)
    (hsmall : 6 * (K * p) ≤ 1 / 2)
    (P : Ω → Prop) (hPm : MeasurableSet {ω | P ω}) (hP : ∀ᵐ ω ∂μ, P ω)
    (R : Ω → Ω → Prop) (hRm : MeasurableSet {z : Ω × Ω | R z.1 z.2})
    (hcert : ∀ ω z, state z = state ω → R ω z)
    (base : Ω → B) (hbase : Measurable base) (σ : Measure B) (C : ℝ) (hC : 0 < C)
    (hcap : μ.map base ≤ ENNReal.ofReal C • σ) (S : Set B) (hS : MeasurableSet S)
    (htest : ∀ ω (z : (Ω × Ω) × (Ω × Ω)), P ω → (∀ i : Fin 4, P (starSample z i)) →
      (∀ i : Fin 4, R ω (starSample z i)) →
      Pairwise (fun i j : Fin 4 => r ≤ |control (starSample z i) - control (starSample z j)|) →
      base ω ∈ S) :
    ENNReal.ofReal ((μ univ).toReal / (2 * C)) ≤ σ S := by
  let kernel := conditionalResampling μ state hstate
  letI : IsMarkovKernel kernel := conditionalResampling_markov μ state hstate
  letI := starKernel_markov kernel
  let θ := μ ⊗ₘ starKernel kernel
  let ρ := θ.restrict (Prod.snd ⁻¹' (starBad control r)ᶜ)
  have hpalette := conditionalResampling_palette_le μ state hstate control hcontrol π K hrect
  have hmass := star_retained_mass μ kernel control hcontrol π K p r hpalette hthin
  have hsupport := conditional_star_ae_support μ state hstate control r P hPm hP R hRm hcert
  have hgood : ∀ᵐ z ∂ρ, z.2 ∉ starBad control r :=
    ae_restrict_mem ((measurableSet_starBad control hcontrol r).compl.preimage measurable_snd)
  have hquery : ∀ᵐ z ∂ρ, base z.1 ∈ S := by
    filter_upwards [hsupport, hgood] with z hs hg
    exact htest z.1 z.2 hs.1 hs.2.1 hs.2.2 (star_good_separated control r z.2 hg)
  have hhalf : μ univ / 2 ≤ ρ univ :=
    half_mass_of_small_relative_loss (μ univ) (ρ univ) (6 * (K * p))
      (measure_ne_top μ univ) hsmall hmass.2
  have hhalfReal : ENNReal.ofReal ((μ univ).toReal / 2) ≤ ρ univ := by
    simpa [ENNReal.ofReal_div_of_pos, ENNReal.ofReal_toReal (measure_ne_top μ univ)] using hhalf
  simpa only [div_div] using original_base_area_floor μ ρ hmass.1 base hbase σ C
    ((μ univ).toReal / 2) hC hcap S hS hquery hhalfReal

end Submission.Lib.K4ScalarActualSwitching
