/- Adapted (namespace renamed) from LOT tree oai_074 (this tree), obligation o062,
session x0511, branch x0511, commit f33e26edad,
Submission/Lib/K4ScalarCoreTools/Simulation/SwitchGlobalMass.lean (an unadmitted lib candidate).
Its own credits follow unchanged. -/

/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarSimulation/SwitchGlobalMass.lean at ccb7071c.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511,
Submission/Obl/k4_scalar_mesh_projection/SwitchGlobalMass.lean.
-/

import Submission.Obl.k4_scalar_capped_heavy_potential.Core.SwitchSupport
import Submission.Obl.k4_scalar_capped_heavy_potential.Core.SwitchFiberMass

namespace Submission.Obl.k4_scalar_capped_heavy_potential.Core.Switching

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4ScalarSwitching.Switching

/-- Integrate the actual endpoint bound over the original start/control
reference. Only the full law's product domination is used: successful
paths and their conditional transition laws are never renormalized. -/
theorem exists_global_switching_mass_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : MvPolynomial (Fin 2) ℝ),
      A.totalDegree ≤ D → B.totalDegree ≤ D →
      ∀ K L κ η ε area b : ℝ, 1 ≤ K → 0 ≤ L → 0 < κ →
        0 < η → η ≤ 1 → 0 ≤ ε → 0 ≤ area → 0 ≤ b →
        ∀ (Θ : Type*) [MeasurableSpace Θ] (ν : Measure Θ) [IsProbabilityMeasure ν]
          (μ : Measure (Θ × (Fin 4 → ℝ))) (S : Set (Θ × (Fin 4 → ℝ)))
          (x : Θ → Fin 2 → ℝ) (v : Θ → Fin 4 → ℝ) (X₀ : Θ → ℝ)
          (ι : Type*) (F : Finset ι) (E : Θ → ι → Set (Fin 2 → ℝ)) (c : Θ → ι → ℝ),
          Measurable x → MeasurableSet S → μ ≤ ENNReal.ofReal L • (ν.prod volume) →
          (∀ z ∈ S, z.2 ∈ Icc (-1 : Fin 4 → ℝ) 1) →
          (∀ z ∈ S, x z.1 ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧
            (∀ i, |v z.1 i| ≤ K) ∧ 1 / K ≤ |v z.1 1 - v z.1 0| ∧
              1 / K ≤ |v z.1 3 - v z.1 2|) →
          ν {θ | x θ ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧
            |eval (x θ) (pderiv 0 B - pderiv 1 A)| ≤ 8 * K ^ 4 * κ} ≤ ENNReal.ofReal b →
          (∀ θ, ∀ i ∈ F, MeasurableSet (E θ i)) →
          (∀ θ, (∑ i ∈ F, volume (E θ i)) ≤ ENNReal.ofReal area) →
          (∀ z ∈ S, ∃ i ∈ F, switchedBaseEndpoint (x z.1) (v z.1) z.2 ∈ E z.1 i ∧
            |X₀ z.1 + eval z.2 (brokenHeight A B (x z.1) (v z.1)) - c z.1 i| ≤ ε) →
          μ S ≤ ENNReal.ofReal (L * (16 * b + η +
            8 * ((D : ℝ) + 2) * area * ε /
              (κ * η ^ (4 * D) / (2 * C * (512 * ((D : ℝ) + 1)) ^ (4 * D))))) := by
  obtain ⟨C, hC, hvolume⟩ := exists_switching_support_volume_constant D
  refine ⟨C, hC, ?_⟩
  intro A B hA hB K L κ η ε area b hK hL hκ hη hη1 hε harea hb
    Θ _ ν _ μ S x v X₀ ι F E c hx hS hdom hbox hdata hbad hE hareaSum hcover
  let Bad : Set Θ := {θ | x θ ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧
    |eval (x θ) (pderiv 0 B - pderiv 1 A)| ≤ 8 * K ^ 4 * κ}
  have hBad : MeasurableSet Bad := (measurableSet_Icc.preimage hx).inter
    (measurableSet_le ((MvPolynomial.continuous_eval _).measurable.comp hx).abs measurable_const)
  let threshold := κ * η ^ (4 * D) / (2 * C * (512 * ((D : ℝ) + 1)) ^ (4 * D))
  have hthreshold : 0 < threshold := by dsimp [threshold]; positivity
  let r := η + 8 * ((D : ℝ) + 2) * area * ε / threshold
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hsection (θ : Θ) (hθ : θ ∉ Bad) :
      volume (Prod.mk θ ⁻¹' S) ≤ ENNReal.ofReal r := by
    by_cases hempty : Prod.mk θ ⁻¹' S = ∅
    · simp only [hempty, measure_empty]
      exact zero_le
    obtain ⟨δ, hδ⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨hstart, hv, hI, hJ⟩ := hdata (θ, δ) hδ
    have hlarge : 8 * K ^ 4 * κ < |eval (x θ) (pderiv 0 B - pderiv 1 A)| :=
      lt_of_not_ge (fun h => hθ ⟨hstart, h⟩)
    have hsm : MeasurableSet (Prod.mk θ ⁻¹' S) :=
      hS.preimage (measurable_const.prodMk measurable_id)
    have hvol := hvolume A B hA hB (x θ) (v θ) K 1 κ η ε (X₀ θ)
      hK zero_lt_one hκ hη hη1 hε hv hI hJ hlarge ι (Prod.mk θ ⁻¹' S)
      F (E θ) (c θ) hsm (fun δ hδ => hbox (θ, δ) hδ) (hE θ)
      (fun δ hδ => hcover (θ, δ) hδ)
    have hvol' : volume (Prod.mk θ ⁻¹' S) ≤ ENNReal.ofReal η +
        ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal area *
          ENNReal.ofReal (4 * ((D : ℝ) + 2) * ε / threshold) := by
      apply hvol.trans
      dsimp only [threshold]
      simp only [one_pow, one_mul, mul_one]
      gcongr
      exact hareaSum θ
    apply hvol'.trans_eq
    rw [← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ)),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * area),
      ← ENNReal.ofReal_add hη.le (by positivity)]
    congr 1
    dsimp only [r]
    ring
  have h := path_mass_le_of_bad_base_and_section_volume ν μ S Bad L b r hL hb hr
    hdom hS hBad hbox hbad hsection
  simpa only [r, add_assoc] using h

end Submission.Obl.k4_scalar_capped_heavy_potential.Core.Switching
