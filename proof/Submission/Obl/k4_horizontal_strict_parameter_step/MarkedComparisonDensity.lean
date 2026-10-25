/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/MarkedComparisonDensity.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.MarkedJitter
import Submission.Obl.k4_horizontal_strict_parameter_step.ComparisonCoordinates

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps

noncomputable section

/-- The complete original marked marginal transports through its own colour's
reference chart. The only new factor is the exact time-times-area Jacobian. -/
theorem markedJitter_comparison_density {Ω ι J : Type*} [MeasurableSpace Ω]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) (mark : Ω → ι) (hm : Measurable mark) (colour : ι → J)
    (Z : Ω → Fin 3 → ℝ) (hZ : Measurable Z) {δ : ℝ} (hδ : 0 < δ)
    (F : Finset (Fin 3 → ℤ)) (C : J → ENNReal)
    (hcap : ∀ j q, q ∈ F → μ {p | baseMesh δ (Z p) = q ∧ colour (mark p) = j} ≤
      C j * ENNReal.ofReal (δ ^ 3))
    (v t₀ H p₀ q₀ D : J → ℝ) (hH : ∀ j, 0 < H j) (hD : ∀ j, 0 < D j)
    (j : J) (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : MeasurableSet U) :
    indexedBaseLaw (fun i => meshJitter δ F
      (fun q => (μ.restrict {p | mark p = i}) {p | baseMesh δ (Z p) = q}))
      {p | colour p.1 = j ∧ comparisonCoordinates (v (colour p.1)) (t₀ (colour p.1))
        (H (colour p.1)) (p₀ (colour p.1)) (q₀ (colour p.1)) (D (colour p.1)) p.2 ∈ U} ≤
        (C j * ENNReal.ofReal (H j * D j ^ 2)) * volume U := by
  let f := comparisonCoordinates (v j) (t₀ j) (H j) (p₀ j) (q₀ j) (D j)
  have hf : Measurable f := measurable_comparisonCoordinates _ _ _ _ _ _
  have hb := markedJitter_marginal μ mark hm colour Z hZ hδ F C hcap j (f ⁻¹' U)
    (hU.preimage hf)
  have hevent : {p : ι × (Fin 3 → ℝ) | colour p.1 = j ∧
      comparisonCoordinates (v (colour p.1)) (t₀ (colour p.1)) (H (colour p.1))
        (p₀ (colour p.1)) (q₀ (colour p.1)) (D (colour p.1)) p.2 ∈ U} =
      {p | colour p.1 = j ∧ p.2 ∈ f ⁻¹' U} := by
    ext p
    constructor
    · rintro ⟨hp, hx⟩
      exact ⟨hp, by simpa only [hp, f, mem_preimage] using hx⟩
    · rintro ⟨hp, hx⟩
      exact ⟨hp, by simpa only [hp, f, mem_preimage] using hx⟩
  rw [hevent]
  apply hb.trans_eq
  rw [← Measure.map_apply hf hU, map_comparisonCoordinates_volume (v j) (t₀ j)
    (p₀ j) (q₀ j) (hH j) (hD j), Measure.smul_apply, smul_eq_mul]
  exact (mul_assoc _ _ _).symm

end

end Submission.Obl.k4_horizontal_strict_parameter_step
