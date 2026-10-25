-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.ConditionalAngularPalette
import Submission.Obl.k4_finite_affine_parent_sources.SourcePalette

namespace Submission.Obl.k4_finite_affine_parent_sources.ReferencePalette

open MeasureTheory Set Submission.Lib.K4AngularCharge
open scoped ENNReal

noncomputable section

/-- Construct one parent palette from original angular/share masks and
one predeletion parent reference set. It has the native Frostman bound,
dominates enlarged old bins, and controls every later code numerator. -/
theorem exists_masked_parent_palette {Ω : Type} {O ι : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace O] [MeasurableEq O]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (obs : Ω → O) (hobs : Measurable obs)
    (velocity : Ω → EuclideanSpace ℝ (Fin 2))
    (lam : Measure O) [SigmaFinite lam] (g : O → ℝ≥0∞) (hg : Measurable g)
    (hmap : μ.map obs = lam.withDensity g)
    (G : ℝ → O × (Fin 2 → ℤ) → ℝ≥0∞)
    (F R : Set Ω) (hF : MeasurableSet F) (hR : μ R ≠ 0)
    (U : Ω → ι) (hU : Measurable U) (center : ι → ℝ)
    (b : Ω → Fin 2 → ℝ) (hb : Measurable (fun z => b z 0))
    (offset : Fin 2 → ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (n : ℕ) (N unit L S K H mesh blur fL eG ePure eShare eParent : ℝ)
    (depth fine : ℝ → ℝ)
    (hN : 1 ≤ N) (hNt : 1 ≤ N ^ (unit * L)) (hS : 0 ≤ S) (hH : 0 ≤ H)
    (hblur : 0 < blur) (hsmall : 2 * blur ≤ (N ^ (unit * L)) ^ (-(n : ℝ)))
    (hclose : ∀ᵐ z ∂nuE μ R, |b z 0 - center (U z)| ≤ blur / 2)
    (hfloor : ENNReal.ofReal (N ^ (-eParent)) * μ F ≤ μ R)
    (hmajor : ∀ e, |M e 0| ≤ H)
    (hcoord : ∀ z ∈ F, ∀ e, velocity z e = offset e + ∑ i, M e i * b z i)
    (hbound : ∀ z ∈ F, |b z 1| ≤ H)
    (hbudget : 6 * ((6 * H + 2) ^ 2 * N ^ (eG + ePure + eShare + eParent)) *
      N ^ (S * mesh) ≤ K)
    (hdepth : ∀ v, (n : ℝ)⁻¹ ≤ v → v ≤ n → unit * L * v - mesh ≤ depth v)
    (hfine : ∀ v, (n : ℝ)⁻¹ ≤ v → v ≤ n →
      0 < fine v ∧ (N ^ (unit * L)) ^ (-v) ≤ fine v)
    (hminor : ∀ v, (n : ℝ)⁻¹ ≤ v → v ≤ n → ∀ e,
      |M e 1| ≤ (N ^ (unit * L)) ^ (-v))
    (hcell : ∀ v, (n : ℝ)⁻¹ ≤ v → v ≤ n →
      Measurable (fun z => fun e : Fin 2 => ⌊velocity z e / fine v⌋))
    (hG : ∀ v, (n : ℝ)⁻¹ ≤ v → v ≤ n → Measurable (G v))
    (hmapG : ∀ v, (n : ℝ)⁻¹ ≤ v → v ≤ n →
      μ.map (fun z => (obs z, fun e : Fin 2 => ⌊velocity z e / fine v⌋)) =
        (lam.prod Measure.count).withDensity (G v))
    (hmask : ∀ v, (n : ℝ)⁻¹ ≤ v → v ≤ n →
      R ⊆ F ∩ {z | ENNReal.ofReal (N ^ (-eShare)) ≤ labelShare μ obs F z} ∩
        {z | G v (obs z, fun e : Fin 2 => ⌊velocity z e / fine v⌋) ≤
          ENNReal.ofReal (N ^ (-fL - S * depth v + eG)) ∧
            ENNReal.ofReal (N ^ (-fL - ePure)) ≤ g (obs z)}) :
    ∃ π : Measure ℝ, IsProbabilityMeasure π ∧
      (∀ v, (n : ℝ)⁻¹ ≤ v → v ≤ n → ∀ e : ℤ,
        π {w | ⌊w / ((N ^ (unit * L)) ^ (-v))⌋ = e} ≤
          ENNReal.ofReal (K * (N ^ (unit * L)) ^ (-S * v))) ∧
      (∀ a c : ℝ, 2 * blur ≤ c - a →
        nuE μ R ((fun z => b z 0) ⁻¹' Icc (a - blur / 2) (c + blur / 2)) ≤
          4 * π (Ico a c)) ∧
      (∀ (ρ : Measure Ω), ρ ≤ nuE μ R → ∀ (P : Set Ω) (C : ℝ≥0∞)
        (width : ℝ), 2 * blur ≤ width →
        (∀ i, ρ (P ∩ U ⁻¹' {i}) ≤ C * nuE μ R (U ⁻¹' {i})) → ∀ e : ℤ,
        ρ (P ∩ {z | ⌊b z 0 / width⌋ = e}) ≤
          4 * C * π {w | ⌊w / width⌋ = e}) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  letI : IsProbabilityMeasure (nuE μ R) := nuE_isProb μ R hR (measure_ne_top _ _)
  have hclose' : ∀ᵐ z ∂nuE μ R, |b z 0 - center (U z)| ≤ blur := by
    filter_upwards [hclose] with z hz
    exact hz.trans (by linarith)
  refine ⟨law (nuE μ R) U center blur, probability _ U hU center hblur, ?_, ?_, ?_⟩
  · intro v hv hvn e
    have hw : 2 * blur ≤ (N ^ (unit * L)) ^ (-v) :=
      hsmall.trans (Real.rpow_le_rpow_of_exponent_le hNt (by linarith))
    apply frostman_cap (nuE μ R) U hU (fun z => b z 0) center hN
      (by positivity) hS hblur hw hclose' (hdepth v hv hvn) hbudget
    intro j
    have hc := conditioned_linear_native_palette_cap μ obs hobs velocity (fine v)
      (hcell v hv hvn) lam g hg hmap (G v) (hG v hv hvn) (hmapG v hv hvn)
      F R hF hR (ENNReal.ofReal (N ^ (-eShare)))
      (ENNReal.ofReal (N ^ (-fL - S * depth v + eG)))
      (ENNReal.ofReal (N ^ (-fL - ePure))) (ENNReal.ofReal (N ^ (-eParent)))
      (by positivity) (by positivity) (by positivity) ENNReal.ofReal_ne_top hfloor
      (hmask v hv hvn) b hb offset M H ((N ^ (unit * L)) ^ (-v)) hH
      (by positivity) (hfine v hv hvn).1 (hfine v hv hvn).2 hmajor
      (hminor v hv hvn) hcoord hbound j
    rw [original_angular_reference_coefficient hN0] at hc
    exact hc
  · intro a c hw
    exact enlarged_interval (nuE μ R) U hU (fun z => b z 0) center hblur hw hclose
  · intro ρ hρ P C width hw hc e
    exact joint_bin_cap (nuE μ R) ρ U (fun z => b z 0) center hblur hw P C
      ((Measure.absolutelyContinuous_of_le hρ).ae_le hclose') hc e

end
end Submission.Obl.k4_finite_affine_parent_sources.ReferencePalette
