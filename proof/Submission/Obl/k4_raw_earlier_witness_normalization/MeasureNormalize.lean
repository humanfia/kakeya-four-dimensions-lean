import Submission.Obl.k4_raw_earlier_witness_normalization.Interface
open MeasureTheory
open scoped ENNReal BigOperators
namespace Submission.Obl.k4_raw_earlier_witness_normalization

noncomputable def normalizedMap {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ρ : Measure X) (f : X → Y) : Measure Y :=
  (ρ Set.univ)⁻¹ • ρ.map f

theorem normalizedMap_probability {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ρ : Measure X) (f : X → Y) (hf : Measurable f)
    (hm0 : 0 < ρ Set.univ) (hmt : ρ Set.univ < ⊤) :
    IsProbabilityMeasure (normalizedMap ρ f) := by
  constructor
  rw [normalizedMap, Measure.smul_apply, Measure.map_apply hf MeasurableSet.univ,
    Set.preimage_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hm0.ne' hmt.ne

theorem weight_smul_normalizedMap {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ρ : Measure X) (f : X → Y) (w : ENNReal)
    (hm0 : 0 < ρ Set.univ) (hmt : ρ Set.univ < ⊤) :
    (w * ρ Set.univ) • normalizedMap ρ f = w • ρ.map f := by
  rw [normalizedMap, smul_smul, mul_assoc, ENNReal.mul_inv_cancel hm0.ne' hmt.ne,
    mul_one]

theorem weighted_maps_le_normalized {X Y A : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace A] {ι : Type*} [Fintype ι]
    (ρ : Measure X) (μ : ι → Measure A) (z : ι → A → X) (R : ι → ENNReal)
    (w : ENNReal) (f : X → Y) (hf : Measurable f) (hz : ∀ i, Measurable (z i))
    (hm0 : 0 < ρ Set.univ) (hmt : ρ Set.univ < ⊤)
    (hdom : (∑ i, R i • (μ i).map (z i)) ≤ w • ρ) :
    (∑ i, R i • (μ i).map (f ∘ z i)) ≤
      (w * ρ Set.univ) • normalizedMap ρ f := by
  rw [weight_smul_normalizedMap ρ f w hm0 hmt]
  have h := Measure.map_mono hdom hf
  rw [Measure.map_finset_sum' hf.aemeasurable, Measure.map_smul w hf.aemeasurable] at h
  simpa only [Measure.map_smul _ hf.aemeasurable, Measure.map_map hf (hz _)] using h

theorem normalizedMap_projected_ceiling
    {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (ρ : Measure X) (f : X → Y) (π : Y → Z) (π₀ : X → Z) (g : Z → Z)
    (ν : Measure Z) (hf : Measurable f) (hπ : Measurable π)
    (hπ₀ : Measurable π₀) (hg : Measurable g)
    (hcomp : π ∘ f = g ∘ π₀) {J K : ℝ} (hJ : 0 < J)
    (hm0 : 0 < ρ Set.univ) (hmt : ρ Set.univ < ⊤)
    (hvol : ν.map g = ENNReal.ofReal J • ν)
    (hraw : ρ.map π₀ ≤ (ENNReal.ofReal (K / J) * ρ Set.univ) • ν) :
    (normalizedMap ρ f).map π ≤ ENNReal.ofReal K • ν := by
  rw [normalizedMap, Measure.map_smul _ hπ.aemeasurable, Measure.map_map hπ hf,
    hcomp, ← Measure.map_map hg hπ₀]
  have h := Measure.map_mono hraw hg
  rw [Measure.map_smul _ hg.aemeasurable, hvol, smul_smul] at h
  have hh : (ρ Set.univ)⁻¹ • (ρ.map π₀).map g ≤
      (ρ Set.univ)⁻¹ • ((ENNReal.ofReal (K / J) * ρ Set.univ * ENNReal.ofReal J) • ν) := by
    exact smul_le_smul_left (ρ Set.univ)⁻¹ h
  rw [smul_smul] at hh
  have hscalar :
      (ρ Set.univ)⁻¹ * (ENNReal.ofReal (K / J) * ρ Set.univ * ENNReal.ofReal J) =
      ENNReal.ofReal K := by
    rw [ENNReal.ofReal_div_of_pos hJ, div_eq_mul_inv]
    calc
      _ = ((ρ Set.univ)⁻¹ * ρ Set.univ) *
          (ENNReal.ofReal K * ((ENNReal.ofReal J)⁻¹ * ENNReal.ofReal J)) := by ring
      _ = _ := by
        rw [ENNReal.inv_mul_cancel hm0.ne' hmt.ne,
          ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hJ) ENNReal.ofReal_ne_top]
        simp
  rwa [hscalar] at hh

theorem normalizedMap_ae {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ρ : Measure X) (f : X → Y) (hf : Measurable f) (Q : Y → Prop)
    (hQ : MeasurableSet {y | Q y}) (h : ∀ᵐ x ∂ρ, Q (f x)) :
    ∀ᵐ y ∂normalizedMap ρ f, Q y := by
  exact Measure.ae_smul_measure ((ae_map_iff hf.aemeasurable hQ).mpr h) _

theorem measurableSet_normalizedBounds (K δ : ℝ) (P S : Poly) :
    MeasurableSet {p | normalizedBounds K δ P S p} := by
  have heval (Q : Poly) : Continuous (fun p : Point => MvPolynomial.eval (fun i => p i) Q) :=
    (MvPolynomial.continuous_eval Q).comp (PiLp.continuous_ofLp 2 _)
  unfold normalizedBounds
  apply MeasurableSet.inter
  · exact measurableSet_le continuous_baseProjection.norm.measurable measurable_const
  apply MeasurableSet.inter
  · exact measurableSet_le (heval P).abs.measurable measurable_const
  apply MeasurableSet.inter
  · exact measurableSet_le measurable_const (heval _).abs.measurable
  apply MeasurableSet.inter
  · exact measurableSet_le (heval _).abs.measurable measurable_const
  apply MeasurableSet.inter
  · exact measurableSet_le (heval _).abs.measurable measurable_const
  apply MeasurableSet.inter
  · exact measurableSet_le (heval S).abs.measurable measurable_const
  exact measurableSet_le (heval _).abs.measurable measurable_const |>.inter
    (measurableSet_le (heval _).abs.measurable measurable_const)

open Submission.Obl.k4_dyadic_crop_affine_laws.Framework in
theorem earlierCoordinates_projected_ceiling (ρ : Measure Point)
    (t₀ q B : ℝ) (c u : Plane) (D : Matrix (Fin 2) (Fin 2) ℝ)
    (hq : 0 < q) (hD : D.det ≠ 0) (K : ℝ)
    (hm0 : 0 < ρ Set.univ) (hmt : ρ Set.univ < ⊤)
    (hraw : ρ.map baseProjection ≤
      (ENNReal.ofReal (K / (q * |D.det|)) * ρ Set.univ) • volume) :
    (normalizedMap ρ (earlierCoordinates t₀ q B c u D)).map baseProjection ≤
      ENNReal.ofReal K • volume := by
  let e := chartBaseEquiv t₀ q c u D hq.ne' hD
  exact normalizedMap_projected_ceiling ρ (earlierCoordinates t₀ q B c u D)
    baseProjection baseProjection e.symm volume
    (continuous_earlierCoordinates t₀ q B c u D).measurable
    continuous_baseProjection.measurable continuous_baseProjection.measurable e.symm.measurable
    (funext (baseProjection_earlierCoordinates t₀ q B c u D hq.ne' hD))
    (mul_pos hq (abs_pos.mpr hD)) hm0 hmt
    (map_chartBaseEquiv_symm t₀ q c u D hq hD) hraw

end Submission.Obl.k4_raw_earlier_witness_normalization
