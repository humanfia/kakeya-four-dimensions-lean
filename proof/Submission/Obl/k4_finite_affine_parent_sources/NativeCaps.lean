-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.ModelEH1
import Submission.Obl.k4_remainder_pure_profile_normalization.Normalization.NormDensityFormula

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory MvPolynomial
open Submission.Obl.k4_remainder_pure_profile_normalization.Normalization

noncomputable section

/-- The exact model observation before taking a base cell. -/
def obsS {α : Type} (b : α → Fin 6 → ℝ) (a : ℝ) (p : α × ℝ) :
    EuclideanSpace ℝ (Fin 3) × ℤ :=
  (WithLp.toLp 2 ![p.2, (exS b p.1 p.2) 1, (exS b p.1 p.2) 2],
    ⌊(exS b p.1 p.2) 3 / a⌋)

theorem measurable_obsS {α : Type} [MeasurableSpace α] {b : α → Fin 6 → ℝ}
    (hb : Measurable b) (a : ℝ) : Measurable (obsS b a) := by
  unfold obsS
  refine Measurable.prodMk ?_ ?_
  · refine (PiLp.volume_preserving_toLp (Fin 3)).measurable.comp ?_
    refine measurable_pi_iff.mpr fun i => ?_
    fin_cases i <;> simp [exS] <;> fun_prop
  · exact Int.measurable_floor.comp (by simp [exS]; fun_prop)

namespace PFrame

/-- The model hidden bin is exactly an original hidden bin at composed width. -/
theorem obsS_tnorm (Φ : PFrame) (hq : Φ.F.q ≠ 0) (δ B a : ℝ)
    (hδ : δ ≠ 0) (hsc : Φ.sc = B / δ) (p : (ℕ × (Fin 6 → ℝ)) × ℝ) :
    obsS Φ.eb a (tnorm Φ.F.t₀ Φ.F.q p) =
      Prod.map Φ.F.obsBase id (obs B (δ * a) p) := by
  calc
    _ = obs (B / δ) a (Φ.F.normInc p) := by
      apply Prod.ext
      · rfl
      · change ⌊(Φ.sc * Φ.F.normCoeff p.1.2 2 +
            ((p.2 - Φ.F.t₀) / Φ.F.q) * (Φ.sc * Φ.F.normCoeff p.1.2 5)) / a⌋ =
          ⌊((B / δ) * (Φ.F.normCoeff p.1.2 2 +
            ((p.2 - Φ.F.t₀) / Φ.F.q) * Φ.F.normCoeff p.1.2 5)) / a⌋
        congr 1
        rw [hsc]
        ring
    _ = _ := Φ.F.obs_normInc hq B δ a hδ p

/-- The inverse base Jacobian restores the original time and spatial volume.
Adapted from o107/x0735, NativeDensityCaps.lean, commit cc2492748f08. -/
theorem obsJacobian (Φ : PFrame) (hq : 0 < Φ.F.q) :
    |Φ.F.obsMatrix.det|⁻¹ = Φ.F.q * |Φ.F.D.det| := by
  rw [Φ.F.det_obsMatrix, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
    abs_mul, abs_inv, abs_inv, mul_inv_rev, inv_inv, inv_inv, abs_of_pos hq]
  ring

/-- A retained original observation ceiling gives the model ceiling with
factor |det D|/nu(A). The parent time normalizer cancels exactly. -/
theorem muE_observation_cap (Φ : PFrame) (hq : 0 < Φ.F.q) (hD : IsUnit Φ.F.D.det)
    (δ B a : ℝ) (hδ : δ ≠ 0) (hsc : Φ.sc = B / δ)
    (ν : Measure (ℕ × (Fin 6 → ℝ))) (A₀ : Set (ℕ × (Fin 6 → ℝ)))
    (S : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (M : ENNReal)
    (hcap : (((ν.prod volume).restrict S).map (obs B (δ * a))) ≤
      M • (volume.prod Measure.count)) :
    (muE ν A₀ Φ.F.t₀ Φ.F.q S).map (obsS Φ.eb a) ≤
      ((ν A₀)⁻¹ * ENNReal.ofReal |Φ.F.D.det| * M) • (volume.prod Measure.count) := by
  let e := Φ.F.obsEquiv hq.ne' hD
  have hO := measurable_obsS Φ.measurable_eb a
  have hmap : (muE ν A₀ Φ.F.t₀ Φ.F.q S).map (obsS Φ.eb a) =
      (ENNReal.ofReal Φ.F.q * ν A₀)⁻¹ • (((ν.prod volume).restrict S).map (obs B (δ * a))).map e := by
    rw [muE, Measure.map_smul _ hO.aemeasurable,
      Measure.map_map hO (measurable_tnorm _ _),
      Measure.map_map e.measurable (measurable_obs _ _)]
    congr 2
    funext p
    exact Φ.obsS_tnorm hq.ne' δ B a hδ hsc p
  rw [hmap]
  calc
    _ ≤ (ENNReal.ofReal Φ.F.q * ν A₀)⁻¹ • (M • (volume.prod Measure.count)).map e :=
      smul_le_smul_meas _ (Measure.map_mono hcap e.measurable)
    _ = ((ν A₀)⁻¹ * ENNReal.ofReal |Φ.F.D.det| * M) • (volume.prod Measure.count) := by
      rw [Measure.map_smul M e.measurable.aemeasurable, Φ.F.map_obsEquiv hq.ne' hD,
        smul_smul, smul_smul, Φ.obsJacobian hq,
        ENNReal.ofReal_mul hq.le]
      congr 1
      have hq0 : ENNReal.ofReal Φ.F.q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hq
      rw [ENNReal.mul_inv (Or.inl hq0) (Or.inl ENNReal.ofReal_ne_top)]
      calc
        _ = (ν A₀)⁻¹ * ENNReal.ofReal |Φ.F.D.det| * M *
            ((ENNReal.ofReal Φ.F.q)⁻¹ * ENNReal.ofReal Φ.F.q) := by ring
        _ = _ := by rw [ENNReal.inv_mul_cancel hq0 ENNReal.ofReal_ne_top, mul_one]

end PFrame

end

end Submission.Obl.k4_finite_affine_parent_sources
