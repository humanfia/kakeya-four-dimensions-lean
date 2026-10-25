/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/WorldCaps.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.WorldObservation
import Submission.Obl.k4_general_parent_projected_layers.Support.ScalarCropLaw
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Normalizing a projected cap uses the full original cropped prior exactly once. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_uncapped_native_capping (scalarX scalarY)

noncomputable section

theorem scalar_world_cap {α : Type} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (μ ρ : Measure (α × ℝ))
    (π : Measure ℝ) [IsProbabilityMeasure π] (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (b : α → Fin 6 → ℝ) (hb : Measurable b)
    {K chi g sigma width B d : ℝ} (hc : 0 < chi) (hg : 0 < g) (hwidth : 0 < width)
    (hB : 0 ≤ B) (C : Set α) (hC : MeasurableSet C)
    (hbound : ∀ l ∈ C, |b l 0| + |b l 1| + |b l 3| + |b l 4| ≤ K)
    (u : Fin 4 → ℤ) (hprior : ν (projectedWorldCrop C b chi g u) ≠ 0)
    (hρ : ρ ≤ μ) (hunit : ∀ᵐ z ∂μ, z.2 ∈ Icc (0 : ℝ) 1)
    (q : Fin 2 → ℤ) (j : ℤ)
    (hcap : μ {z | z.2 ∈ Icc (0 : ℝ) 1 ∧
      b z.1 ∈ majorGroup chi (projectedWorldRepresentatives K chi g u 1)
        (projectedWorldRepresentatives K chi g u 0) ∧
      projectedCell sigma g (projectedWorldRepresentatives K chi g u 2)
        (projectedWorldRepresentatives K chi g u 3) (b z.1) z.2 = q ∧
      ⌊eval (trajectory (b z.1) z.2) P / width⌋ = j ∧ ⌊b z.1 3 / chi⌋ = u 0} ≤
        ENNReal.ofReal (B * chi * g * width ^ d) * π {v | ⌊v / chi⌋ = u 0}) :
    scalarCropLaw ν ρ (projectedWorldCrop C b chi g u)
      {z | (![⌊z.2 / sigma⌋,
        ⌊scalarY (worldScalarCoefficients P b K chi g C u z.1) z.2 / sigma⌋] : Fin 2 → ℤ) = q ∧
          ⌊scalarX (worldScalarCoefficients P b K chi g C u z.1) z.2 / width⌋ = j} ≤
      ENNReal.ofReal (B * (chi * g * (π {v | ⌊v / chi⌋ = u 0}).toReal /
        (ν (projectedWorldCrop C b chi g u)).toReal) * width ^ d) := by
  let crop := projectedWorldCrop C b chi g u
  have hcrop : MeasurableSet crop := measurableSet_projectedWorldCrop hC b hb chi g u
  have hprior' : 0 < (ν crop).toReal := ENNReal.toReal_pos hprior (measure_ne_top _ _)
  have hinv : (ν crop)⁻¹ = ENNReal.ofReal ((ν crop).toReal)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hprior', ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hcapB : 0 ≤ B * chi * g * width ^ d := by positivity
  have hle := scalarCropLaw_event_le (ν := ν) hρ hcrop hunit
    (E := {z | (![⌊z.2 / sigma⌋,
      ⌊scalarY (worldScalarCoefficients P b K chi g C u z.1) z.2 / sigma⌋] : Fin 2 → ℤ) = q ∧
        ⌊scalarX (worldScalarCoefficients P b K chi g C u z.1) z.2 / width⌋ = j})
    (F := {z | z.2 ∈ Icc (0 : ℝ) 1 ∧
      b z.1 ∈ majorGroup chi (projectedWorldRepresentatives K chi g u 1)
        (projectedWorldRepresentatives K chi g u 0) ∧
      projectedCell sigma g (projectedWorldRepresentatives K chi g u 2)
        (projectedWorldRepresentatives K chi g u 3) (b z.1) z.2 = q ∧
      ⌊eval (trajectory (b z.1) z.2) P / width⌋ = j ∧ ⌊b z.1 3 / chi⌋ = u 0})
    (by
      intro z hzC hzt hz
      have ho := world_scalar_observation P hP b hc hg C hbound u hzC sigma z.2
      refine ⟨hzt, ho.1, ho.2.2.1.symm.trans hz.1, ?_, ho.2.1⟩
      simpa only [ho.2.2.2] using hz.2)
  apply hle.trans
  apply (mul_le_mul' le_rfl hcap).trans_eq
  have hprod : ENNReal.ofReal (B * chi * g * width ^ d) * π {v | ⌊v / chi⌋ = u 0} =
      ENNReal.ofReal ((B * chi * g * width ^ d) * (π {v | ⌊v / chi⌋ = u 0}).toReal) := by
    rw [ENNReal.ofReal_mul hcapB, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hprod, hinv, ← ENNReal.ofReal_mul (inv_nonneg.mpr hprior'.le)]
  congr 1
  dsimp only [crop]
  simp only [div_eq_mul_inv]
  ring

end

end Submission.Obl.k4_general_parent_projected_layers
