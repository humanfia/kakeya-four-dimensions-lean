-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalParameterWidths, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/OriginalParameterWidths.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/OriginalParameterWidths.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/OriginalParameterWidths.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalParameterFloors


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory

noncomputable section

/-- Apply coefficient cleanup directly at ANY actual small width p.
The auxiliary scale is p inverse, so original dyadic bins are retained
exactly and no lower bin floor is interpolated between shifted grids. -/
theorem original_parameter_floors_at_actual_width (d ε : ℝ)
    (hd : 0 ≤ d) (hd1 : d < 1) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∀ (Λ : Type) [MeasurableSpace Λ] (ν : Measure Λ) [IsFiniteMeasure ν]
        (reference : Measure (Λ × ℝ)) [IsFiniteMeasure reference]
        (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
        (E : Set (Λ × ℝ)) (hE : MeasurableSet E) (S : Set Λ) (hS : MeasurableSet S)
        (hES : E ⊆ S ×ˢ Icc (0 : ℝ) 1) (K Kr Kfloor Kbase : ℝ)
        (hK : 1 ≤ K) (hKr : 0 ≤ Kr) (hKfloor : 0 < Kfloor) (hKbase : 0 ≤ Kbase)
        (π : Measure (Fin 2 → ℤ)) [IsProbabilityMeasure π]
        (hcoeff : ∀ l∈S, ∀ i, |c l i| ≤ K)
        (hocc : ∀ l∈S, ENNReal.ofReal K⁻¹ ≤ volume {t | (l,t)∈E})
        (hCoeffBudget : 2*K ≤ p^(-η))
        (hCapBudget : originalParameterCapConstant K Kr d ≤ p^(-η))
        (hSupportBudget : 4*(4*K+6)^3*(Kbase*Kfloor) ≤ p^(-η))
        (hPhysicalFloor : ∀ z∈E, ENNReal.ofReal (p^(3+d)/Kfloor) ≤
          reference ((originalFineState c p) ⁻¹' {originalFineState c p z}))
        (hBaseCap : ∀ q, reference {z | originalBaseCode c p z=q} ≤
          ENNReal.ofReal (Kbase*p^3))
        (hrect : ∀ (t₀ : ℝ) (Y : Fin 2 → ℝ) (left q w : ℝ) (J : Fin 2 → ℤ), p ≤ q → p ≤ w →
          (ν.prod volume) {z | z ∈ E ∧ z.2 ∈ Icc t₀ (t₀ + p) ∧
            (∀ i, zy (c z.1) z.2 i ∈ Icc (Y i) (Y i + q)) ∧ zx (c z.1) z.2 ∈ Icc left (left + w) ∧
            vbin p (c z.1) = J} ≤ ENNReal.ofReal (Kr * p * q ^ 2 * w ^ d) * π {J})
        , ∃ R : Set Λ, MeasurableSet R ∧ R ⊆ S ∧
          (ν.prod volume) (E ∩ ((S \ R) ×ˢ univ)) ≤
            ENNReal.ofReal ((4*K+2)^2)*ENNReal.ofReal (p^η) ∧
          ∀ l∈R, ENNReal.ofReal (p^(2+d)*p^ε)*π {vbin p (c l)} ≤
            ν {l' | parameterCode p (c l')=parameterCode p (c l)} := by
  obtain ⟨η,hη,N₀,hN₀,hSource⟩ := original_parameter_floor_preparation d 1 ε hd hd1 (by norm_num) hε
  have hN₀pos : 0 < N₀ := by linarith
  refine ⟨η,hη,N₀⁻¹,inv_pos.mpr hN₀pos,?_⟩
  intro p hp hp0
  have hInv : N₀ ≤ p⁻¹ := by
    have hh := mul_le_mul_of_nonneg_left hp0 hN₀pos.le
    rw [mul_inv_cancel₀ hN₀pos.ne'] at hh
    rw [←one_div,le_div_iff₀ hp]
    exact hh
  have hPower (b : ℝ) : (p⁻¹)^b=p^(-b) := by
    calc
      (p⁻¹)^b=(p^(-1 : ℝ))^b := by rw [Real.rpow_neg_one]
      _ = p^((-1)*b) := (Real.rpow_mul hp.le _ _).symm
      _ = p^(-b) := by congr 1; ring
  simpa only [hPower,neg_neg,Real.rpow_one] using hSource (p⁻¹) hInv

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
