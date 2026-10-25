-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalDyadicParameterFloors, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/OriginalDyadicParameterFloors.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/OriginalDyadicParameterFloors.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/OriginalDyadicParameterFloors.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalParameterWidths
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.DyadicFloorBudget


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory

noncomputable section

/-- ONE original line restriction gives every floor on the actual
aligned dyadic range. All scalar tables, coefficient caps and palette
carriers are produced by the actual-width source factory. The deletion
budget is geometric, independent of the number of widths. -/
theorem original_dyadic_parameter_floors (d ε : ℝ) (hd : 0 ≤ d) (hd1 : d < 1) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ n L : ℕ, dyadicParameterWidth n ≤ p₀ →
      ∀ (Λ : Type) [MeasurableSpace Λ] (ν : Measure Λ) [IsFiniteMeasure ν]
        (reference : Measure (Λ × ℝ)) [IsFiniteMeasure reference]
        (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
        (E : Set (Λ × ℝ)) (hE : MeasurableSet E) (S : Set Λ) (hS : MeasurableSet S)
        (hES : E ⊆ S ×ˢ Icc (0 : ℝ) 1) (K Kr Kfloor Kbase : ℝ)
        (hK : 1 ≤ K) (hKr : 0 ≤ Kr) (hKfloor : 0 < Kfloor) (hKbase : 0 ≤ Kbase)
        (π : Fin L → Measure (Fin 2 → ℤ)) [∀ i, IsProbabilityMeasure (π i)]
        (hcoeff : ∀ l∈S, ∀ j, |c l j| ≤ K)
        (hocc : ∀ l∈S, ENNReal.ofReal K⁻¹ ≤ volume {t | (l,t)∈E})
        (hCoeffBudget : 2*K ≤ (dyadicParameterWidth n)^(-η))
        (hCapBudget : originalParameterCapConstant K Kr d ≤ (dyadicParameterWidth n)^(-η))
        (hSupportBudget : 4*(4*K+6)^3*(Kbase*Kfloor) ≤ (dyadicParameterWidth n)^(-η))
        (hPhysicalFloor : ∀ i : Fin L, ∀ z∈E,
          ENNReal.ofReal ((dyadicParameterWidth (n+i.val))^(3+d)/Kfloor) ≤
            reference ((originalFineState c (dyadicParameterWidth (n+i.val))) ⁻¹'
              {originalFineState c (dyadicParameterWidth (n+i.val)) z}))
        (hBaseCap : ∀ i : Fin L, ∀ q,
          reference {z | originalBaseCode c (dyadicParameterWidth (n+i.val)) z=q} ≤
            ENNReal.ofReal (Kbase*(dyadicParameterWidth (n+i.val))^3))
        (hrect : ∀ i : Fin L, ∀ (t₀ : ℝ) (Y : Fin 2 → ℝ) (left q w : ℝ) (J : Fin 2 → ℤ),
          dyadicParameterWidth (n+i.val) ≤ q → dyadicParameterWidth (n+i.val) ≤ w →
            (ν.prod volume) {z | z∈E ∧ z.2∈Icc t₀ (t₀+dyadicParameterWidth (n+i.val)) ∧
              (∀ j, zy (c z.1) z.2 j∈Icc (Y j) (Y j+q)) ∧ zx (c z.1) z.2∈Icc left (left+w) ∧
              vbin (dyadicParameterWidth (n+i.val)) (c z.1)=J} ≤
                ENNReal.ofReal (Kr*dyadicParameterWidth (n+i.val)*q^2*w^d)*(π i) {J}),
        ∃ R : Set Λ, MeasurableSet R ∧ R ⊆ S ∧
          (ν.prod volume) (E ∩ ((S \ R) ×ˢ univ)) ≤
            ENNReal.ofReal (((4*K+2)^2)*(dyadicParameterWidth n)^η/(1-(2 : ℝ)^(-η))) ∧
          ∀ i : Fin L, ∀ l∈R,
            ENNReal.ofReal ((dyadicParameterWidth (n+i.val))^(2+d)*
              (dyadicParameterWidth (n+i.val))^ε)*(π i) {vbin (dyadicParameterWidth (n+i.val)) (c l)} ≤
                ν {l' | parameterCode (dyadicParameterWidth (n+i.val)) (c l')=
                  parameterCode (dyadicParameterWidth (n+i.val)) (c l)} := by
  obtain ⟨η,hη,p₀,hp₀,hSource⟩ := original_parameter_floors_at_actual_width d ε hd hd1 hε
  refine ⟨η,hη,p₀,hp₀,?_⟩
  intro n L hn Λ _ ν _ reference _ c hc E hE S hS hES K Kr Kfloor Kbase hK hKr hKfloor hKbase
    π _ hcoeff hocc hCoeffBudget hCapBudget hSupportBudget hPhysicalFloor hBaseCap hrect
  have hWidth (i : Fin L) : dyadicParameterWidth (n+i.val) ≤ dyadicParameterWidth n :=
    dyadicParameterWidth_antitone (Nat.le_add_right _ _)
  have hPower (i : Fin L) : (dyadicParameterWidth n)^(-η) ≤
      (dyadicParameterWidth (n+i.val))^(-η) :=
    Real.rpow_le_rpow_of_nonpos (dyadicParameterWidth_pos _) (hWidth i) (by linarith)
  have hOne (i : Fin L) := hSource (dyadicParameterWidth (n+i.val)) (dyadicParameterWidth_pos _)
    ((hWidth i).trans hn) Λ ν reference c hc E hE S hS hES K Kr Kfloor Kbase hK hKr hKfloor hKbase
    (π i) hcoeff hocc (hCoeffBudget.trans (hPower i)) (hCapBudget.trans (hPower i))
    (hSupportBudget.trans (hPower i)) (hPhysicalFloor i) (hBaseCap i) (hrect i)
  choose Ri hRi hRiS hLoss hFloor using hOne
  let R := S ∩ ⋂ i : Fin L, Ri i
  have hR : MeasurableSet R := hS.inter (MeasurableSet.iInter hRi)
  have hSub : E ∩ ((S \ R) ×ˢ univ) ⊆ ⋃ i : Fin L, E ∩ ((S \ Ri i) ×ˢ univ) := by
    intro z hz
    have hex : ∃ i : Fin L, z.1∉Ri i := by
      by_contra! hh
      exact hz.2.1.2 ⟨hz.2.1.1,mem_iInter.mpr hh⟩
    obtain ⟨i,hi⟩ := hex
    exact mem_iUnion.mpr ⟨i,hz.1,⟨hz.2.1.1,hi⟩,mem_univ _⟩
  refine ⟨R,hR,fun l hl => hl.1,?_,?_⟩
  · calc
      (ν.prod volume) (E ∩ ((S \ R) ×ˢ univ)) ≤
          ∑ i : Fin L, (ν.prod volume) (E ∩ ((S \ Ri i) ×ˢ univ)) :=
        (measure_mono hSub).trans (measure_iUnion_fintype_le _ _)
      _ ≤ ∑ i : Fin L, ENNReal.ofReal ((4*K+2)^2)*
          ENNReal.ofReal ((dyadicParameterWidth (n+i.val))^η) :=
        Finset.sum_le_sum fun i _ => hLoss i
      _ = ENNReal.ofReal (∑ i : Fin L, ((4*K+2)^2)*(dyadicParameterWidth (n+i.val))^η) := by
        simp_rw [←ENNReal.ofReal_mul (sq_nonneg (4*K+2))]
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro i _
        exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (dyadicParameterWidth_pos _).le _)
      _ ≤ _ := ENNReal.ofReal_le_ofReal (dyadic_floor_loss_budget η ((4*K+2)^2) hη (sq_nonneg _) n L)
  · intro i l hl
    exact hFloor i l (mem_iInter.mp hl.2 i)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
