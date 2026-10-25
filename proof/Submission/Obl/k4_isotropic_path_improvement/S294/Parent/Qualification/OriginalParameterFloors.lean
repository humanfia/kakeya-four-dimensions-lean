-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalParameterFloors, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/OriginalParameterFloors.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/OriginalParameterFloors.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/OriginalParameterFloors.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalParameterCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalAffineBinCarriers
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalVerticalCounts
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ParameterFloors2Heavy
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ParameterBridge2


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory

noncomputable section

/-- Full ORIGINAL parameter-bin floors from actual source rectangle caps,
occupation floors, physical-cell floors and base caps. The original
palette-area carrier, every scalar support table and every coefficient
ball cap are constructed internally before invoking scalar cleanup. -/
theorem original_parameter_floor_preparation (d a ε : ℝ)
    (hd : 0 ≤ d) (hd1 : d < 1) (ha : 0 < a) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (Λ : Type) [MeasurableSpace Λ] (ν : Measure Λ) [IsFiniteMeasure ν]
        (reference : Measure (Λ × ℝ)) [IsFiniteMeasure reference]
        (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
        (E : Set (Λ × ℝ)) (hE : MeasurableSet E) (S : Set Λ) (hS : MeasurableSet S)
        (hES : E ⊆ S ×ˢ Icc (0 : ℝ) 1) (K Kr Kfloor Kbase : ℝ)
        (hK : 1 ≤ K) (hKr : 0 ≤ Kr) (hKfloor : 0 < Kfloor) (hKbase : 0 ≤ Kbase)
        (π : Measure (Fin 2 → ℤ)) [IsProbabilityMeasure π]
        (hcoeff : ∀ l∈S, ∀ i, |c l i| ≤ K)
        (hocc : ∀ l∈S, ENNReal.ofReal K⁻¹ ≤ volume {t | (l,t)∈E})
        (hCoeffBudget : 2*K ≤ N^η)
        (hCapBudget : originalParameterCapConstant K Kr d ≤ N^η)
        (hSupportBudget : 4*(4*K+6)^3*(Kbase*Kfloor) ≤ N^η)
        (hPhysicalFloor : ∀ z∈E, ENNReal.ofReal ((N^(-a))^(3+d)/Kfloor) ≤
          reference ((originalFineState c (N^(-a))) ⁻¹' {originalFineState c (N^(-a)) z}))
        (hBaseCap : ∀ q, reference {z | originalBaseCode c (N^(-a)) z=q} ≤
          ENNReal.ofReal (Kbase*(N^(-a))^3))
        (hrect : ∀ (t₀ : ℝ) (Y : Fin 2 → ℝ) (left q w : ℝ) (J : Fin 2 → ℤ), N^(-a) ≤ q → N^(-a) ≤ w →
          (ν.prod volume) {z | z ∈ E ∧ z.2 ∈ Icc t₀ (t₀ + N^(-a)) ∧
            (∀ i, zy (c z.1) z.2 i ∈ Icc (Y i) (Y i + q)) ∧ zx (c z.1) z.2 ∈ Icc left (left + w) ∧
            vbin (N^(-a)) (c z.1) = J} ≤ ENNReal.ofReal (Kr * N^(-a) * q ^ 2 * w ^ d) * π {J})
        , ∃ R : Set Λ, MeasurableSet R ∧ R ⊆ S ∧
          (ν.prod volume) (E ∩ ((S \ R) ×ˢ univ)) ≤
            ENNReal.ofReal ((4*K+2)^2)*ENNReal.ofReal (N^(-η)) ∧
          ∀ l∈R, ENNReal.ofReal ((N^(-a))^(2+d)*N^(-ε))*π {vbin (N^(-a)) (c l)} ≤
            ν {l' | parameterCode (N^(-a)) (c l')=parameterCode (N^(-a)) (c l)} := by
  obtain ⟨η,hη,N₀,hN₀,hclean⟩ := parameter_floor_cleanup
    (floorCleanupStatement_holds d a ε hd hd1 ha hε)
  refine ⟨η,hη,N₀,hN₀,?_⟩
  intro N hN Λ _ ν _ reference _ c hc E hE S hS hES K Kr Kfloor Kbase hK hKr hKfloor hKbase
    π _ hcoeff hocc hCoeffBudget hCapBudget hSupportBudget hPhysicalFloor hBaseCap hrect
  let p := N^(-a)
  have hNp : 0 < N := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (hN₀.trans hN)
  have hp : 0 < p := Real.rpow_pos_of_pos hNp _
  have hp1 : p ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by linarith [hN₀.trans hN] : (1 : ℝ) ≤ N) (by linarith)
  have hK0 : 0 ≤ K := by linarith
  have hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1 := fun z hz => ⟨mem_univ _,(hES hz).2⟩
  have hcoeffE (z : Λ × ℝ) (hz : z∈E) : ∀ i, |c z.1 i| ≤ K := hcoeff z.1 (hES hz).1
  obtain ⟨A2,hA2,hPalette⟩ := original_affine_bin_carrier S c p K hp hp1 hK0 hcoeff π
  have hVertical := original_vertical_physical_count reference c hc E p Kfloor Kbase d
    hp hKfloor hKbase hPhysicalFloor hBaseCap
  obtain ⟨F,hFcard,hFknown⟩ := original_affine_scalar_support_tables E c p K (Kbase*Kfloor) d
    hp hp1 hK0 (mul_nonneg hKbase hKfloor.le) (fun z hz => (hES hz).2) hcoeffE
    (fun q => (hVertical q).2)
  obtain ⟨hMass,hBall⟩ := original_parameter_coefficient_caps ν c hc E hE hunit S hS p K Kr d
    hp hp1 hK hKr hd hd1.le (fun J => π {J}) hcoeff hocc hrect
  have hcleanMass (q) (_hq : q∈A2) : ν (affineWorld S c p q.1 q.2) ≤
      π {q.2}*ENNReal.ofReal (p^2*N^η) := by
    apply (hMass q.1 q.2).trans
    calc
      ENNReal.ofReal (originalParameterCapConstant K Kr d*p^2)*π {q.2} ≤
          ENNReal.ofReal (N^η*p^2)*π {q.2} :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right hCapBudget (sq_nonneg p))) le_rfl
      _ = _ := by
        rw [mul_comm]
        exact congrArg (fun x : ℝ => π {q.2}*ENNReal.ofReal x) (by ring)
  have hcleanBall (q) (_hq : q∈A2) (b : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : p ≤ r) :
      ν (affineWorld S c p q.1 q.2 ∩ {l | scalarCoeffPoint K (c l)∈Metric.ball b r}) ≤
        π {q.2}*ENNReal.ofReal (p^2*(N^η*r^d)) := by
    apply (hBall q.1 q.2 b r hr).trans
    calc
      ENNReal.ofReal (originalParameterCapConstant K Kr d*p^2*r^d)*π {q.2} ≤
          ENNReal.ofReal (N^η*p^2*r^d)*π {q.2} :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCapBudget (sq_nonneg p))
            (Real.rpow_nonneg (hp.le.trans hr) _))) le_rfl
      _ = _ := by
        rw [mul_comm]
        exact congrArg (fun x : ℝ => π {q.2}*ENNReal.ofReal x) (by ring)
  have hcleanSupport (q) (_hq : q∈A2) : ((F q.1 q.2).card : ℝ) ≤ N^η*p^(-1-d) :=
    (hFcard q.1 q.2).trans (mul_le_mul_of_nonneg_right hSupportBudget (Real.rpow_nonneg hp.le _))
  have hcleanKnown (q) (_hq : q∈A2) (l : Λ) (t : ℝ) (hz : (l,t)∈E)
      (hl : l∈affineWorld S c p q.1 q.2) : (⌊t/p⌋,⌊zx (c l) t/p⌋)∈F q.1 q.2 := by
    have hh := hFknown (l,t) hz
    simpa only [hl.2.1,hl.2.2] using hh
  obtain ⟨hLoss,hGood⟩ := hclean N hN Λ ν c E S K ((4*K+2)^2) (fun J => π {J}) A2 F
    hc hE hunit hS hK0 hCoeffBudget (sq_nonneg _) hA2 hPalette
    (fun l hl => ⟨hcoeff l hl 0,hcoeff l hl 1,hcoeff l hl 2⟩)
    hcleanMass hcleanBall hcleanSupport hcleanKnown
  let bad : Set Λ := ⋃ q∈A2, lightPart ν c S K p (fun J => π {J}) (N^(-a*d-ε)) q.1 q.2
  let f := p^2*N^(-a*d-ε)
  let R : Set Λ := {l∈S | ENNReal.ofReal f*π {vbin p (c l)} ≤
    ν {l' | parameterCode p (c l')=parameterCode p (c l)}}
  have hCode := (measurable_parameterCode p).comp hc
  have hPrior : Measurable (fun l => ν {l' | parameterCode p (c l')=parameterCode p (c l)}) :=
    (measurable_of_countable (fun q : Fin 7 → ℤ => ν {l' | parameterCode p (c l')=q})).comp hCode
  have hPal : Measurable (fun l => π {vbin p (c l)}) :=
    (measurable_of_countable (fun J : Fin 2 → ℤ => π {J})).comp (measurable_vbin hc p)
  have hR : MeasurableSet R := hS.inter (measurableSet_le (measurable_const.mul hPal) hPrior)
  have hOutside (l : Λ) (hl : l∈S) (hnot : l∉bad) : l∈R := by
    have hh := hGood l hl hnot
    have hf := blockPrior_floor_of_world (ν := ν) (S := S) (cf := c) (K := K) (p := p)
      (f := f) (π := fun J => π {J})
      (fun l hl => ⟨hcoeff l hl 0,hcoeff l hl 1,hcoeff l hl 2⟩) hl hh
    rw [←vbin_eq_blockVbin] at hf
    refine ⟨hl,hf.trans (measure_mono ?_)⟩
    intro l' hl'
    exact hl'.2
  have hLoss' : (ν.prod volume) (E ∩ ((S \ R) ×ˢ univ)) ≤
      ENNReal.ofReal ((4*K+2)^2)*ENNReal.ofReal (N^(-η)) := by
    apply (measure_mono ?_).trans hLoss
    intro z hz
    refine ⟨hz.1,?_,mem_univ _⟩
    by_contra hh
    exact hz.2.1.2 (hOutside z.1 hz.2.1.1 hh)
  have hscale : f=p^(2+d)*N^(-ε) := by
    have he : N^(-a*d-ε)=p^d*N^(-ε) := by
      rw [show -a*d-ε=(-a)*d+(-ε) by ring,Real.rpow_add hNp,Real.rpow_mul hNp.le]
    dsimp [f]
    rw [he,Real.rpow_add hp]
    norm_num only [Real.rpow_ofNat]
    ring
  refine ⟨R,hR,fun l hl => hl.1,hLoss',?_⟩
  intro l hl
  have hh := hl.2
  rw [hscale] at hh
  exact hh

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
