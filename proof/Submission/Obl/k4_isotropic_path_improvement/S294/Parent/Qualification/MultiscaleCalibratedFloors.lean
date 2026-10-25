-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.MultiscaleCalibratedFloors, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/MultiscaleCalibratedFloors.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CalibratedClockCensus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ClockIsotropicFloors
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.WholeStateFloors
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.HereditaryClockSupport

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ClockCalibration

open Set MeasureTheory
open Submission.Lib.K4ParentSignalPreparation.Census
open scoped ENNReal BigOperators

noncomputable section

/-- The same original anisotropic census supplies calibrated isotropic
carriers at every coarser dyadic width. The original resolution and
height factor are retained. -/
theorem support_at_dyadic_width {Ω : Type*}
    (E : Set Ω) (z : Ω → Fin 3 → ℝ) (X : Ω → ℝ)
    {ε θ K d : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hK : 1 ≤ K) (hθK : θ ≤ K)
    (hcensus : ∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 →
      K^(100:ℕ)*p ≤ θ*w → (occupied E z X p w).Finite ∧
        ((occupied E z X p w).ncard : ℝ) ≤ K/(p^3*w^d))
    (steps level : ℕ) (hsteps : K^(100:ℕ) ≤ (2:ℝ)^steps)
    (hwidth1 : ε*(2:ℝ)^steps*(2:ℝ)^level ≤ 1)
    (hresolved : ε*(2:ℝ)^steps*(2:ℝ)^level ≤ θ) :
    ∃ F : Finset ((Fin 3 → ℤ) × ℤ),
      (F.card : ℝ)*(ε*(2:ℝ)^steps*(2:ℝ)^level)^((3:ℝ)+d) ≤
        K*θ^d*((2:ℝ)^steps)^3 ∧
      ∀ x∈E, gridCode z (fun x => θ*X x)
        (ε*(2:ℝ)^steps*(2:ℝ)^level) (ε*(2:ℝ)^steps*(2:ℝ)^level) x∈F := by
  let ε' := ε*(2:ℝ)^level
  have hε' : 0 < ε' := by dsimp [ε']; positivity
  have hεε' : ε ≤ ε' := by
    dsimp [ε']
    exact le_mul_of_one_le_right hε.le (one_le_pow₀ (by norm_num))
  have hD : 1 ≤ (2:ℝ)^steps := one_le_pow₀ (by norm_num)
  have hwidth : ε'*(2:ℝ)^steps=ε*(2:ℝ)^steps*(2:ℝ)^level := by
    dsimp [ε']; ring
  have hε'1 : ε' ≤ 1 :=
    (le_mul_of_one_le_right hε'.le hD).trans (hwidth ▸ hwidth1)
  have hcensus' : ∀ p w : ℝ, ε' ≤ p → p ≤ 1 → ε' ≤ w → w ≤ 1 →
      K^(100:ℕ)*p ≤ θ*w → (occupied E z X p w).Finite ∧
        ((occupied E z X p w).ncard : ℝ) ≤ K/(p^3*w^d) := by
    intro p w hp hp1 hw hw1 hscale
    exact hcensus p w (hεε'.trans hp) hp1 (hεε'.trans hw) hw1 hscale
  obtain ⟨F,hF,hcover⟩ := ParentSource.clock_isotropic_support_height_calibrated
    E z X hε' hε'1 hθ hK hθK hcensus' steps hsteps (hwidth ▸ hresolved)
  rw [hwidth] at hF hcover
  exact ⟨F,hF,hcover⟩

/-- A calibrated support count pays a calibrated floor with no inverse
height factor. This is the real-number budget used by the common cut. -/
theorem calibrated_floor_budget {card : ℕ} {width θ d C rate : ℝ}
    (hwidth : 0 < width) (hθ : 0 < θ) (hrate : 0 ≤ rate)
    (hcount : (card:ℝ)*width^((3:ℝ)+d) ≤ C*θ^d) :
    (card:ℝ)*(rate*θ^(-d)*width^((3:ℝ)+d)) ≤ C*rate := by
  have hh := mul_le_mul_of_nonneg_right hcount
    (mul_nonneg hrate (Real.rpow_nonneg hθ.le (-d)))
  have heq : θ^d*θ^(-d)=1 := by
    rw [←Real.rpow_add hθ,add_neg_cancel,Real.rpow_zero]
  calc
    _ = ((card:ℝ)*width^((3:ℝ)+d))*(rate*θ^(-d)) := by ring
    _ ≤ (C*θ^d)*(rate*θ^(-d)) := hh
    _ = C*rate := by rw [mul_mul_mul_comm,heq,mul_one]

/-- Restore calibrated floors at all requested widths in ONE restriction
by whole original finest cells. Both the original reference and the
original finest conditional laws remain fixed. -/
theorem simultaneous_floors {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (E : Set Ω) (hsupport : ∀ᵐ x ∂μ, x∈E)
    (z : Ω → Fin 3 → ℝ) (hz : Measurable z) (X : Ω → ℝ) (hX : Measurable X)
    {ε θ K d : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hK : 1 ≤ K) (hθK : θ ≤ K)
    (hcensus : ∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 →
      K^(100:ℕ)*p ≤ θ*w → (occupied E z X p w).Finite ∧
        ((occupied E z X p w).ncard : ℝ) ≤ K/(p^3*w^d))
    (steps : ℕ) (hsteps : K^(100:ℕ) ≤ (2:ℝ)^steps)
    (hbase1 : ε*(2:ℝ)^steps ≤ 1) (hbaseθ : ε*(2:ℝ)^steps ≤ θ)
    (level : I → ℕ)
    (hwidth1 : ∀ i, ε*(2:ℝ)^steps*(2:ℝ)^(level i) ≤ 1)
    (hwidthθ : ∀ i, ε*(2:ℝ)^steps*(2:ℝ)^(level i) ≤ θ)
    (rate : I → ℝ) (hrate : ∀ i, 0 ≤ rate i) (reference : ENNReal) :
    let base := ε*(2:ℝ)^steps
    let Y := fun x => θ*X x
    ∃ U : Set ((Fin 3 → ℤ) × ℤ), MeasurableSet U ∧
      μ univ ≤ μ ((gridCode z Y base base) ⁻¹' U) +
        ENNReal.ofReal ((K*((2:ℝ)^steps)^3)*∑ i, rate i)*reference ∧
      (∀ i x, gridCode z Y base base x∈U →
        ENNReal.ofReal (rate i*θ^(-d)*(base*(2:ℝ)^(level i))^((3:ℝ)+d))*reference ≤
          (μ.restrict ((gridCode z Y base base) ⁻¹' U))
            {y | gridCode z Y (base*(2:ℝ)^(level i)) (base*(2:ℝ)^(level i)) y=
              gridCode z Y (base*(2:ℝ)^(level i)) (base*(2:ℝ)^(level i)) x}) ∧
      ∀ x, gridCode z Y base base x∈U →
        (μ.restrict ((gridCode z Y base base) ⁻¹' U))
          ((gridCode z Y base base) ⁻¹' {gridCode z Y base base x}) ≠ 0 := by
  classical
  dsimp only
  let base := ε*(2:ℝ)^steps
  let Y := fun x => θ*X x
  let state := gridCode z Y base base
  let code (i : I) := ParentSource.coarsenProductGrid (level i) (level i)
  let width (i : I) := base*(2:ℝ)^(level i)
  let cost (i : I) := ENNReal.ofReal (rate i*θ^(-d)*(width i)^((3:ℝ)+d))*reference
  have hb : 0 < base := by dsimp [base]; positivity
  have hwidth (i : I) : 0 < width i := by dsimp [width]; positivity
  have hm : Measurable state := ParentSource.measurable_product_gridCode z hz Y (hX.const_mul θ) _ _
  have hfactor (i : I) (x : Ω) : gridCode z Y (width i) (width i) x=code i (state x) :=
    HereditaryClockSupport.product_code_coarsens z Y base base (level i) (level i) x
  obtain ⟨S0,hS0,hcover0⟩ := support_at_dyadic_width E z X hε hθ hK hθK hcensus
    steps 0 hsteps (by simpa using hbase1) (by simpa using hbaseθ)
  let A := occupied E z Y base base
  have hfinite : A.Finite := S0.finite_toSet.subset (by
    rintro q ⟨x,hx,hq⟩
    subst q
    change state x ∈ S0
    simpa only [state,Y,base,pow_zero,mul_one] using hcover0 x hx)
  let F := hfinite.toFinset
  have hcarrier : ∀ᵐ x ∂μ, state x∈F := hsupport.mono (by
    intro x hx
    exact hfinite.mem_toFinset.mpr ⟨x,hx,rfl⟩)
  have hcount (i : I) : ((F.image (code i)).card:ℝ)*(width i)^((3:ℝ)+d) ≤
      (K*((2:ℝ)^steps)^3)*θ^d := by
    obtain ⟨S,hS,hcover⟩ := support_at_dyadic_width E z X hε hθ hK hθK hcensus
      steps (level i) hsteps (hwidth1 i) (hwidthθ i)
    have hsub : F.image (code i) ⊆ S := by
      intro q hq
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨x,hx,hxa⟩ := hfinite.mem_toFinset.mp ha
      change state x=a at hxa
      have hh := hcover x hx
      change gridCode z Y (width i) (width i) x∈S at hh
      rw [hfactor i x,hxa] at hh
      exact hh
    apply (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hsub))
      (Real.rpow_nonneg (hwidth i).le _)).trans
    exact hS.trans_eq (by ring)
  have hcost (i : I) : ∑ _c∈F.image (code i), cost i ≤
      ENNReal.ofReal ((K*((2:ℝ)^steps)^3)*rate i)*reference := by
    simp only [Finset.sum_const,nsmul_eq_mul]
    change ((F.image (code i)).card:ENNReal)*
      (ENNReal.ofReal (rate i*θ^(-d)*(width i)^((3:ℝ)+d))*reference) ≤ _
    rw [←mul_assoc,←ENNReal.ofReal_natCast,
      ←ENNReal.ofReal_mul (by positivity : 0 ≤ ((F.image (code i)).card:ℝ))]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal
      (calibrated_floor_budget (hwidth i) hθ (hrate i) (hcount i))) le_rfl
  obtain ⟨U,hU,hUF,hloss,hfloor,hpositive⟩ := simultaneous_whole_state_floors
    μ state hm F hcarrier code (fun i _ => cost i)
  refine ⟨U,hU,hloss.trans ?_,?_,hpositive⟩
  · apply add_le_add le_rfl
    calc
      _ ≤ ∑ i : I, ENNReal.ofReal ((K*((2:ℝ)^steps)^3)*rate i)*reference :=
        Finset.sum_le_sum (fun i _ => hcost i)
      _ = ENNReal.ofReal ((K*((2:ℝ)^steps)^3)*∑ i : I, rate i)*reference := by
        rw [←Finset.sum_mul,←ENNReal.ofReal_sum_of_nonneg]
        · congr 2
          rw [Finset.mul_sum]
        · intro i _
          exact mul_nonneg (by positivity) (hrate i)
  · intro i x hx
    have hh := hfloor i x hx
    change cost i ≤ (μ.restrict (state ⁻¹' U)) {y | code i (state y)=code i (state x)} at hh
    simpa only [←hfactor i] using hh

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ClockCalibration
