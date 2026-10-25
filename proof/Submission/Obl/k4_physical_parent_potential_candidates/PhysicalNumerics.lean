import Submission.Obl.k4_physical_parent_potential_candidates.PhysicalGroup

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory PhysicalPotentialData
open scoped ENNReal

noncomputable section

/-- The fixed MK3 constant in the original heavy-source floor. -/
def physicalMassLoss (C : ℝ) : ℝ := 2038431744*(1000*C)^2

theorem physicalMassLoss_pos {C : ℝ} (hC : 0 < C) : 0 < physicalMassLoss C := by
  unfold physicalMassLoss
  positivity

theorem physicalHeavyFloor_eq {h prior C K w d : ℝ} (hK : 0 < K) (hC : 0 < C) :
    physicalHeavyFloor h prior C K w d =
      h*prior*w^d/(254803968*(1000*C)^2*(1+K)^3*K^205) := by
  have hr : K^(-100:ℝ) = (K^100)⁻¹ := by
    rw [show (-100:ℝ) = -(100:ℝ) by norm_num, Real.rpow_neg hK.le]
    norm_cast
  unfold physicalHeavyFloor
  rw [hr]
  field_simp
  <;> ring

/-- Only a fixed polynomial in K is charged to the original mass reference. -/
theorem physicalHeavyFloor_lower {h prior C K w d : ℝ}
    (hh : 0 ≤ h) (hprior : 0 ≤ prior) (hC : 0 < C) (hK : 1 ≤ K) (hw : 0 < w) :
    h*prior*w^d/(physicalMassLoss C*K^208) ≤ physicalHeavyFloor h prior C K w d := by
  have hK0 : 0 < K := by linarith
  rw [physicalHeavyFloor_eq hK0 hC]
  have hcube : (1+K)^3 ≤ 8*K^3 := by
    have hc := pow_le_pow_left₀ (by positivity : 0 ≤ 1+K) (by linarith : 1+K ≤ 2*K) 3
    convert hc using 1 <;> ring
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  calc
    254803968*(1000*C)^2*(1+K)^3*K^205 ≤
        254803968*(1000*C)^2*(8*K^3)*K^205 := by gcongr
    _ = physicalMassLoss C*K^208 := by unfold physicalMassLoss; ring

/-- The scalar ceiling and heavy floor have the same w^d, so their ratio
has a polynomial K bound independent of the chosen intercept width. -/
theorem physical_scalar_density_real {h prior C K w d mass : ℝ}
    (hh : 0 ≤ h) (hprior : 0 ≤ prior) (hC : 0 < C) (hK : 1 ≤ K)
    (hw : 0 < w) (hd : d ≤ 1)
    (hmass : physicalHeavyFloor h prior C K w d ≤ mass) :
    K*(2*w)^d*(h*prior) ≤ (2*physicalMassLoss C*K^209)*mass := by
  have hK0 : 0 < K := by linarith
  have hden : 0 < physicalMassLoss C*K^208 :=
    mul_pos (physicalMassLoss_pos hC) (pow_pos hK0 _)
  have hm := (div_le_iff₀ hden).1
    ((physicalHeavyFloor_lower hh hprior hC hK hw).trans hmass)
  have htwo : (2:ℝ)^d ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hd
  calc
    K*(2*w)^d*(h*prior) = (K*2^d)*(h*prior*w^d) := by
      rw [Real.mul_rpow (by norm_num) hw.le]
      ring
    _ ≤ (2*K)*(h*prior*w^d) := by
      apply mul_le_mul_of_nonneg_right ?_ (by positivity)
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left htwo hK0.le
    _ ≤ (2*K)*(physicalMassLoss C*K^208*mass) :=
      mul_le_mul_of_nonneg_left (by nlinarith [hm]) (by positivity)
    _ = (2*physicalMassLoss C*K^209)*mass := by ring

namespace PhysicalSource

variable {q T j : ℕ} {ν : Measure Ln} [IsFiniteMeasure ν]
  {B a ζ d : ℝ} {c u : P2} {P0 : Po} {A : Set Ln} {F H : Set Ev}
  (source : PhysicalSource q ν B a ζ d T j c u P0 A F H)

/-- The retained base law has a density bound relative to its OWN original
mass, with no intercept-width loss. -/
theorem group_base_density
    (hSA : source.S ⊆ A ×ˢ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹)
      ((j:ℝ)*((2:ℝ)^T)⁻¹+((2:ℝ)^T)⁻¹))
    {C w : ℝ} (hC : 0 < C) (hw : 0 < w) (hd : d ≤ 1)
    {G : Set Ev} (hGm : MeasurableSet G) (hGS : G ⊆ source.S)
    (hmass : physicalHeavyFloor ((2:ℝ)^T)⁻¹ (ν.real A) C source.K w d ≤
      (ν.prod volume).real G)
    (hcap : ∀ U : Set P3, MeasurableSet U →
      ((ν.prod volume).restrict G) {e | packetBase T j c u e ∈ U} ≤
        ENNReal.ofReal (source.K*(2*w)^d)*
          (ENNReal.ofReal (((2:ℝ)^T)⁻¹)*ν A)*volume U) :
    ∀ U : Set P3, MeasurableSet U →
      ((ν.prod volume).restrict G) {e | packetBase T j c u e ∈ U} ≤
        ENNReal.ofReal (2*physicalMassLoss C*source.K^209)*
          ((ν.prod volume).restrict G) univ*volume U := by
  have hh : 0 ≤ ((2:ℝ)^T)⁻¹ := by positivity
  have hK0 : 0 < source.K := by linarith [source.K_two]
  have hGfin : (ν.prod volume) G ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := ENNReal.ofReal (((2:ℝ)^T)⁻¹)*ν A) (by finiteness)
    simpa only [Measure.restrict_apply_univ] using
      original_block_mass_le ν A _ _ G (hGS.trans hSA)
  have hreal := physical_scalar_density_real hh (show 0 ≤ ν.real A from measureReal_nonneg)
    hC (by linarith [source.K_two]) hw hd hmass
  have hcoeff : ENNReal.ofReal (source.K*(2*w)^d)*
        (ENNReal.ofReal (((2:ℝ)^T)⁻¹)*ν A) ≤
      ENNReal.ofReal (2*physicalMassLoss C*source.K^209)*
        ((ν.prod volume).restrict G) univ := by
    calc
      _ = ENNReal.ofReal (source.K*(2*w)^d*(((2:ℝ)^T)⁻¹*ν.real A)) := by
        rw [ENNReal.ofReal_mul (p := source.K*(2*w)^d) (by positivity),
          ENNReal.ofReal_mul hh, measureReal_def,
          ENNReal.ofReal_toReal (measure_ne_top ν A)]
      _ ≤ ENNReal.ofReal ((2*physicalMassLoss C*source.K^209)*(ν.prod volume).real G) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (2*physicalMassLoss C*source.K^209)*
          ((ν.prod volume).restrict G) univ := by
        rw [ENNReal.ofReal_mul (by positivity [physicalMassLoss_pos hC]), measureReal_def,
          ENNReal.ofReal_toReal hGfin, Measure.restrict_apply_univ]
  intro U hU
  exact (hcap U hU).trans (mul_le_mul' hcoeff le_rfl)

end PhysicalSource

end

end Submission.Obl.k4_physical_parent_potential_candidates
