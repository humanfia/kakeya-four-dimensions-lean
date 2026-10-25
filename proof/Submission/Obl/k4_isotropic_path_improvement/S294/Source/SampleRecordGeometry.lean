-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleRecordGeometry, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordMiddleInFamily
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.GeometryEnvelope

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

noncomputable section

/-- The normalized exponent of the deterministic geometry envelope.
The literal envelope in `eventually_sample_record_geometry_envelope`
is `N^(recordGeometryExponent * L)`. -/
def recordGeometryExponent (tune : Tuning) (κ₁ d₁ : ℝ) (Ep : ℕ)
    (precision loss gain divisor : ℝ) : ℝ :=
  (tune.budget κ₁ d₁ Ep precision loss*(loss*gain/((Ep:ℝ)+1))/divisor)/
    (256*(FixedSourcePowers.power:ℝ))

theorem record_geometry_full_power_le :
    ((3*FixedSourcePowers.coreRadius+58+7)*FixedSourcePowers.jet+
      FixedSourcePowers.coreRadius+13) ≤ FixedSourcePowers.power := by
  have hh := Nat.mul_le_mul_left FixedSourcePowers.coreRadius FixedSourcePowers.jet_positive
  unfold FixedSourcePowers.power
  nlinarith

/-- Every actual geometry power costs at most gain/256, independently
of the front's arbitrary late prediction budget. -/
theorem record_geometry_exponent_bounds (tune : Tuning)
    {κ₁ d₁ precision loss gain divisor : ℝ} {Ep : ℕ}
    (hloss : 0 < loss) (hloss1 : loss ≤ 1) (hgain : 0 < gain)
    (hdivisor : 1 ≤ divisor) :
    let gamma := recordGeometryExponent tune κ₁ d₁ Ep precision loss gain divisor
    0 ≤ gamma ∧ gamma*(FixedSourcePowers.power:ℝ) ≤ gain/256 := by
  have hB := tune.budget_pos κ₁ d₁ Ep precision loss
  have hB1 := tune.budget_le_one κ₁ d₁ Ep precision loss
  have hEp : (1:ℝ) ≤ (Ep:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) Ep]
  have hEpp : 0 < (Ep:ℝ)+1 := zero_lt_one.trans_le hEp
  have hdivp : 0 < divisor := zero_lt_one.trans_le hdivisor
  have hpNat : 0 < FixedSourcePowers.power := by unfold FixedSourcePowers.power; omega
  have hp : 0 < (FixedSourcePowers.power:ℝ) := Nat.cast_pos.mpr hpNat
  have hsmall : loss*gain/((Ep:ℝ)+1) ≤ gain := by
    rw [div_le_iff₀ hEpp]
    nlinarith only [mul_le_mul_of_nonneg_right hloss1 hgain.le,
      mul_le_mul_of_nonneg_left hEp hgain.le]
  have hnum : tune.budget κ₁ d₁ Ep precision loss*(loss*gain/((Ep:ℝ)+1)) ≤ gain := by
    calc
      _ ≤ 1*(loss*gain/((Ep:ℝ)+1)) :=
        mul_le_mul_of_nonneg_right hB1 (by positivity)
      _ ≤ _ := by simpa only [one_mul] using hsmall
  have hwhole : tune.budget κ₁ d₁ Ep precision loss*(loss*gain/((Ep:ℝ)+1))/divisor ≤ gain := by
    rw [div_le_iff₀ hdivp]
    exact hnum.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hdivisor hgain.le)
  refine ⟨by unfold recordGeometryExponent; positivity,?_⟩
  have heq : recordGeometryExponent tune κ₁ d₁ Ep precision loss gain divisor*
      (FixedSourcePowers.power:ℝ)=
      (tune.budget κ₁ d₁ Ep precision loss*(loss*gain/((Ep:ℝ)+1))/divisor)/256 := by
    unfold recordGeometryExponent
    field_simp
  rw [heq]
  exact div_le_div_of_nonneg_right hwhole (by norm_num)

/-- Two simple room bounds choose a genuine record depth in the
registered core family. They pay all four literal geometry margins. -/
theorem exists_sample_record_middle_in_family
    (tune : Tuning) {κ₁ d₁ precision loss gain divisor δ₀ accuracy : ℝ}
    {Ep m i stop nfam : ℕ} {s : ℕ → ℝ}
    (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1)
    (hloss : 0 < loss) (hloss1 : loss ≤ 1) (hgain : 0 < gain)
    (hdivisor : 1 ≤ divisor) (hδ0 : 0 ≤ δ₀) (hδ : δ₀ ≤ gain/100)
    (haccuracy : 0 ≤ accuracy) (hm : 0 < m) (hgm : 8 ≤ gain*(m:ℝ))
    (hs : ∀ j, s j=((j:ℝ)+1)/m) (hnfam : 0 < nfam)
    (hwindow : (2*accuracy+4*gain)/κ₁ ≤ s stop-s i)
    (hfamily : accuracy+2*gain ≤ s (i+nfam-1)-s i) :
    let gamma := recordGeometryExponent tune κ₁ d₁ Ep precision loss gain divisor
    ∃ j : Fin nfam, i+j.val ≤ stop ∧
      gain+3*gamma+(κ₁*(s i-s stop)+2*δ₀) ≤ -accuracy ∧
      gain+((FixedSourcePowers.coreRadius+5:ℕ):ℝ)*gamma+
        (κ₁*(s (i+j.val)-s stop)+2*δ₀) ≤ 0 ∧
      gain+8*gamma-(s (i+j.val)-s i-2*δ₀) ≤ -accuracy ∧
      gain+(((3*FixedSourcePowers.coreRadius+58+7)*FixedSourcePowers.jet+
        FixedSourcePowers.coreRadius+13:ℕ):ℝ)*gamma+
        (κ₁*(s (i+j.val)-s stop)+2*δ₀) ≤ -accuracy := by
  let gamma := recordGeometryExponent tune κ₁ d₁ Ep precision loss gain divisor
  obtain ⟨hgamma,hpower⟩ := record_geometry_exponent_bounds tune hloss hloss1 hgain hdivisor
  change 0 ≤ gamma at hgamma
  change gamma*(FixedSourcePowers.power:ℝ) ≤ gain/256 at hpower
  have hpNat : 8 ≤ FixedSourcePowers.power := by unfold FixedSourcePowers.power; omega
  have hp8 : (8:ℝ) ≤ (FixedSourcePowers.power:ℝ) := by exact_mod_cast hpNat
  have hgamma8 : 8*gamma ≤ gain/256 := by
    calc
      _ ≤ (FixedSourcePowers.power:ℝ)*gamma := mul_le_mul_of_nonneg_right hp8 hgamma
      _ = gamma*(FixedSourcePowers.power:ℝ) := mul_comm _ _
      _ ≤ _ := hpower
  have hgamma3 : 3*gamma ≤ gain/256 := by
    linarith only [hgamma8,hgamma]
  have hP : (((3*FixedSourcePowers.coreRadius+58+7)*FixedSourcePowers.jet+
      FixedSourcePowers.coreRadius+13:ℕ):ℝ) ≤ (FixedSourcePowers.power:ℝ) := by
    exact_mod_cast record_geometry_full_power_le
  have hgammaP : (((3*FixedSourcePowers.coreRadius+58+7)*FixedSourcePowers.jet+
      FixedSourcePowers.coreRadius+13:ℕ):ℝ)*gamma ≤ gain/256 := by
    calc
      _ ≤ (FixedSourcePowers.power:ℝ)*gamma := mul_le_mul_of_nonneg_right hP hgamma
      _ = gamma*(FixedSourcePowers.power:ℝ) := mul_comm _ _
      _ ≤ _ := hpower
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hstep : 1/(m:ℝ) ≤ gain/8 := by
    rw [div_le_div_iff₀ hmR (by norm_num : (0:ℝ) < 8)]
    linarith only [hgm]
  have hleft : accuracy+8*gamma+2*δ₀+gain+1/(m:ℝ) ≤ accuracy+2*gain := by
    linarith only [hgamma8,hδ,hstep,hgain]
  have hright : (accuracy+8*gamma+2*δ₀+gain)+
      (accuracy+(((3*FixedSourcePowers.coreRadius+58+7)*FixedSourcePowers.jet+
        FixedSourcePowers.coreRadius+13:ℕ):ℝ)*gamma+2*δ₀+gain)/κ₁+1/(m:ℝ) ≤
        (2*accuracy+4*gain)/κ₁ := by
    rw [le_div_iff₀ hκ]
    have hh := mul_le_mul_of_nonneg_left hleft hκ.le
    have hsmall : (accuracy+2*gain)*κ₁ ≤ accuracy+2*gain :=
      mul_le_of_le_one_right (by positivity) hκ1
    have heq : ((accuracy+8*gamma+2*δ₀+gain)+
        (accuracy+(((3*FixedSourcePowers.coreRadius+58+7)*FixedSourcePowers.jet+
          FixedSourcePowers.coreRadius+13:ℕ):ℝ)*gamma+2*δ₀+gain)/κ₁+1/(m:ℝ))*κ₁=
        (accuracy+8*gamma+2*δ₀+gain+1/(m:ℝ))*κ₁+
        (accuracy+(((3*FixedSourcePowers.coreRadius+58+7)*FixedSourcePowers.jet+
          FixedSourcePowers.coreRadius+13:ℕ):ℝ)*gamma+2*δ₀+gain) := by field_simp; ring
    rw [heq]
    nlinarith only [hh,hsmall,hgammaP,hδ,hgain]
  apply exists_record_middle_in_consecutive_family hm hs FixedSourcePowers.coreRadius
    FixedSourcePowers.jet (3*FixedSourcePowers.coreRadius+58) i stop nfam hnfam hκ hδ0 hgamma
    hgain.le haccuracy _ (hright.trans hwindow) (hleft.trans hfamily)
  have hh := (div_le_iff₀ hκ).mp hwindow
  nlinarith only [hh,hgamma3,hδ,hgain,haccuracy]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
