-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleFamilyAtChoices, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleChoices
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordWindowRoom
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleAtNumerics

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

noncomputable section

/-- The literal family choice agrees with the record constructor's
family, and contains the actual child level. Both facts follow from
the existing window room, before any path or root package is supplied. -/
theorem sample_family_at_choices
    (tune : Tuning) {κ₁ d₁ precision loss gain delta : ℝ} {Ep m C : ℕ} {s : ℕ → ℝ}
    (hv : NativeDesign.Valid κ₁ d₁ precision loss)
    (hdepth : tune.depth κ₁ d₁ Ep precision loss=NativeDesign.depth κ₁ d₁ Ep precision loss)
    (hgain : 0 < gain) (hdelta0 : 0 ≤ delta) (hm : 0 < m)
    (hs : ∀ j, s j=((j:ℝ)+1)/m) (hslack : censusSlack ≤ tune.slack)
    (hdelta : delta ≤ tolOf tune κ₁ d₁ Ep precision loss gain) (hdeltaGain : delta ≤ gain/100)
    (hgm : 8 ≤ gain*(m:ℝ))
    (hC : windowOf tune κ₁ d₁ Ep precision loss gain*(m:ℝ) ≤ C) :
    let ub := ubOf tune κ₁ d₁ Ep precision loss gain
    let g := familyMarginOf κ₁ delta ub m
    g ≤ C ∧ nfamAt κ₁ delta ub m C=C-g+1 ∧
      childOffset κ₁ Ep precision gain m < nfamAt κ₁ delta ub m C := by
  let X := ((Ep:ℝ)+1)*precision+3
  let accuracy := nativeRecordAccuracyCoeff κ₁ d₁ Ep precision loss
  let g := familyMarginOf κ₁ delta (ubOf tune κ₁ d₁ Ep precision loss gain) m
  let c := childOffset κ₁ Ep precision gain m
  have hκ := hv.2.2.1
  have hκ1 := hv.2.2.2.1
  have hprecision := hv.2.2.2.2.1
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hX0 : 0 ≤ X := by dsimp only [X]; have hp0 := zero_le_one.trans hprecision; positivity
  obtain ⟨hg,_hwindow,hfamily⟩ := record_window_room tune hdepth hv hgain hdelta0 hm hs hslack
    hdelta hdeltaGain hgm hC (i:=0)
  change g ≤ C at hg
  have hFamilyGap : s (0+(C-g+1)-1)-s 0=((C:ℝ)-g)/m := by
    have hidx : 0+(C-g+1)-1=C-g := by omega
    rw [hidx,hs,hs,Nat.cast_sub hg]
    ring
  change accuracy*gain+2*gain ≤ s (0+(C-g+1)-1)-s 0 at hfamily
  rw [hFamilyGap] at hfamily
  have hmg : 1/(m:ℝ) ≤ gain/κ₁ := by
    rw [div_le_div_iff₀ hmR hκ]
    nlinarith only [hgm,hκ1]
  have hcdiv := childOffset_div_le hκ hm hgain hprecision hmg (Ep:=Ep)
  change (c:ℝ)/m ≤ 2*X*gain/κ₁ at hcdiv
  have hMax := le_max_right
    (max (NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision)
      (NativeDesign.auxiliaryChiCoeff κ₁ d₁ Ep precision loss*(NativeDesign.auxiliaryFinest κ₁ d₁ Ep precision loss:ℝ)))
    (6*X/κ₁)
  have hSix : 6*X/κ₁ ≤ accuracy := by
    dsimp only [accuracy,nativeRecordAccuracyCoeff]
    dsimp only [X] at hMax
    linarith only [hMax]
  have hTwo : 2*X/κ₁ ≤ accuracy :=
    (div_le_div_of_nonneg_right (by linarith only [hX0]) hκ.le).trans hSix
  have hcSmall : (c:ℝ)/m ≤ accuracy*gain+2*gain := by
    calc
      _ ≤ 2*X*gain/κ₁ := hcdiv
      _ = (2*X/κ₁)*gain := by ring
      _ ≤ accuracy*gain := mul_le_mul_of_nonneg_right hTwo hgain.le
      _ ≤ _ := by linarith only [hgain]
  have hcReal : (c:ℝ) ≤ (C:ℝ)-g := (div_le_div_iff_of_pos_right hmR).mp (hcSmall.trans hfamily)
  have hcNat : c ≤ C-g := by exact_mod_cast (by simpa only [Nat.cast_sub hg] using hcReal : (c:ℝ) ≤ (C-g:ℕ))
  refine ⟨hg,?_,?_⟩
  · unfold nfamAt
    change C+1-g=C-g+1
    omega
  · unfold nfamAt
    change c < C+1-g
    omega

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
