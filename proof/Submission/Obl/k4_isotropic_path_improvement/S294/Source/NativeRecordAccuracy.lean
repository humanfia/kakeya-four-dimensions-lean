-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeRecordAccuracy, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesignPowers
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordAuxiliaryReferences

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData)

noncomputable section

/-- One normalized accuracy for both actual record references,
including the native auxiliary cutoff and both physical transports. -/
def nativeRecordAccuracyCoeff (κ₁ d : ℝ) (Ep : ℕ) (precision loss : ℝ) : ℝ :=
  max (max (NativeDesign.graphLowerCoeff κ₁ d Ep precision)
    (NativeDesign.auxiliaryChiCoeff κ₁ d Ep precision loss*
      (NativeDesign.auxiliaryFinest κ₁ d Ep precision loss:ℝ)))
    (6*(((Ep:ℝ)+1)*precision+3)/κ₁)+1

/-- The concrete depth dominates every component of the exact
reference accuracy. No further native scale comparison is assumed. -/
theorem native_record_accuracy_le_depth
    {κ₁ d precision loss : ℝ} (Ep : ℕ) (hv : NativeDesign.Valid κ₁ d precision loss) :
    0 ≤ nativeRecordAccuracyCoeff κ₁ d Ep precision loss ∧
      nativeRecordAccuracyCoeff κ₁ d Ep precision loss ≤ 2*NativeDesign.depth κ₁ d Ep precision loss := by
  obtain ⟨hd0,hd1,hκ,hκ1,hprecision,hloss,hloss1⟩ := hv
  let X := ((Ep:ℝ)+1)*precision+3
  let W := 2+(NativeDesign.rhoPower κ₁ Ep precision:ℝ)+
    (NativeDesign.auxiliaryFinest κ₁ d Ep precision loss:ℝ)+
      |NativeDesign.graphLowerCoeff κ₁ d Ep precision|+|NativeDesign.floorEndCoeff κ₁ d Ep precision|
  let D := NativeDesign.depth κ₁ d Ep precision loss
  have hEp : (1:ℝ) ≤ (Ep:ℝ)+1 := by linarith only [Nat.cast_nonneg (α := ℝ) Ep]
  have hEpPos : 0 < (Ep:ℝ)+1 := zero_lt_one.trans_le hEp
  have hX : 1 ≤ X := by
    have hh := one_le_mul_of_one_le_of_one_le hEp hprecision
    dsimp only [X]
    linarith only [hh]
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hRho0 : (0:ℝ) ≤ NativeDesign.rhoPower κ₁ Ep precision := Nat.cast_nonneg _
  have hFinest0 : (0:ℝ) ≤ NativeDesign.auxiliaryFinest κ₁ d Ep precision loss := Nat.cast_nonneg _
  have hGraphAbs : 0 ≤ |NativeDesign.graphLowerCoeff κ₁ d Ep precision| := abs_nonneg _
  have hEndAbs : 0 ≤ |NativeDesign.floorEndCoeff κ₁ d Ep precision| := abs_nonneg _
  have hW : 1 ≤ W := by dsimp only [W]; linarith only [hRho0,hFinest0,hGraphAbs,hEndAbs]
  have hWD : W ≤ D := by
    have hh : W ≤ W^4 := le_self_pow₀ hW (by norm_num)
    exact hh.trans (le_max_right 1 (W^4))
  have hD : 1 ≤ D := NativeDesign.one_le_depth _ _ _ _ _
  have hRhoD : (NativeDesign.rhoPower κ₁ Ep precision:ℝ) ≤ D := by
    apply le_trans _ hWD
    dsimp only [W]
    linarith only [hFinest0,hGraphAbs,hEndAbs]
  have hFinestD : (NativeDesign.auxiliaryFinest κ₁ d Ep precision loss:ℝ) ≤ D := by
    apply le_trans _ hWD
    dsimp only [W]
    linarith only [hRho0,hGraphAbs,hEndAbs]
  have hGraphD : NativeDesign.graphLowerCoeff κ₁ d Ep precision ≤ D := by
    apply le_trans (le_abs_self _) (le_trans _ hWD)
    dsimp only [W]
    linarith only [hRho0,hFinest0,hEndAbs]
  have hLossRatio : loss/((Ep:ℝ)+1) ≤ 1 := by
    rw [div_le_one hEpPos]
    exact hloss1.trans hEp
  have hMass : NativeDesign.massCoeff κ₁ d Ep precision loss ≤ 1 := by
    unfold NativeDesign.massCoeff
    apply (div_le_one (zero_lt_one.trans_le (le_max_left 1 κ₁⁻¹))).mpr
    apply le_trans _ (le_max_left 1 κ₁⁻¹)
    rw [div_le_one (by positivity : (0:ℝ) <
      100000000*((NativeDesign.residualLength κ₁ d Ep precision loss:ℝ)+1))]
    exact (min_le_left _ _).trans (hLossRatio.trans (by
      have hh : (0:ℝ) ≤ NativeDesign.residualLength κ₁ d Ep precision loss := Nat.cast_nonneg _
      linarith only [hh]))
  have hRegLength : (1:ℝ) ≤ NativeDesign.regularityLength κ₁ d Ep precision loss := by
    exact_mod_cast Nat.succ_le_of_lt (NativeDesign.regularityLength_pos κ₁ d Ep precision loss)
  have hReg : NativeDesign.regularityCoeff κ₁ d Ep precision loss ≤ 1 := by
    unfold NativeDesign.regularityCoeff
    rw [div_le_one (by positivity : (0:ℝ) < 400*(NativeDesign.regularityLength κ₁ d Ep precision loss:ℝ))]
    exact hMass.trans (by linarith only [hRegLength])
  have hCoefficient : NativeDesign.coefficientCoeff κ₁ d Ep precision loss ≤ 1 := by
    have hh := NativeDesign.coefficient_le_regularity κ₁ d (Ep:=Ep) (precision:=precision) hloss
    linarith only [hh,hReg]
  have hChi : NativeDesign.auxiliaryChiCoeff κ₁ d Ep precision loss ≤ 1 := by
    unfold NativeDesign.auxiliaryChiCoeff
    linarith only [hCoefficient]
  have hAuxD : NativeDesign.auxiliaryChiCoeff κ₁ d Ep precision loss*
      (NativeDesign.auxiliaryFinest κ₁ d Ep precision loss:ℝ) ≤ D := by
    calc
      _ ≤ (NativeDesign.auxiliaryFinest κ₁ d Ep precision loss:ℝ) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hChi hFinest0
      _ ≤ _ := hFinestD
  have hRho : 100*NativeDesign.clockCoeff Ep precision/κ₁ ≤
      (NativeDesign.rhoPower κ₁ Ep precision:ℝ) := by
    have hh := Nat.le_ceil (100*NativeDesign.clockCoeff Ep precision/κ₁)
    unfold NativeDesign.rhoPower
    push_cast
    linarith only [hh]
  have hClockD : 6*X/κ₁ ≤ D := by
    apply le_trans _ (hRho.trans hRhoD)
    apply div_le_div_of_nonneg_right _ hκ.le
    change 6*X ≤ 100*(4*X)
    nlinarith only [hX0]
  have hMax : max (max (NativeDesign.graphLowerCoeff κ₁ d Ep precision)
      (NativeDesign.auxiliaryChiCoeff κ₁ d Ep precision loss*
        (NativeDesign.auxiliaryFinest κ₁ d Ep precision loss:ℝ))) (6*X/κ₁) ≤ D :=
    max_le (max_le hGraphD hAuxD) hClockD
  have hMax0 : 0 ≤ max (max (NativeDesign.graphLowerCoeff κ₁ d Ep precision)
      (NativeDesign.auxiliaryChiCoeff κ₁ d Ep precision loss*
        (NativeDesign.auxiliaryFinest κ₁ d Ep precision loss:ℝ))) (6*X/κ₁) :=
    (by positivity : (0:ℝ) ≤ 6*X/κ₁).trans (le_max_right _ _)
  change 0 ≤ _+1 ∧ _+1 ≤ 2*D
  exact ⟨by linarith only [hMax0],by linarith only [hMax,hD]⟩

/-- The exact sample references have the normalized accuracy chosen
by NativeDesign, including the auxiliary native cutoff. -/
theorem sample_native_record_reference_floors
    {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    {d₁ precision loss gain graphMesh : ℝ} {Ep i : ℕ}
    (hv : NativeDesign.Valid κ₁ d₁ precision loss)
    (hN : 1 ≤ d.N k) (hL : 0 < d.L) (hgain : 0 < gain)
    (hδ0 : 0 ≤ δ₀) (hδ : δ₀ ≤ gain/100) (hm : 0 < m) (hgm : 8 ≤ gain*(m:ℝ))
    (hs : ∀ j, s j=((j:ℝ)+1)/m) (hi : i < m)
    (hib : i+childOffset κ₁ Ep precision gain m < m)
    (hconstant : 6 ≤ d.N k^(gain*d.L))
    (hgraph : d.N k^(-(NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision*(gain*d.L))) ≤ graphMesh) :
    let ib := i+childOffset κ₁ Ep precision gain m
    let epsilon := epsOf Ep precision loss gain (d.N k) d.L (p.r i) (p.r ib) (p.T i) (p.T ib)
    let chi := NativeDesign.auxiliaryChiCoeff κ₁ d₁ Ep precision loss*(gain*d.L)
    let finest : ℝ := NativeDesign.auxiliaryFinest κ₁ d₁ Ep precision loss
    let referenceMesh := min graphMesh (((d.N k)^chi)^(-finest))
    let accuracy := nativeRecordAccuracyCoeff κ₁ d₁ Ep precision loss*gain
    d.N k^(-accuracy*d.L) ≤
      recordReference referenceMesh epsilon ((2:ℝ)^p.T i/(2:ℝ)^p.T ib) ∧
    d.N k^(-accuracy*d.L) ≤
      recordReference referenceMesh epsilon (δ (d.N k) (p.r ib)/δ (d.N k) (p.r i)) := by
  obtain ⟨_hd0,_hd1,hκ,hκ1,hprecision,hloss,hloss1⟩ := hv
  have hraw := sample_auxiliary_record_reference_floors
    (chi := NativeDesign.auxiliaryChiCoeff κ₁ d₁ Ep precision loss*(gain*d.L))
    (finest := (NativeDesign.auxiliaryFinest κ₁ d₁ Ep precision loss:ℝ))
    hp hN hL hκ hκ1 hprecision hloss hloss1 hgain hδ0 hδ hm hgm hs hi hib hconstant hgraph
  have hGainL : 0 ≤ gain*d.L := (mul_pos hgain hL).le
  have hAux : (NativeDesign.auxiliaryChiCoeff κ₁ d₁ Ep precision loss*(gain*d.L))*
      (NativeDesign.auxiliaryFinest κ₁ d₁ Ep precision loss:ℝ)=
      (NativeDesign.auxiliaryChiCoeff κ₁ d₁ Ep precision loss*
        (NativeDesign.auxiliaryFinest κ₁ d₁ Ep precision loss:ℝ))*(gain*d.L) := by ring
  have hPhysical : 2*(3*(((Ep:ℝ)+1)*precision+3)*gain*d.L/κ₁)=
      (6*(((Ep:ℝ)+1)*precision+3)/κ₁)*(gain*d.L) := by ring
  have hPower : max
      (max (NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision*(gain*d.L))
        ((NativeDesign.auxiliaryChiCoeff κ₁ d₁ Ep precision loss*(gain*d.L))*
          (NativeDesign.auxiliaryFinest κ₁ d₁ Ep precision loss:ℝ)))
      (2*(3*(((Ep:ℝ)+1)*precision+3)*gain*d.L/κ₁))+gain*d.L=
        (nativeRecordAccuracyCoeff κ₁ d₁ Ep precision loss*gain)*d.L := by
    rw [hAux,hPhysical,←max_mul_of_nonneg _ _ hGainL,←max_mul_of_nonneg _ _ hGainL]
    unfold nativeRecordAccuracyCoeff
    ring
  dsimp only at hraw ⊢
  simpa only [hPower,neg_mul] using hraw

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
