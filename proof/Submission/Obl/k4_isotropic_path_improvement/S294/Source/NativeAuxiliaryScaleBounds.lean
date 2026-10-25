-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeAuxiliaryScaleBounds, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeScaleDesignBounds
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeRecordAccuracy
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleAtNumerics

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData)
open Parent.Qualification
open Parent.Qualification.PhysicalModel

noncomputable section

/-- The actual auxiliary fine and coarse exponents enclose the
original census resolution and coefficient-floor starting width. -/
theorem native_auxiliary_exponent_bounds
    {κ₁ d₁ precision loss : ℝ} {Ep : ℕ} (hv : NativeDesign.Valid κ₁ d₁ precision loss) :
    NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision+NativeDesign.coefficientCoeff κ₁ d₁ Ep precision loss/5 ≤
        NativeDesign.auxiliaryChiCoeff κ₁ d₁ Ep precision loss*(NativeDesign.auxiliaryFinest κ₁ d₁ Ep precision loss:ℝ) ∧
      NativeDesign.auxiliaryChiCoeff κ₁ d₁ Ep precision loss/(NativeDesign.auxiliaryFinest κ₁ d₁ Ep precision loss:ℝ) ≤
        NativeDesign.floorStartCoeff κ₁ d₁ Ep precision loss ∧
      NativeDesign.auxiliaryChiCoeff κ₁ d₁ Ep precision loss/(NativeDesign.auxiliaryFinest κ₁ d₁ Ep precision loss:ℝ) ≤
        NativeDesign.graphTargetCoeff κ₁ d₁ Ep precision := by
  have hp := hv.2.2.2.2.1
  have hl := hv.2.2.2.2.2.1
  have hk := hv.2.2.1
  have hmass := NativeDesign.massCoeff_le_one κ₁ d₁ (Ep:=Ep) (precision:=precision) hv.2.2.2.2.2.2
  have hreg := NativeDesign.regularityCoeff_le_mass κ₁ d₁ (Ep:=Ep) (precision:=precision) hl
  have hcoef := NativeDesign.coefficient_le_mass_quarter κ₁ d₁ (Ep:=Ep) (precision:=precision) hl
  have hfloor := NativeDesign.floorEndCoeff_pos κ₁ d₁ (Ep:=Ep) hp
  have hAux := NativeDesign.auxiliary_finest_covers_graph κ₁ d₁ (Ep:=Ep) (precision:=precision) hl
  have hCoarse := NativeDesign.auxiliary_coarse_below_floor_start κ₁ d₁ (Ep:=Ep) (precision:=precision) hl
  have hRho := NativeDesign.rhoCoeff_pos κ₁ d₁ (Ep:=Ep) hp
  have hZeta := NativeDesign.zetaCoeff_pos κ₁ d₁ (Ep:=Ep) hp
  have hE4 : 4 ≤ NativeDesign.floorEndCoeff κ₁ d₁ Ep precision := by
    unfold NativeDesign.floorEndCoeff
    linarith only [hRho,hZeta]
  have hstartTarget : NativeDesign.floorStartCoeff κ₁ d₁ Ep precision loss ≤
      NativeDesign.graphTargetCoeff κ₁ d₁ Ep precision := by
    have hC := NativeDesign.clockCoeff_pos (Ep:=Ep) hp
    have hpositive : 0 ≤ 16*NativeDesign.clockCoeff Ep precision/κ₁ := by positivity
    unfold NativeDesign.floorStartCoeff NativeDesign.graphTargetCoeff
    linarith only [hreg,hmass,hE4,hpositive]
  exact ⟨by linarith only [hAux,hcoef,hmass,hfloor],hCoarse,hCoarse.trans hstartTarget⟩

/-- Both exact auxiliary query bounds of `native_root_step`, and its
coefficient-floor starting bound, from the constructed scale data and
the actual graph lower power and logarithmic census steps. -/
theorem native_auxiliary_resolution_bounds
    {q : NativeScaleDesign} {N sigma Kcensus stripWidth theta : ℝ} {T fine steps : ℕ}
    (native : NativeScaleData q N sigma T fine steps Kcensus stripWidth theta)
    (hN : 1 < N)
    (hgraph : N^(-(NativeDesign.graphLowerCoeff q.kappa1 q.dimension q.Ep q.precision*q.gainL)) ≤ native.scales.b)
    (hupper : native.scales.b ≤ N^(-q.target))
    (hsteps : (2:ℝ)^steps ≤ N^(q.coefficient/5)) :
    let chi := NativeDesign.auxiliaryChiCoeff q.kappa1 q.dimension q.Ep q.precision q.loss*q.gainL
    let finest : ℝ := NativeDesign.auxiliaryFinest q.kappa1 q.dimension q.Ep q.precision q.loss
    1 < N^chi ∧ (N^chi)^(-finest) ≤ native.scales.resolution ∧
      native.scales.resolution ≤ (N^chi)^(-finest⁻¹) ∧
      Jets2.dyadicParameterWidth native.scales.floorStart ≤ (N^chi)^(-finest⁻¹) := by
  let A := NativeDesign.auxiliaryChiCoeff q.kappa1 q.dimension q.Ep q.precision q.loss
  let finest : ℝ := NativeDesign.auxiliaryFinest q.kappa1 q.dimension q.Ep q.precision q.loss
  let chi := A*q.gainL
  have hNp : 0 < N := zero_lt_one.trans hN
  have hA : 0 < A := NativeDesign.auxiliaryChiCoeff_pos q.kappa1 q.dimension q.valid.2.2.2.2.2.1
  have hchi : 0 < chi := mul_pos hA q.gainL_pos
  obtain ⟨hFine,hCoarseStart,hCoarseTarget⟩ := native_auxiliary_exponent_bounds q.valid (Ep:=q.Ep)
  have hFineL := mul_le_mul_of_nonneg_right hFine q.gainL_pos.le
  have hCoarseL := mul_le_mul_of_nonneg_right hCoarseTarget q.gainL_pos.le
  have hStartL := mul_le_mul_of_nonneg_right hCoarseStart q.gainL_pos.le
  have hFineEq : (N^chi)^(-finest)=N^(-(A*finest*q.gainL)) := by
    rw [←Real.rpow_mul hNp.le]
    congr 1
    dsimp only [chi]
    ring
  have hCoarseEq : (N^chi)^(-finest⁻¹)=N^(-((A/finest)*q.gainL)) := by
    rw [←Real.rpow_mul hNp.le]
    congr 1
    dsimp only [chi]
    ring
  have hResolution : native.scales.resolution=native.scales.b/(2:ℝ)^steps := by
    rw [native.resolution_eq,native.b_eq]
  refine ⟨Real.one_lt_rpow hN hchi,?_,?_,?_⟩
  · rw [hFineEq,hResolution,le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^steps)]
    calc
      _ ≤ N^(-(A*finest*q.gainL))*N^(q.coefficient/5) :=
        mul_le_mul_of_nonneg_left hsteps (Real.rpow_nonneg hNp.le _)
      _ = N^(-(A*finest*q.gainL)+q.coefficient/5) := (Real.rpow_add hNp _ _).symm
      _ ≤ N^(-(NativeDesign.graphLowerCoeff q.kappa1 q.dimension q.Ep q.precision*q.gainL)) :=
        Real.rpow_le_rpow_of_exponent_le hN.le (by
          change _ ≤ (A*finest)*q.gainL at hFineL
          change -(A*finest*q.gainL)+(NativeDesign.coefficientCoeff q.kappa1 q.dimension q.Ep q.precision q.loss*q.gainL)/5 ≤ _
          linarith only [hFineL])
      _ ≤ _ := hgraph
  · rw [hCoarseEq]
    calc
      _ ≤ native.scales.b := by
        rw [hResolution]
        exact div_le_self native.scales.hb.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
      _ ≤ N^(-q.target) := hupper
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN.le (by
        change (A/finest)*q.gainL ≤ NativeDesign.graphTargetCoeff q.kappa1 q.dimension q.Ep q.precision*q.gainL at hCoarseL
        change -(NativeDesign.graphTargetCoeff q.kappa1 q.dimension q.Ep q.precision*q.gainL) ≤ -((A/finest)*q.gainL)
        exact neg_le_neg hCoarseL)
  · rw [hCoarseEq]
    refine native.floorStartWidth_upper.trans (Real.rpow_le_rpow_of_exponent_le hN.le ?_)
    change (A/finest)*q.gainL ≤ (NativeDesign.regularityCoeff q.kappa1 q.dimension q.Ep q.precision q.loss/1000)*q.gainL at hStartL
    change -(NativeDesign.regularityCoeff q.kappa1 q.dimension q.Ep q.precision q.loss*q.gainL/1000) ≤ -((A/finest)*q.gainL)
    linarith only [hStartL]

/-- The auxiliary fine query lower bound and the available depth room
also resolve the actual original height band to the end of the path. -/
theorem auxiliary_resolution_resolves_end
    {N chi finest L r resolution : ℝ} (hN : 1 ≤ N)
    (hdepth : r+chi*finest ≤ L) (hresolution : (N^chi)^(-finest) ≤ resolution) :
    N^(-(L-r)) ≤ 4*resolution := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hresolved : N^(-(L-r)) ≤ resolution := by
    apply le_trans _ hresolution
    rw [←Real.rpow_mul hNp.le]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hdepth])
  have hres0 : 0 ≤ resolution := (Real.rpow_nonneg hNp.le (-(L-r))).trans hresolved
  linarith only [hresolved,hres0]

/-- The finite native depth also dominates its literal palette floor. -/
theorem native_depth_dominates_floor (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) :
    NativeDesign.floorEndCoeff κ₁ d₁ Ep precision ≤ NativeDesign.depth κ₁ d₁ Ep precision loss := by
  let W := 2+(NativeDesign.rhoPower κ₁ Ep precision:ℝ)+
    (NativeDesign.auxiliaryFinest κ₁ d₁ Ep precision loss:ℝ)+
      |NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision|+|NativeDesign.floorEndCoeff κ₁ d₁ Ep precision|
  have hr : (0:ℝ) ≤ NativeDesign.rhoPower κ₁ Ep precision := Nat.cast_nonneg _
  have hf : (0:ℝ) ≤ NativeDesign.auxiliaryFinest κ₁ d₁ Ep precision loss := Nat.cast_nonneg _
  have hg := abs_nonneg (NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision)
  have he := abs_nonneg (NativeDesign.floorEndCoeff κ₁ d₁ Ep precision)
  have hW : 1 ≤ W := by dsimp only [W]; linarith only [hr,hf,hg,he]
  have hWD : W ≤ NativeDesign.depth κ₁ d₁ Ep precision loss :=
    (le_self_pow₀ hW (by norm_num : 4 ≠ 0)).trans (le_max_right 1 (W^4))
  refine le_trans (le_abs_self _) (le_trans ?_ hWD)
  dsimp only [W]
  linarith only [hr,hf,hg]

/-- The front's literal fine palette is below the native palette
floor at the actual tuning depth. -/
theorem native_sample_palette_floor
    (tune : Tuning) {κ₁ d₁ precision loss gain L delta N : ℝ} {Ep : ℕ}
    (hv : NativeDesign.Valid κ₁ d₁ precision loss)
    (hdepth : tune.depth κ₁ d₁ Ep precision loss=NativeDesign.depth κ₁ d₁ Ep precision loss)
    (hN : 1 ≤ N) (hgain : 0 < gain) (hL : 0 < L) (hdelta0 : 0 ≤ delta) :
    N^(-ueOf tune κ₁ d₁ Ep precision loss gain delta L) ≤
      N^(-(NativeDesign.floorEndCoeff κ₁ d₁ Ep precision*(gain*L))) := by
  have hk := hv.2.2.1
  have hk1 := hv.2.2.2.1
  have hp := hv.2.2.2.2.1
  let X := ((Ep:ℝ)+1)*precision+3
  let D := NativeDesign.depth κ₁ d₁ Ep precision loss
  have hD : 1 ≤ D := NativeDesign.one_le_depth _ _ _ _ _
  have hX : 1 ≤ X := by
    have hE : (1:ℝ) ≤ (Ep:ℝ)+1 := by linarith only [Nat.cast_nonneg (α:=ℝ) Ep]
    have hh := one_le_mul_of_one_le_of_one_le hE hp
    dsimp only [X]
    linarith only [hh]
  have hfactor : 1 ≤ 4*X/κ₁ := by rw [le_div_iff₀ hk]; linarith only [hX,hk1]
  have hroom : NativeDesign.floorEndCoeff κ₁ d₁ Ep precision*(gain*L) ≤
      paletteExpOf tune κ₁ d₁ Ep precision loss gain L := by
    calc
      _ ≤ D*(gain*L) := mul_le_mul_of_nonneg_right (native_depth_dominates_floor κ₁ d₁ Ep precision loss) (by positivity)
      _ ≤ (4*X/κ₁)*(D*(gain*L)) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor (by positivity : (0:ℝ) ≤ D*(gain*L))
      _ = _ := by unfold paletteExpOf; rw [hdepth]; dsimp only [X,D]; ring
  apply Real.rpow_le_rpow_of_exponent_le hN
  unfold ueOf
  have hd := mul_nonneg hdelta0 hL.le
  linarith only [hroom,hd]

/-- The actual chosen gain leaves uniform room against the complete
native depth before the path and sample are supplied. -/
theorem native_gain_depth_le
    (tune : Tuning) {κ₁ d₁ precision loss e0 : ℝ} {Ep : ℕ}
    (hv : NativeDesign.Valid κ₁ d₁ precision loss) (he0 : 0 < e0) :
    gainOf tune κ₁ d₁ Ep precision loss e0*tune.depth κ₁ d₁ Ep precision loss ≤ 1/16 := by
  obtain ⟨hd0,hd1,hk,hk1,hp,hl,hl1⟩ := hv
  have hgain := gainOf_pos (tune:=tune) (Ep:=Ep) hk hd1 hp hl he0
  have hD := tune.one_le_depth κ₁ d₁ Ep precision loss
  have hscaled := gain_scaled_le (Ep:=Ep) tune hk hd0 hd1 hp hl hl1 he0
  have hE : (1:ℝ) ≤ (Ep:ℝ)+1 := by linarith only [Nat.cast_nonneg (α:=ℝ) Ep]
  have hX : 1 ≤ ((Ep:ℝ)+1)*precision+3 := by
    have hh := one_le_mul_of_one_le_of_one_le hE hp
    linarith only [hh]
  have hsquareD : (1-d₁)^2 ≤ 1 := by nlinarith only [hd0,hd1]
  have hsquareK : κ₁^2 ≤ 1 := by nlinarith only [hk,hk1]
  have hProduct : (1-d₁)^2*κ₁^2 ≤ 1 := by
    calc
      _ ≤ 1*κ₁^2 := mul_le_mul_of_nonneg_right hsquareD (sq_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using hsquareK
  have hSmall : (1-d₁)^2*κ₁^2/(2:ℝ)^48 ≤ 1/16 := by
    apply (div_le_div_of_nonneg_right hProduct (by norm_num)).trans
    norm_num
  have hXmul := mul_le_mul_of_nonneg_right hX (by positivity : (0:ℝ) ≤ gainOf tune κ₁ d₁ Ep precision loss e0*tune.depth κ₁ d₁ Ep precision loss)
  nlinarith only [hscaled,hSmall,hXmul]

/-- The actual auxiliary finest depth fits before the end of the
path at every sample in the first half of the prepared grid. -/
theorem native_sample_auxiliary_depth_room
    (tune : Tuning) {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ delta sigma : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s delta Mp Dp sigma)
    {d₁ precision loss e0 : ℝ} {Ep i : ℕ}
    (hv : NativeDesign.Valid κ₁ d₁ precision loss)
    (hdepth : tune.depth κ₁ d₁ Ep precision loss=NativeDesign.depth κ₁ d₁ Ep precision loss)
    (he0 : 0 < e0) (hL : 0 < d.L) (hi : i < m) (hhalf : s i ≤ 1/2)
    (hdelta : delta ≤ gainOf tune κ₁ d₁ Ep precision loss e0/100) :
    let gain := gainOf tune κ₁ d₁ Ep precision loss e0
    let chi := NativeDesign.auxiliaryChiCoeff κ₁ d₁ Ep precision loss*(gain*d.L)
    let finest : ℝ := NativeDesign.auxiliaryFinest κ₁ d₁ Ep precision loss
    p.r i+chi*finest ≤ d.L := by
  let gain := gainOf tune κ₁ d₁ Ep precision loss e0
  let D := NativeDesign.depth κ₁ d₁ Ep precision loss
  have hgain := gainOf_pos (tune:=tune) (Ep:=Ep) hv.2.2.1 hv.2.1 hv.2.2.2.2.1 hv.2.2.2.2.2.1 he0
  change 0 < gain at hgain
  change delta ≤ gain/100 at hdelta
  have hD := NativeDesign.one_le_depth κ₁ d₁ Ep precision loss
  have hGD := native_gain_depth_le (Ep:=Ep) tune hv he0
  rw [hdepth] at hGD
  change gain*D ≤ 1/16 at hGD
  have hGainSmall : gain ≤ 1/16 := by
    have hh := mul_le_mul_of_nonneg_left hD hgain.le
    change gain*1 ≤ gain*D at hh
    linarith only [hh,hGD]
  have hAccuracy := (native_record_accuracy_le_depth (Ep:=Ep) hv).2
  have hAux : NativeDesign.auxiliaryChiCoeff κ₁ d₁ Ep precision loss*
      (NativeDesign.auxiliaryFinest κ₁ d₁ Ep precision loss:ℝ) ≤ 2*D := by
    have hh := le_max_right (NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision)
      (NativeDesign.auxiliaryChiCoeff κ₁ d₁ Ep precision loss*(NativeDesign.auxiliaryFinest κ₁ d₁ Ep precision loss:ℝ))
    have hh2 := le_max_left (max (NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision)
      (NativeDesign.auxiliaryChiCoeff κ₁ d₁ Ep precision loss*(NativeDesign.auxiliaryFinest κ₁ d₁ Ep precision loss:ℝ)))
      (6*(((Ep:ℝ)+1)*precision+3)/κ₁)
    unfold nativeRecordAccuracyCoeff at hAccuracy
    linarith only [hh,hh2,hAccuracy]
  have hAuxG := mul_le_mul_of_nonneg_right hAux hgain.le
  have hAuxL := mul_le_mul_of_nonneg_right hAuxG hL.le
  have hGDl := mul_le_mul_of_nonneg_right hGD hL.le
  have hr := (abs_le.mp (hp.2.2.2.2.1 i hi).1).2
  have hhalfL := mul_le_mul_of_nonneg_right hhalf hL.le
  have hdeltaL := mul_le_mul_of_nonneg_right hdelta hL.le
  have hGainL := mul_le_mul_of_nonneg_right hGainSmall hL.le
  change p.r i+(NativeDesign.auxiliaryChiCoeff κ₁ d₁ Ep precision loss*(gain*d.L))*
    (NativeDesign.auxiliaryFinest κ₁ d₁ Ep precision loss:ℝ) ≤ d.L
  nlinarith only [hAuxL,hGDl,hr,hhalfL,hdeltaL,hGainL,hL]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
