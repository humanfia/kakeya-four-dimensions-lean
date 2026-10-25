-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalIncidenceFromPureCells, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalIncidenceData
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalDyadicFloorData
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PureCellCanonicalCaps

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- Scalar conditions for the original incidence construction. These
contain no incidence set, coefficient table, prior, row or certificate. -/
structure OriginalIncidenceScales
    (b ρ H Krow η error ζ dimension Kss Htarget Kcap Cpure : ℝ)
    (floorStart floorCount : ℕ) (floorExponent : ℝ) where
  L : ℕ
  hL : 1 ≤ L
  level : ℕ → ℕ
  hlevel0 : level 0=0
  A : ℝ
  hA : 1 ≤ A
  hratio : ∀ i, i+1 < L → dyadicParameterWidth (level i) ≤ A*dyadicParameterWidth (level (i+1))
  hfloorScale : dyadicParameterWidth (level (L-1)) ≤ ζ
  hsmall : ∀ i < L, (2+3*(H+1))*b ≤ ρ*dyadicParameterWidth (level i)
  hρs : ∀ i < L, ρ ≤ dyadicParameterWidth (level i)
  hosc : ∀ i < L, (2*(error+2*η*ρ)+2*(H+1)*b)/ρ ≤ dyadicParameterWidth (level i)
  n0 : ℕ
  hρdyadic : ρ=dyadicParameterWidth n0
  lastLevel : ℕ
  hlevelMax : ∀ i < L, level i ≤ lastLevel
  hqueryMax : parameterLevel ζ ≤ lastLevel
  hfloorStart : floorStart ≤ n0
  hfloorEnd : n0+lastLevel < floorStart+floorCount
  hexponent : 0 ≤ floorExponent
  hreserve : 1/Kcap ≤ (dyadicParameterWidth (floorStart+floorCount-1))^floorExponent
  resolution : ℝ
  hresolution : 0 < resolution
  hcanonical : 3*(H+1)*resolution ≤ ρ*dyadicParameterWidth lastLevel
  entryCut0 : ℝ
  hentryCut0 : 0 < entryCut0
  entryCut : ℕ → ℝ
  hentryCut : ∀ i < L, 0 < entryCut i
  Cstate : ℝ
  hCstate : 0 ≤ Cstate
  cut : ℕ → ℝ
  hcut : ∀ i < L, 0 < cut i
  analyticEpsilon : ℝ
  cZeta : ℝ
  alpha : ℝ
  Q0 : ℝ
  N : ℝ
  ch : ℝ
  nativeCut : ℝ
  M : ℕ
  hqualification : NativeQualificationAt dimension M analyticEpsilon cZeta alpha Q0
  hN : 0 < N
  hch : 0 < ch
  hQ : Q0 ≤ N^ch
  hHtarget : Htarget=N^(ch*alpha)
  hζ : 0 < ζ
  hζ1 : ζ ≤ 1
  hρζ : ρ ≤ ζ
  hnativeCut : 0 < nativeCut
  hnativeNum : 625*(151200*(12*H+3)*Cpure*(3:ℝ)^dimension)/nativeCut ≤ Kcap
  hcapH : 8*Kcap^2 ≤ N^(ch*alpha)
  hssH : Kss ≤ N^(ch*alpha)
  hresH : 2*(A+5*Krow^2) ≤ N^(ch*alpha)

/-- Build every original incidence floor, canonical numerator and
state palette used by native qualification from actual pure-cell data. -/
def originalIncidenceData_of_pure_cells {Λ : Type} [MeasurableSpace Λ]
    (ν : Measure Λ) (μ : Measure (Λ × ℝ))
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (E : Set (Λ × ℝ)) (hE : MeasurableSet E)
    {b ρ H Krow η error ζ dimension Kss Htarget Kcap Cpure : ℝ}
    {floorStart floorCount : ℕ} {floorExponent : ℝ}
    (scales : OriginalIncidenceScales b ρ H Krow η error ζ dimension Kss Htarget Kcap Cpure
      floorStart floorCount floorExponent)
    (palette : Measure (Fin 2 → ℝ))
    (floors : OriginalDyadicFloorData ν c E palette dimension floorExponent floorStart floorCount)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hH : 1 ≤ H) (hKcap : 0 < Kcap)
    (hCpure : 0 ≤ Cpure) (hdim : 0 ≤ dimension)
    (ht : ∀ z∈E, z.2∈Icc (0:ℝ) 1)
    (hcoeff : ∀ z∈E, ∀ j, |c z.1 j| ≤ H)
    (hμ : μ=((ν.prod volume).restrict E))
    (hpure : ∀ query : ℕ, query ≤ scales.n0+scales.lastLevel →
      ∀ w : ℝ, scales.resolution ≤ w → w ≤ 1 →
      ∀ (base : Fin 3 → ℤ) (hidden : ℤ) (vcode : Fin 2 → ℤ),
      (μ.restrict E) {z | originalBaseCode c scales.resolution z=base ∧
        ⌊zx (c z.1) z.2/w⌋=hidden ∧
        parameterCode (dyadicParameterWidth query) (zv (c z.1))=vcode} ≤
      ENNReal.ofReal (Cpure*scales.resolution^3*w^dimension)*
        (palette.map (parameterCode (dyadicParameterWidth query))) {vcode})
    (hstate : ∀ query : ℕ, query ≤ scales.n0+scales.lastLevel →
      ∀ q (D : Set (Fin 2 → ℤ)), MeasurableSet D →
      μ {z | originalFineState c b z=q ∧
        parameterCode (dyadicParameterWidth query) (zv (c z.1))∈D} ≤
      ENNReal.ofReal scales.Cstate*μ ((originalFineState c b) ⁻¹' {q})*
        (palette.map (parameterCode (dyadicParameterWidth query))) D) :
    OriginalIncidenceData ν μ c E b ρ H Krow η error ζ dimension Kss Htarget Kcap 1 palette := by
  let Ccanon := 151200*(12*H+3)*Cpure*(3:ℝ)^dimension
  have hCcanon : 0 ≤ Ccanon := by dsimp only [Ccanon]; positivity
  letI : IsProbabilityMeasure palette := floors.probability
  have hmapProb (query : ℕ) : IsProbabilityMeasure (palette.map (parameterCode (dyadicParameterWidth query))) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_parameterCode _).aemeasurable).mpr inferInstance
  have hscale (level : ℕ) : ρ*dyadicParameterWidth level=dyadicParameterWidth (scales.n0+level) := by
    calc
      ρ*dyadicParameterWidth level=dyadicParameterWidth scales.n0*dyadicParameterWidth level :=
        congrArg (·*dyadicParameterWidth level) scales.hρdyadic
      _=dyadicParameterWidth (scales.n0+level) := by
        simp only [dyadicParameterWidth,pow_add,mul_inv_rev]
        ring
  have hvelocity (w : ℝ) (cf : Fin 7 → ℝ) : vbin w cf=parameterCode w (zv cf) := rfl
  have hμE : μ.restrict E=μ := by
    rw [hμ,Measure.restrict_restrict hE,inter_self]
  have hwidth1 (n : ℕ) : dyadicParameterWidth n ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hcanon (level : ℕ) (hlevel : level ≤ scales.lastLevel) :
      ∀ world cell v,
      (μ.restrict E) {z | parameterCode ρ (c z.1)=world ∧
        canonicalZoomCell c ρ (dyadicParameterWidth level) z=cell ∧
        parameterCode (ρ*dyadicParameterWidth level) (zv (c z.1))=v} ≤
      ENNReal.ofReal (Ccanon*dyadicParameterWidth level*
        (ρ*dyadicParameterWidth level)^((2:ℝ)+dimension))*
          (palette.map (parameterCode (ρ*dyadicParameterWidth level))) {v} := by
    have hsmall : 3*(H+ρ)*scales.resolution ≤ ρ*dyadicParameterWidth level := by
      have h := scales.hcanonical.trans (mul_le_mul_of_nonneg_left
        (dyadicParameterWidth_antitone hlevel) hρ.le)
      nlinarith [scales.hresolution]
    have hδp : scales.resolution ≤ ρ*dyadicParameterWidth level := by
      have h := scales.hcanonical.trans (mul_le_mul_of_nonneg_left
        (dyadicParameterWidth_antitone hlevel) hρ.le)
      nlinarith [scales.hresolution]
    have hδs : scales.resolution ≤ dyadicParameterWidth level := by
      exact hδp.trans (by nlinarith [dyadicParameterWidth_pos level])
    have hweight (v : Fin 2 → ℤ) :
        (palette.map (parameterCode (ρ*dyadicParameterWidth level))) {v}≠∞ := by
      rw [hscale]
      letI := hmapProb (scales.n0+level)
      exact measure_ne_top _ _
    exact canonical_cell_cap_of_current_pure_cells μ c hc E hE scales.hresolution hρ hρ1
      (dyadicParameterWidth_pos _) (hwidth1 _) hδs hδp hH hCpure hdim hsmall ht hcoeff _ hweight
      (by simpa only [hscale] using hpure (scales.n0+level) (Nat.add_le_add_left hlevel _))
  have hcanon0 : ∀ world cell v,
      (μ.restrict E) {z | parameterCode 1 (c z.1)=world ∧
        canonicalZoomCell c 1 ρ z=cell ∧ parameterCode ρ (zv (c z.1))=v} ≤
      ENNReal.ofReal (Ccanon*ρ*ρ^((2:ℝ)+dimension))*
        (palette.map (parameterCode ρ)) {v} := by
    have hsmall : 3*(H+1)*scales.resolution ≤ ρ :=
      scales.hcanonical.trans (by nlinarith [hwidth1 scales.lastLevel])
    have hδρ : scales.resolution ≤ ρ := by nlinarith [scales.hresolution]
    have hweight (v : Fin 2 → ℤ) : (palette.map (parameterCode ρ)) {v}≠∞ := by
      rw [scales.hρdyadic]
      letI := hmapProb scales.n0
      exact measure_ne_top _ _
    have hh := canonical_cell_cap_of_current_pure_cells μ c hc E hE scales.hresolution (by norm_num) le_rfl
      hρ hρ1 hδρ (by simpa only [one_mul] using hδρ) hH hCpure hdim
      (by simpa only [one_mul] using hsmall) ht hcoeff _ (by simpa only [one_mul] using hweight)
      (by simpa only [one_mul,scales.hρdyadic] using hpure scales.n0 (by omega))
    simpa only [one_mul] using hh
  have hfloorAt (n : ℕ) (hn : n ≤ scales.lastLevel) (z : Λ × ℝ) (hz : z∈E) :=
    floors.at_level_bin scales.hexponent scales.hreserve (scales.n0+n)
      (by have := scales.hfloorStart; omega) (by have := scales.hfloorEnd; omega) z hz
  have hcoarseAt (z : Λ × ℝ) (hz : z∈E) :=
    floors.at_level scales.hexponent scales.hreserve scales.n0 scales.hfloorStart
      (by have := scales.hfloorEnd; omega) z hz
  have hfineAt (r : ℝ) (hr : ζ ≤ r) (hr1 : r ≤ 1) (z : Λ × ℝ) (hz : z∈E) :=
    floors.at_level scales.hexponent scales.hreserve (scales.n0+parameterLevel r)
      (by have := scales.hfloorStart; omega)
      (by have h := (parameterLevel_below_floor scales.hζ hr hr1); have := scales.hqueryMax; have := scales.hfloorEnd; omega) z hz
  refine {
    L := scales.L, hL := scales.hL, level := scales.level, hlevel0 := scales.hlevel0,
    A := scales.A, hA := scales.hA, hratio := scales.hratio, hfloorScale := scales.hfloorScale,
    hsmall := scales.hsmall, hρs := scales.hρs, hosc := scales.hosc,
    amplitude0 := ρ^dimension, K0 := Kcap, C0 := Ccanon,
    entryCut0 := scales.entryCut0, hamp0 := Real.rpow_pos_of_pos hρ _, hK0 := hKcap,
    hC0 := hCcanon, hentryCut0 := scales.hentryCut0, n0 := scales.n0, hρdyadic := scales.hρdyadic,
    amplitude := fun i => (ρ*dyadicParameterWidth (scales.level i))^dimension,
    K := fun _ => Kcap, C := fun _ => Ccanon, entryCut := scales.entryCut,
    hamp := fun i _ => Real.rpow_pos_of_pos (mul_pos hρ (dyadicParameterWidth_pos _)) _,
    hK := fun _ _ => hKcap, hC := fun _ _ => hCcanon, hentryCut := scales.hentryCut,
    weight0 := fun v => (palette.map (parameterCode ρ)) {v},
    hweight0 := ?_, weight := fun i v =>
      (palette.map (parameterCode (ρ*dyadicParameterWidth (scales.level i)))) {v}, hweight := ?_,
    hfloor0 := ?_, hfloor := ?_, hcap0 := ?_, hcap := ?_,
    π := fun i => palette.map (parameterCode (ρ*dyadicParameterWidth (scales.level i))),
    π_probability := ?_, Cstate := scales.Cstate, hCstate := scales.hCstate,
    cut := scales.cut, hcut := scales.hcut, hstateCap := ?_,
    hcoarseFloor := ?_, hfineFloor := ?_, analyticEpsilon := scales.analyticEpsilon,
    cZeta := scales.cZeta, alpha := scales.alpha, Q0 := scales.Q0, N := scales.N,
    ch := scales.ch, nativeCut := scales.nativeCut, nativeC := Ccanon, M := scales.M,
    hqualification := scales.hqualification, hN := scales.hN, hch := scales.hch, hQ := scales.hQ,
    hHtarget := scales.hHtarget, hζ := scales.hζ, hζ1 := scales.hζ1, hρζ := scales.hρζ,
    hnativeCut := scales.hnativeCut, hnativeC := hCcanon, hprofile := by norm_num,
    hKcap := hKcap, hnativeNum := scales.hnativeNum, hcapH := scales.hcapH,
    hssH := scales.hssH, hresH := scales.hresH, hNativeCap := ?_ }
  · intro v
    rw [scales.hρdyadic]
    letI := hmapProb scales.n0
    exact measure_ne_top _ _
  · intro i hi v
    rw [hscale]
    letI := hmapProb (scales.n0+scales.level i)
    exact measure_ne_top _ _
  · intro z hz
    have hh := hfloorAt 0 (Nat.zero_le _) z hz
    simpa only [Nat.add_zero,←scales.hρdyadic,mul_one,one_mul,hvelocity,
      Real.rpow_add hρ,Real.rpow_two,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  · intro i hi z hz
    have hh := hfloorAt (scales.level i) (scales.hlevelMax i hi) z hz
    simpa only [←hscale,mul_one,one_mul,hvelocity,Real.rpow_add (mul_pos hρ (dyadicParameterWidth_pos _)),
      Real.rpow_two,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  · intro world cell v
    simpa only [Real.rpow_add hρ,Real.rpow_two,mul_assoc] using hcanon0 world cell v
  · intro i hi world cell v
    simpa only [Real.rpow_add (mul_pos hρ (dyadicParameterWidth_pos _)),Real.rpow_two,mul_assoc] using
      hcanon (scales.level i) (scales.hlevelMax i hi) world cell v
  · intro i
    rw [hscale]
    exact hmapProb _
  · intro i hi q D hD
    simpa only [hscale] using hstate (scales.n0+scales.level i)
      (Nat.add_le_add_left (scales.hlevelMax i hi) _) q D hD
  · intro z hz
    simpa only [←scales.hρdyadic,mul_one] using hcoarseAt z hz
  · intro r hr hr1 z hz
    simpa only [←hscale,zoomParameterPiece,mul_one] using hfineAt r hr hr1 z hz
  · intro q hq hq1 world cell v
    rw [←hμ]
    have hh := hcanon (parameterLevel q)
      ((Nat.lt_succ_iff.mp (parameterLevel_below_floor scales.hζ hq hq1)).trans scales.hqueryMax) world cell v
    rw [hμE] at hh
    rw [Measure.map_apply (measurable_parameterCode _) (measurableSet_singleton _)] at hh
    simpa only [Set.preimage,mem_singleton_iff,mul_one] using hh

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
