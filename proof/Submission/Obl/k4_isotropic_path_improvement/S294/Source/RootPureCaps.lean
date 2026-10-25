-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.RootPureCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeVelocityReference
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalAncestorRecordSource

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData PreparedAngularPath PaletteFamily labelledVelocityPalette)
open Parent.Qualification.Jets2
open Submission.Lib.K4ReferenceMeshPreparation
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
open scoped ENNReal

noncomputable section

/-- The actual power-grid caps cover every real resolved pair of
base and hidden widths in their displayed range. -/
theorem exists_native_power_widths {B finest base hidden : ℝ} (hB : 1 < B)
    (hbaseLo : B^(-finest) ≤ base) (hbaseHi : base ≤ B^(-finest⁻¹))
    (hhidden : base ≤ hidden) (hhidden1 : hidden ≤ 1) :
    ∃ r t : ℝ, finest⁻¹ ≤ r ∧ r ≤ finest ∧ 0 ≤ t ∧ t ≤ finest ∧
      B^(-r)=base ∧ B^(-t)=hidden := by
  have hB0 : 0 < B := zero_lt_one.trans hB
  have hbase : 0 < base := (Real.rpow_pos_of_pos hB0 _).trans_le hbaseLo
  have hh : 0 < hidden := hbase.trans_le hhidden
  let r := -Real.logb B base
  let t := -Real.logb B hidden
  refine ⟨r,t,?_,?_,?_,?_,?_,?_⟩
  · have h := (Real.logb_le_iff_le_rpow hB hbase).mpr hbaseHi
    dsimp only [r]
    linarith
  · have h := (Real.le_logb_iff_rpow_le hB hbase).mpr hbaseLo
    dsimp only [r]
    linarith
  · have h := (Real.logb_le_iff_le_rpow hB hh).mpr (by simpa only [Real.rpow_zero] using hhidden1 : hidden ≤ B^(0:ℝ))
    dsimp only [t]
    linarith
  · have h := (Real.le_logb_iff_rpow_le hB hh).mpr (hbaseLo.trans hhidden)
    dsimp only [t]
    linarith
  · dsimp only [r]
    rw [neg_neg]
    exact Real.rpow_logb hB0 hB.ne' hbase
  · dsimp only [t]
    rw [neg_neg]
    exact Real.rpow_logb hB0 hB.ne' hh

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {meshF envF : ℝ} {θF : ENNReal}
    {F : PaletteFamily Q i stop meshF envF θF}
    {root : Fin p.C} {Edata : Set Ev}
    {Krecord baseRef hiddenRef finePv paletteRatio cut frontRadius fraction χ finest dimension Kcap : ℝ}
    (data : OriginalAncestorRecordSource F root Edata Krecord baseRef hiddenRef finePv paletteRatio cut
      frontRadius fraction χ finest dimension Kcap)

/-- Actual retained ancestor records supply all original pure-cell
numerators needed by coefficient floors, derivative entry and native
qualification, against ONE unchanged original velocity reference. -/
theorem original_root_pure_caps_of_records
    (hB : 1 < d.N k^χ) (hrootStop : p.lev root ≤ stop) (hr : 0 ≤ p.r (p.lev root))
    (hdepth : p.r (p.lev root)+χ*finest ≤ d.L)
    (hbaseRef : 3*baseRef ≤ (d.N k^χ)^(-finest))
    (hhiddenRef : 3*hiddenRef ≤ (d.N k^χ)^(-finest))
    (hRatio : 0 ≤ paletteRatio) (hcut : 0 < cut) (hKcap : 0 ≤ Kcap)
    (hF : MeasurableSet (p.F root))
    (S : Set Ev) (hSkept : S⊆data.kept) (hSF : S⊆p.F root)
    {palette : Measure (Fin 2 → ℝ)} {paletteFinest : ℕ}
    (reference : CommonDyadicVelocityReference finePv paletteFinest
      (fun b => (Parent.OriginalVelocityPalette.originalVectorPalette F root finePv) {b}) palette)
    (hfinePv : 0 < finePv) (hvelocityWidth : finePv ≤ dyadicParameterWidth paletteFinest)
    {base Cpure : ℝ} (hbaseLo : (d.N k^χ)^(-finest) ≤ base)
    (hbaseHi : base ≤ (d.N k^χ)^(-finest⁻¹))
    (hCpure : 4*625*((8*paletteRatio)/cut)*Kcap ≤ Cpure) :
    ∀ query : ℕ, query ≤ paletteFinest → ∀ w : ℝ, base ≤ w → w ≤ 1 →
    ∀ (b : Fin 3 → ℤ) (j : ℤ) (D : Set (Fin 2 → ℤ)), MeasurableSet D →
      (((d.ν k (p.γ root)).prod volume).restrict S) {z |
        (fun l => ⌊unshearedPacketBase p root z l/base⌋)=b ∧
        ⌊physicalParentSignal (d.N k) p root (p.R root) z/w⌋=j ∧
        parameterCode (dyadicParameterWidth query) (fun l => Parent.v z.1 l)∈D} ≤
      (ENNReal.ofReal (Cpure*base^3*w^dimension)*(palette.map (parameterCode (dyadicParameterWidth query))) D)*
        (ENNReal.ofReal (((2:ℝ)^p.T (p.lev root))⁻¹)*d.ν k (p.γ root) (p.A root)) := by
  intro query hquery w hw hw1 b j D hD
  obtain ⟨r,t,hrlo,hrhi,htlo,hthi,hbaseEq,hwEq⟩ :=
    exists_native_power_widths hB hbaseLo hbaseHi hw hw1
  have hNbase : 0 < d.N k^χ := zero_lt_one.trans hB
  have hbase0 : 0 < base := (Real.rpow_pos_of_pos hNbase _).trans_le hbaseLo
  have hw0 : 0 < w := hbase0.trans_le hw
  let raw := (d.ν k (p.γ root)).prod (volume : Measure ℝ)
  let state : Ev → (Fin 3 → ℤ)×ℤ := fun z =>
    ((fun l => ⌊unshearedPacketBase p root z l/base⌋),
      ⌊physicalParentSignal (d.N k) p root (p.R root) z/w⌋)
  have hstate : Measurable state := by
    apply Measurable.prodMk
    · apply measurable_pi_iff.mpr
      intro l
      exact (((PiLp.continuous_apply 2 _ l).measurable.comp (measurable_unshearedPacketBase p root)).div_const base).floor
    · exact ((measurable_physicalParentSignal (d.N k) p root (p.R root)).div_const w).floor
  let pairPalette := (Q.coarseLaw (p.lev root) (F.code root)).map (labelledVelocityPalette finePv)
  let Cbase : ℝ := 625*((8*paletteRatio)/cut)*Kcap
  have hCbase : 0 ≤ Cbase := by dsimp only [Cbase]; positivity
  have hpower : (d.N k^χ)^(-3*r-dimension*t)=base^3*w^dimension := by
    rw [←hbaseEq,←hwEq,←Real.rpow_mul_natCast hNbase.le,←Real.rpow_mul hNbase.le,
      ←Real.rpow_add hNbase]
    congr 1
    ring
  have hrawDom : raw.restrict S ≤ (raw.restrict data.kept).restrict (p.F root) := by
    rw [Measure.restrict_restrict hF]
    exact Measure.restrict_mono (show S⊆p.F root∩data.kept from fun z hz => ⟨hSF hz,hSkept hz⟩) le_rfl
  have hpair (q : (Fin 3 → ℤ)×ℤ) (Dpair : Set (ℤ×ℤ)) (hDpair : MeasurableSet Dpair) :
      (raw.restrict S) {z | state z=q ∧ Native.velocityPalette finePv (Parent.v z.1)∈Dpair} ≤
      ENNReal.ofReal (Cbase*base^3*w^dimension)*
        (ENNReal.ofReal (((2:ℝ)^p.T (p.lev root))⁻¹)*d.ν k (p.γ root) (p.A root))*pairPalette Dpair := by
    have hh := data.native_caps root rfl le_rfl hr hrootStop hdepth
      (by simpa only [div_self (by positivity : (2:ℝ)^p.T (p.lev root)≠0),mul_one] using hbaseRef)
      (by have hδ : δ (d.N k) (p.r (p.lev root))≠0 := by unfold δ; positivity
          simpa only [div_self hδ,mul_one] using hhiddenRef)
      r t hrlo hrhi htlo hthi (Fin.snoc q.1 q.2) Dpair hDpair
    rw [hbaseEq,hwEq,hpower] at hh
    have hsub : {z | state z=q ∧ Native.velocityPalette finePv (Parent.v z.1)∈Dpair}⊆
        {z | jointCode base w (fun l => unshearedPacketBase p root z l)
          (physicalParentSignal (d.N k) p root (p.R root) z)=Fin.snoc q.1 q.2 ∧
          Native.velocityPalette finePv (Parent.v z.1)∈Dpair} := by
      intro z hz
      refine ⟨?_,hz.2⟩
      change (Fin.snoc (state z).1 (state z).2 : Fin 4 → ℤ)=(Fin.snoc q.1 q.2 : Fin 4 → ℤ)
      rw [hz.1]
    apply ((measure_mono hsub).trans (hrawDom _)).trans (hh.trans_eq ?_)
    have hnum : ENNReal.ofReal (Cbase*base^3*w^dimension)=
        ENNReal.ofReal ((8*paletteRatio)/cut)*625*ENNReal.ofReal (Kcap*(base^3*w^dimension)) := by
      rw [show Cbase*base^3*w^dimension=(625*((8*paletteRatio)/cut))*(Kcap*(base^3*w^dimension)) by dsimp only [Cbase]; ring]
      rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤625)]
      norm_num
      ring
    rw [hnum]
    dsimp only [pairPalette]
    ac_rfl
  have hh := current_pair_caps_under_common_reference (raw.restrict S) state hstate
    (fun z l => Parent.v z.1 l) (by unfold Parent.v; fun_prop) pairPalette
    (fun _ => ENNReal.ofReal (((2:ℝ)^p.T (p.lev root))⁻¹)*d.ν k (p.γ root) (p.A root))
    (ENNReal.ofReal (Cbase*base^3*w^dimension)) reference hfinePv hvelocityWidth hpair
    query hquery (b,j) D hD
  have hfactor : (4:ENNReal)*ENNReal.ofReal (Cbase*base^3*w^dimension) ≤
      ENNReal.ofReal (Cpure*base^3*w^dimension) := by
    calc
      _=ENNReal.ofReal (4*(Cbase*base^3*w^dimension)) := by rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4)]; norm_num
      _≤_ := ENNReal.ofReal_le_ofReal (by
        have hb : 4*Cbase ≤ Cpure := by simpa only [Cbase,mul_assoc] using hCpure
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hb (mul_nonneg (pow_nonneg hbase0.le 3) (Real.rpow_nonneg hw0.le _)))
  dsimp only [raw,state] at hh
  simp only [Prod.mk.injEq,and_assoc] at hh
  apply hh.trans
  change _ ≤ _
  calc
    _ ≤ ENNReal.ofReal (Cpure*base^3*w^dimension)*
        (ENNReal.ofReal (((2:ℝ)^p.T (p.lev root))⁻¹)*d.ν k (p.γ root) (p.A root))*
          (palette.map (parameterCode (dyadicParameterWidth query))) D :=
      mul_le_mul' (mul_le_mul' hfactor le_rfl) le_rfl
    _=_ := by ac_rfl

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
