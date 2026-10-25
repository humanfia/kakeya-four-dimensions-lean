-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleStateBlock, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeCensusPowerBudgets
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleRecordBudgets
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordWidth
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordPaletteResolution

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData)
open scoped ENNReal

noncomputable section

/-- The original state and native strip widths at every actual child.
The native width is the explicit coefficient power used as input to
the native factory, so its lower width bound is an equality. -/
theorem sample_state_strip_block
    (tune : Tuning) {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    {d₁ precision loss gain : ℝ} {Ep i c : ℕ}
    (hv : NativeDesign.Valid κ₁ d₁ precision loss)
    (hbudget : tune.budget κ₁ d₁ Ep precision loss=NativeDesign.budget κ₁ d₁ Ep precision loss)
    (hgain : 0 < gain) (hL : 0 < d.L) (hδ0 : 0 ≤ δ₀) (hslack : censusSlack ≤ tune.slack)
    (hδtol : δ₀ ≤ tolOf tune κ₁ d₁ Ep precision loss gain)
    (hgrid : 8 ≤ gridFineOf tune κ₁ d₁ Ep precision loss gain*m)
    (hdisplayStrip : (KOf Ep loss gain (d.N k) d.L/4)^(-100:ℝ)*p.κ*d.N k^(2*δ₀*d.L) ≤
      d.N k^(-(ubOf tune κ₁ d₁ Ep precision loss gain*d.L)))
    (hwideStrip : d.N k^(-(2*(ubOf tune κ₁ d₁ Ep precision loss gain*d.L)))*p.κ*d.N k^(2*δ₀*d.L) ≤
      d.N k^(-(ubOf tune κ₁ d₁ Ep precision loss gain*d.L))) :
    let frontRadius := d.N k^(-(ubOf tune κ₁ d₁ Ep precision loss gain*d.L))
    let stripWidth := d.N k^(-(NativeDesign.coefficientCoeff κ₁ d₁ Ep precision loss*(gain*d.L)))
    ∃ radiusP : ℝ, 0 < radiusP ∧ (6*p.κ)*radiusP ≤ frontRadius ∧
      (∀ b : Fin p.C, p.lev b=i+c →
        (KOf Ep loss gain (d.N k) d.L/4)^(-100:ℝ)*
          (∑ j : Fin 2, ∑ l : Fin 2, |p.Q (p.par^[c] b) j l|) ≤
          frontRadius*((2:ℝ)^p.T (p.lev (p.par^[c] b))*|(p.Q (p.par^[c] b)).det|)) ∧
      ∀ b : Fin p.C, p.lev b=i+c →
        stripWidth*(∑ j : Fin 2, ∑ l : Fin 2, |p.Q (p.par^[c] b) j l|) ≤
          frontRadius*((2:ℝ)^p.T (p.lev (p.par^[c] b))*|(p.Q (p.par^[c] b)).det|) := by
  have hN : 1 ≤ d.N k := (by norm_num : (1:ℝ) ≤ 2).trans (hd.1 k)
  have hNp : 0 < d.N k := zero_lt_one.trans_le hN
  have hκp : 0 < p.κ := zero_lt_one.trans_le hp.1
  have hrate := native_sample_census_rate tune hv hbudget hgain hδ0 hslack hδtol hgrid
  have hcoeff := NativeDesign.coefficientCoeff_pos κ₁ d₁ (Ep:=Ep) (precision:=precision) hv.2.2.2.2.2.1
  have hdeltaF : 0 ≤ 3*δ₀*(censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet:ℝ) := by positivity
  have hinvm : 0 ≤ 1/(m:ℝ) := by positivity
  have hub : ubOf tune κ₁ d₁ Ep precision loss gain ≤ NativeDesign.coefficientCoeff κ₁ d₁ Ep precision loss*gain/1000000000 := by
    linarith only [hrate,hdeltaF,hinvm]
  have hroom : 2*(ubOf tune κ₁ d₁ Ep precision loss gain*d.L) ≤
      NativeDesign.coefficientCoeff κ₁ d₁ Ep precision loss*(gain*d.L) := by
    have hh := mul_le_mul_of_nonneg_right hub hL.le
    have hp0 := mul_pos hcoeff (mul_pos hgain hL)
    nlinarith only [hh,hp0]
  have hstripH : d.N k^(-(NativeDesign.coefficientCoeff κ₁ d₁ Ep precision loss*(gain*d.L)))*
      p.κ*d.N k^(2*δ₀*d.L) ≤ d.N k^(-(ubOf tune κ₁ d₁ Ep precision loss gain*d.L)) := by
    calc
      _ ≤ d.N k^(-(2*(ubOf tune κ₁ d₁ Ep precision loss gain*d.L)))*p.κ*d.N k^(2*δ₀*d.L) := by
        gcongr
      _ ≤ _ := hwideStrip
  let frontRadius := d.N k^(-(ubOf tune κ₁ d₁ Ep precision loss gain*d.L))
  refine ⟨frontRadius/(6*p.κ),by dsimp only [frontRadius]; positivity,?_,?_,?_⟩
  · exact le_of_eq (by dsimp only [frontRadius]; field_simp)
  · intro b _hb
    have hK : 0 < KOf Ep loss gain (d.N k) d.L := by unfold KOf; positivity
    exact original_record_strip_width hp hN (p.par^[c] b)
      (Real.rpow_nonneg (div_nonneg hK.le (by norm_num)) _) hdisplayStrip
  · intro b _hb
    exact original_record_strip_width hp hN (p.par^[c] b) (Real.rpow_nonneg hNp.le _) hstripH

/-- The palette mesh, actual child transports and conditional state
coefficients at a sample, using the already fixed original-record cut. -/
theorem sample_state_mesh_block
    (tune : Tuning) {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    {d₁ precision loss gain b front entropy Krecord baseRef hiddenRef : ℝ} {Ep i : ℕ}
    (hv : NativeDesign.Valid κ₁ d₁ precision loss)
    (hgain : 0 < gain) (hL : 0 < d.L) (hδ0 : 0 ≤ δ₀) (hδ : δ₀ ≤ gain/100)
    (hm : 0 < m) (hgm : 8 ≤ gain*(m:ℝ)) (hs : ∀ j, s j=((j:ℝ)+1)/m)
    (hi : i < m) (hib : i+childOffset κ₁ Ep precision gain m < m)
    (hconstant : 2 ≤ d.N k^(gain*d.L))
    (hstates : RecordBudgets.StateBudgetsAt (d.N k) p.κ Krecord b front
      (loss*gain*d.L/((Ep:ℝ)+1)) entropy)
    (hbase : 3*((2:ℝ)^p.T (i+childOffset κ₁ Ep precision gain m)/(2:ℝ)^p.T i)*baseRef ≤
      epsOf Ep precision loss gain (d.N k) d.L (p.r i) (p.r (i+childOffset κ₁ Ep precision gain m))
        (p.T i) (p.T (i+childOffset κ₁ Ep precision gain m)))
    (hhidden : 3*(δ (d.N k) (p.r i)/δ (d.N k) (p.r (i+childOffset κ₁ Ep precision gain m)))*hiddenRef ≤
      epsOf Ep precision loss gain (d.N k) d.L (p.r i) (p.r (i+childOffset κ₁ Ep precision gain m))
        (p.T i) (p.T (i+childOffset κ₁ Ep precision gain m))) :
    let c := childOffset κ₁ Ep precision gain m
    let epsilon := epsOf Ep precision loss gain (d.N k) d.L (p.r i) (p.r (i+c)) (p.T i) (p.T (i+c))
    let pv := d.N k^(-ueOf tune κ₁ d₁ Ep precision loss gain δ₀ d.L)
    let pvP := pvOf Ep precision loss gain (d.N k) d.L (p.r i) (p.r (i+c)) (p.T i) (p.T (i+c))
    let cut := d.N k^(-b)
    let beta := ENNReal.ofReal cut
    let fraction := 2*((d.N k^front)^1)⁻¹
    0 < pv ∧ pv ≤ pvP ∧ beta ≠ 0 ∧ beta ≠ ⊤ ∧
      (∀ packet : Fin p.C, p.lev packet=i+c →
        3*((2:ℝ)^p.T (p.lev packet)/(2:ℝ)^p.T (p.lev (p.par^[c] packet)))*baseRef ≤ epsilon) ∧
      (∀ packet : Fin p.C, p.lev packet=i+c →
        3*(δ (d.N k) (p.r (p.lev (p.par^[c] packet)))/δ (d.N k) (p.r (p.lev packet)))*hiddenRef ≤
          (δ (d.N k) (p.r (p.lev packet))/δ (d.N k) (p.r (p.lev packet)))*epsilon) ∧
      ENNReal.ofReal ((8*fraction)/cut)/beta ≤ (1/2000000000000:ENNReal) ∧
      ENNReal.ofReal ((8*d.N k^entropy)/cut)/beta ≤ ENNReal.ofReal (KOf Ep loss gain (d.N k) d.L/4) := by
  have hv0 := hv
  obtain ⟨_hd0,_hd1,hκ,hκ1,hprecision,hloss,hloss1⟩ := hv0
  have hN : 1 ≤ d.N k := (by norm_num : (1:ℝ) ≤ 2).trans (hd.1 k)
  have hNp : 0 < d.N k := zero_lt_one.trans_le hN
  let c := childOffset κ₁ Ep precision gain m
  have hpv := fine_palette_le_pvOf_at_childOffset (d₁:=d₁) tune (p.T i) (p.T (i+c)) s hN hκ hκ1 hprecision
    hloss hloss1 hgain hL.le hδ0 hδ hm hgm hs (hp.2.2.2.2.1 i hi).1 (hp.2.2.2.2.1 (i+c) hib).1 hconstant
  have hcut : 0 < d.N k^(-b) := hstates.1
  have hfraction : 2*((d.N k^front)^1)⁻¹=2*d.N k^(-front) := by
    rw [pow_one,Real.rpow_neg hNp.le]
  refine ⟨Real.rpow_pos_of_pos hNp _,hpv,ne_of_gt (ENNReal.ofReal_pos.mpr hcut),ENNReal.ofReal_ne_top,?_,?_,?_,?_⟩
  · intro packet hlevel
    have hc : c ≤ p.toOriginal.lev packet := by change c ≤ p.lev packet; omega
    have hpar := (Broad.iterate_par_spec hp.toOriginal c packet hc).1
    have hparent : p.lev (p.par^[c] packet)=i := by
      change p.lev (p.par^[c] packet)=p.lev packet-c at hpar
      omega
    dsimp only [c] at hparent
    simpa only [hlevel,hparent] using hbase
  · intro packet hlevel
    have hc : c ≤ p.toOriginal.lev packet := by change c ≤ p.lev packet; omega
    have hpar := (Broad.iterate_par_spec hp.toOriginal c packet hc).1
    have hparent : p.lev (p.par^[c] packet)=i := by
      change p.lev (p.par^[c] packet)=p.lev packet-c at hpar
      omega
    have hdelta : δ (d.N k) (p.r (i+c)) ≠ 0 := by unfold δ; positivity
    dsimp only [c] at hparent hdelta
    simpa only [hlevel,hparent,div_self hdelta,one_mul] using hhidden
  · simpa only [hfraction] using hstates.2.2.2.1
  · exact hstates.2.2.2.2

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
