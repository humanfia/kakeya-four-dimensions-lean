-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeSampleScalarBlock, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeScaleData
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Stages

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Scalar inputs of the sample's regularity and qualification stage,
at the actual displayed coefficient scale. -/
structure NativeSampleScalarBlock
    {design : NativeScaleDesign} {N sigma Kcensus stripWidth theta : ℝ} {T fine steps : ℕ}
    (native : NativeScaleData design N sigma T fine steps Kcensus stripWidth theta) (K : ℝ) : Prop where
  Pfac_ne_top : native.scales.regularityFactor ≠ ⊤
  Pfac_ne_zero : native.scales.regularityFactor ≠ 0
  chargeR_ne_top : native.scales.regularityFactor*native.scales.supportLoss ≠ ⊤
  eta_ne_top : native.scales.nativeFailureBound ≠ ⊤
  preCharge_ne_top : native.pre.charge ≠ ⊤
  Lp_nonneg : 0 ≤ native.scales.Lp
  mesh_nonneg : 0 ≤ native.scales.mesh
  bound_nonneg : 0 ≤ native.scales.bound
  coefficient_cost : Parent.QualificationClock.coefficientCost design.degree*
    (native.scales.mesh*(native.scales.bound:ℝ)) ≤ K
  error_le : native.scales.err ≤ theta
  duration_min : 1/K ≤ native.scales.duration/((2:ℝ)^T)⁻¹

/-- The native displayed power is precisely the requested `KOf`. -/
theorem NativeScaleDesign.display_power_eq_KOf (design : NativeScaleDesign)
    {N gain L : ℝ} (hGain : design.gainL=gain*L) :
    N^design.display=KOf design.Ep design.loss gain N L := by
  unfold NativeScaleDesign.display NativeDesign.displayCoeff KOf
  rw [hGain]
  congr 1
  ring

/-- Every finite-cost, coefficient and duration input follows from
native scale data, without an incidence or source premise. -/
theorem native_sample_scalar_block
    {design : NativeScaleDesign} {N sigma Kcensus stripWidth theta : ℝ} {T fine steps : ℕ}
    (native : NativeScaleData design N sigma T fine steps Kcensus stripWidth theta)
    {gain L kappa : ℝ} (hGain : design.gainL=gain*L)
    (hKappa : 1 ≤ kappa) (hKappaPower : kappa ≤ N^sigma) :
    NativeSampleScalarBlock native (KOf design.Ep design.loss gain N L) := by
  have hSupport : native.scales.supportLoss ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top native.support_power
  have hNative : native.scales.nativeFailureBound ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top native.native_power
  have hPre : native.pre.charge ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (native.pre_charge kappa hKappa hKappaPower)
  have hK := design.display_power_eq_KOf (N:=N) hGain
  refine {
    Pfac_ne_top := native.regularity_ne_top
    Pfac_ne_zero := ne_of_gt native.regularity_pos
    chargeR_ne_top := ENNReal.mul_ne_top native.regularity_ne_top hSupport
    eta_ne_top := hNative
    preCharge_ne_top := hPre
    Lp_nonneg := native.scales.hLp
    mesh_nonneg := native.scales.hmesh.le
    bound_nonneg := native.qbound_nonneg
    coefficient_cost := ?_
    error_le := native.qerror_eq.le
    duration_min := ?_
  }
  · simpa only [hK] using native.qcoefficient_cost
  · simpa only [hK] using native.qduration_min

/-- The native relative duration is the duration required at every
actual child with its actual ancestor clock. -/
theorem native_sample_duration_at_child
    {d : Parent.ParentSource.Native.ProblemData} {k m : ℕ}
    {p : Parent.ParentSource.Native.PathData (d.W k)}
    {kappa1 delta sigmaPath : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      kappa1 m s delta Mp Dp sigmaPath)
    {design : NativeScaleDesign} {sigmaNative Kcensus stripWidth theta : ℝ}
    {T fine steps i c : ℕ}
    (native : NativeScaleData design (d.N k) sigmaNative T fine steps Kcensus stripWidth theta)
    {gain : ℝ} (hGain : design.gainL=gain*d.L)
    (hT : T=p.T (i+c)-p.T i) (hTlb : p.T i ≤ p.T (i+c))
    (b : Fin p.C) (hb : p.lev b=i+c) :
    1/KOf design.Ep design.loss gain (d.N k) d.L ≤ native.scales.duration/
      ((((2:ℝ)^p.T (p.lev b))⁻¹)/(((2:ℝ)^p.T (p.lev (p.par^[c] b)))⁻¹)) := by
  have hLevel : p.lev (p.par^[c] b)=i := by
    have hh := (Parent.ParentSource.Broad.iterate_par_spec hp.toOriginal c b (by change c ≤ p.lev b; omega)).1
    change p.lev (p.par^[c] b)=p.lev b-c at hh
    rw [hh,hb]
    omega
  have hClock : ((2:ℝ)^p.T (i+c))⁻¹/((2:ℝ)^p.T i)⁻¹=((2:ℝ)^T)⁻¹ := by
    rw [hT,pow_sub₀ _ (by norm_num : (2:ℝ) ≠ 0) hTlb]
    field_simp
  rw [hLevel,hb,hClock]
  simpa only [design.display_power_eq_KOf hGain] using native.qduration_min

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
