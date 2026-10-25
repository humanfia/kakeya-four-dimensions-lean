-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ParentSignalCellCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ParentSignalCellCaps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1046 (branch x0943), commit 1fcc75a78b90aa1b479052c83612b68563af73b6,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ParentSignalCellCaps.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentUnshearedBandWidths
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalSignalCellCaps

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Native
open Submission.Lib.K4ReferenceMeshPreparation
open scoped ENNReal

noncomputable section

/-- The literal unsheared old base together with the original parent P/a. -/
def parentUnshearedCoordinates {W : ℕ} (N : ℝ) (p : PathData W) (old : Fin p.C)
    (P : MvPolynomial (Fin 4) ℝ) (z : Ev) : Fin 4 → ℝ :=
  Fin.snoc (fun j => unshearedPacketBase p old z j) (physicalParentSignal N p old P z)

theorem measurable_parentUnshearedCoordinates {W : ℕ} (N : ℝ) (p : PathData W)
    (old : Fin p.C) (P : MvPolynomial (Fin 4) ℝ) :
    Measurable (parentUnshearedCoordinates N p old P) := by
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.lastCases ?_ ?_ i
  · simpa only [parentUnshearedCoordinates,Fin.snoc_last] using
      measurable_physicalParentSignal N p old P
  · intro j
    simpa only [parentUnshearedCoordinates,Fin.snoc_castSucc,Function.comp_def] using
      (PiLp.continuous_apply 2 _ j).measurable.comp (measurable_unshearedPacketBase p old)

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ ε : ℝ}
    (Q : PreparedAngularPath d k p m H u τ) (hpure : Q.uniformPureCeiling ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hpure hd hp

/-- The genuine parent-P pure cap supplies all cells required by joint
record/palette pruning, in unsheared old units and with the unchanged
full original assignment and clock denominator. -/
theorem Native.PreparedAngularPath.parent_unsheared_signal_power_caps
    (old : Fin p.C) (hr : 0 ≤ p.r (p.lev old))
    (χ finest : ℝ) (hχ : 0 ≤ χ) (hdepth : p.r (p.lev old)+χ*finest ≤ d.L)
    (μ : Measure Ev) (hμ : μ ≤ d.μ k (p.γ old))
    (hbase : ∀ᵐ z ∂μ, z∈Q.base (p.γ old)) (hF : ∀ᵐ z ∂μ, z∈p.F old)
    {dimension f₀ error Kcap : ℝ} (hdim : 0 ≤ dimension)
    (hprofile : ∀ a, 0 ≤ a → a ≤ d.L → |d.f a-f₀-dimension*a| ≤ error)
    (hbudget : 512*(max p.κ (d.K k))^2*p.κ*4^dimension*
      d.N k^(2*error+(τ+2*δ₀*d.L)+ε) ≤ Kcap) :
    let α := (d.ν k (p.γ old) (p.A old)*
      ENNReal.ofReal (((2:ℝ)^p.T (p.lev old))⁻¹))⁻¹
    ∀ r t, finest⁻¹ ≤ r → r ≤ finest → 0 ≤ t → t ≤ finest → ∀ q,
      (α • μ) {z | nativeSignalCell (d.N k^χ) r t
        (parentUnshearedCoordinates (d.N k) p old (d.P k (p.γ old))) (MvPolynomial.X 3) z=q} ≤
          ENNReal.ofReal (Kcap*(d.N k^χ)^(-3*r-dimension*t)) := by
  intro α r t _hrl _hrh ht htf q
  have hN : 1 ≤ d.N k := by linarith [hd.1 k]
  have hNp : 0 < d.N k := zero_lt_one.trans_le hN
  have hκ : 0 < p.κ := zero_lt_one.trans_le hp.1
  let base := (d.N k^χ)^(-r)
  let hidden := (d.N k^χ)^(-t)
  let C := 64*(max p.κ (d.K k))^2*p.κ*4^dimension*
    d.N k^(2*error+(τ+2*δ₀*d.L)+ε)
  have hb : 0 < base := by dsimp [base]; positivity
  have hw : 0 < hidden := by dsimp [hidden]; positivity
  have htarget : p.r (p.lev old)+χ*t ≤ d.L := by
    nlinarith [mul_le_mul_of_nonneg_left htf hχ]
  have holdL : p.r (p.lev old) ≤ d.L :=
    (le_add_of_nonneg_right (mul_nonneg hχ ht)).trans htarget
  have hhiddenEq : hidden=d.N k^(-(χ*t)) := by
    dsimp only [hidden]
    rw [←Real.rpow_mul hNp.le]
    congr 1
    ring
  have hresolved : d.N k^(-(d.L-p.r (p.lev old))) ≤ 4*hidden := by
    have hh : d.N k^(-(d.L-p.r (p.lev old))) ≤ hidden := by
      rw [hhiddenEq]
      exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    linarith
  let center : EuclideanSpace ℝ (Fin 4) := WithLp.toLp 2
    (Fin.snoc (fun j => base*(q.1 j:ℝ)) 0)
  let U := k4_profile_density_bounds.baseBox center base
  have hUm : MeasurableSet U := k4_profile_density_bounds.measurableSet_baseBox center base
  have hvol : volume U=ENNReal.ofReal ((2*base)^3) :=
    k4_profile_density_bounds.volume_baseBox center base hb.le
  let band := {z | |physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z-hidden*(q.2:ℝ)| ≤ hidden}
  have hsub : {z | nativeSignalCell (d.N k^χ) r t
      (parentUnshearedCoordinates (d.N k) p old (d.P k (p.γ old))) (MvPolynomial.X 3) z=q} ⊆
      (unshearedPacketBase p old) ⁻¹' U∩band := by
    intro z hz
    have hparts : nativeSignalCell (d.N k^χ) r t
        (parentUnshearedCoordinates (d.N k) p old (d.P k (p.γ old))) (MvPolynomial.X 3) z=
        ((fun j => ⌊unshearedPacketBase p old z j/base⌋),
          ⌊physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z/hidden⌋) := by
      apply Prod.ext
      · ext j
        change ⌊(Fin.snoc (fun j => unshearedPacketBase p old z j)
          (physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z) : Fin 4 → ℝ) j.castSucc/base⌋=_
        rw [Fin.snoc_castSucc]
      · simp [nativeSignalCell,parentUnshearedCoordinates,Fin.snoc,hidden]
    have hz' : ((fun j => ⌊unshearedPacketBase p old z j/base⌋),
        ⌊physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z/hidden⌋)=q := by
      exact hparts.symm.trans hz
    refine ⟨?_,physical_grid_corner_error hw (congrArg Prod.snd hz')⟩
    apply (k4_profile_density_bounds.mem_baseBox_iff center base _).mpr
    intro j
    have hh := physical_grid_corner_error hb (congrFun (congrArg Prod.fst hz') j)
    simpa only [center,PiLp.toLp_apply,Fin.snoc_castSucc] using hh
  have hcap := Q.parent_unsheared_moving_band_all_widths hpure hd hp old hr holdL
    μ hμ hbase hF hdim hprofile (fun _ => hidden*(q.2:ℝ)) measurable_const hw hresolved
  have hcapU := hcap U
  simp only [Measure.smul_apply,smul_eq_mul] at hcapU
  rw [Measure.map_apply (measurable_unshearedPacketBase p old) hUm,
    Measure.restrict_apply ((measurable_unshearedPacketBase p old) hUm),hvol,
    ←ENNReal.ofReal_mul (by positivity)] at hcapU
  have hCbudget : 8*C ≤ Kcap := by
    convert hbudget using 1 <;> dsimp only [C] <;> ring
  have hmeshPower : base^3*hidden^dimension=(d.N k^χ)^(-3*r-dimension*t) := by
    dsimp only [base,hidden]
    rw [←Real.rpow_mul_natCast (Real.rpow_nonneg hNp.le _),
      ←Real.rpow_mul (Real.rpow_nonneg hNp.le _),
      ←Real.rpow_add (Real.rpow_pos_of_pos hNp _)]
    congr 1
    ring
  calc
    _ ≤ α*μ ((unshearedPacketBase p old) ⁻¹' U∩band) := by
      simpa only [Measure.smul_apply,smul_eq_mul] using
        mul_le_mul' (le_refl α) (measure_mono hsub)
    _ ≤ ENNReal.ofReal ((C*hidden^dimension)*(2*base)^3) := hcapU
    _ = ENNReal.ofReal ((8*C)*(base^3*hidden^dimension)) := by congr 1; ring
    _ ≤ ENNReal.ofReal (Kcap*(base^3*hidden^dimension)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCbudget (by positivity))
    _ = _ := by rw [hmeshPower]

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
