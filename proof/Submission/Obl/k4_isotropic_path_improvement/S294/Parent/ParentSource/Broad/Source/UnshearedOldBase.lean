-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.UnshearedOldBase, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/UnshearedOldBase.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/UnshearedOldBase.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.BaseCapChange
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Frames
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Interface

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Native
open scoped ENNReal

noncomputable section

/-- The original physical time and planar position. -/
def originalPhysicalBase (z : Ev) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![z.2, (xp z.1 z.2) 1, (xp z.1 z.2) 2]

/-- Isotropic old units, translated to the left endpoint without velocity shear. -/
def unshearedPacketBase {W : ℕ} (p : PathData W) (old : Fin p.C) (z : Ev) :
    EuclideanSpace ℝ (Fin 3) :=
  let h := ((2 : ℝ)^p.T (p.lev old))⁻¹
  let t0 := (p.j old : ℝ)*h
  WithLp.toLp 2 ![(z.2-t0)/h,
    ((xp z.1 z.2) 1-(p.c old 0+t0*p.u old 0))/h,
    ((xp z.1 z.2) 2-(p.c old 1+t0*p.u old 1))/h]

def unshearedOldBaseFrame {W : ℕ} (p : PathData W) (old : Fin p.C) :
    Submission.Lib.K4ChartLifting.Frame where
  t₀ := (p.j old : ℝ)*((2 : ℝ)^p.T (p.lev old))⁻¹
  q := ((2 : ℝ)^p.T (p.lev old))⁻¹
  c := p.c old+((p.j old : ℝ)*((2 : ℝ)^p.T (p.lev old))⁻¹) • p.u old
  u := 0
  D := Matrix.diagonal (fun _ : Fin 2 => ((2 : ℝ)^p.T (p.lev old))⁻¹)

theorem unshearedOldBaseFrame_det {W : ℕ} (p : PathData W) (old : Fin p.C) :
    (unshearedOldBaseFrame p old).D.det = (((2 : ℝ)^p.T (p.lev old))⁻¹)^2 := by
  simp [unshearedOldBaseFrame, Matrix.det_diagonal, pow_two]

theorem unshearedOldBaseFrame_obsBase {W : ℕ} (p : PathData W) (old : Fin p.C) :
    (unshearedOldBaseFrame p old).obsBase ∘ originalPhysicalBase = unshearedPacketBase p old := by
  have hinv : (Matrix.diagonal (fun _ : Fin 2 => ((2 : ℝ)^p.T (p.lev old))⁻¹))⁻¹ =
      Matrix.diagonal (fun _ : Fin 2 => (2 : ℝ)^p.T (p.lev old)) := by
    apply Matrix.inv_eq_left_inv
    ext i j
    by_cases hij : i=j
    · simp [Matrix.one_apply, hij]
    · simp [hij]
  funext z
  ext i
  fin_cases i <;>
    simp [Submission.Lib.K4ChartLifting.Frame.obsBase, unshearedOldBaseFrame,
      originalPhysicalBase, unshearedPacketBase, hinv,
      PiLp.add_apply, PiLp.smul_apply, div_eq_mul_inv, mul_comm]

theorem measurable_unshearedPacketBase {W : ℕ} (p : PathData W) (old : Fin p.C) :
    Measurable (unshearedPacketBase p old) := by
  rw [← unshearedOldBaseFrame_obsBase]
  exact (unshearedOldBaseFrame p old).measurable_obsBase.comp (by
    unfold originalPhysicalBase xp
    fun_prop)

/-- Saturation bounds the isotropic old spatial Jacobian in original units. -/
theorem Native.PathData.Valid.unsheared_determinant_floor
    {W : ℕ} {p : PathData W} {N L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hN : 1 ≤ N) (old : Fin p.C) :
    N^(-(2*δ₀*L))*(((2 : ℝ)^p.T (p.lev old))⁻¹)^2 ≤ |(p.Q old).det| := by
  rcases hp.2.2.2.2.2.2.2 old with
    ⟨hlev, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdetlow, _⟩
  obtain ⟨_, _, _, _, hnw, _⟩ := hp.2.2.2.2.1 (p.lev old) hlev
  simp only [zero_mul, sub_zero] at hnw
  have hnwle : p.nw (p.lev old) ≤ δ₀*L := (le_abs_self _).trans hnw
  have hraw : N^(-(2*δ₀*L)) ≤ |(p.Q old).det| *(4 : ℝ)^p.T (p.lev old) :=
    (Real.rpow_le_rpow_of_exponent_le hN (by linarith)).trans hdetlow
  have hpow : (4 : ℝ)^p.T (p.lev old) = ((2 : ℝ)^p.T (p.lev old))^2 := by
    rw [show (4 : ℝ)=(2 : ℝ)^2 by norm_num, ←pow_mul, ←pow_mul, Nat.mul_comm]
  rw [hpow] at hraw
  have hr := (div_le_iff₀ (show 0 < ((2 : ℝ)^p.T (p.lev old))^2 by positivity)).mpr hraw
  simpa only [div_eq_mul_inv, inv_pow] using hr

/-- An original continuous base cap in isotropic old units. The full original
assignment and clock stay fixed, and the only extra loss is the existing
path profile tolerance, independent of the input format. -/
theorem unsheared_base_cap_in_old_packet_units
    {W : ℕ} {p : PathData W} {N L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hN : 1 ≤ N)
    (old : Fin p.C) (μ : Measure Ev) (C : ENNReal)
    (hcap : μ.map originalPhysicalBase ≤ C • volume) :
    (ν (p.γ old) (p.A old)*ENNReal.ofReal (((2 : ℝ)^p.T (p.lev old))⁻¹))⁻¹ •
      μ.map (unshearedPacketBase p old) ≤
      (C*ENNReal.ofReal ((p.κ*N^(2*δ₀*L))*N^f (p.r (p.lev old)))) • volume := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hκ : 0 < p.κ := zero_lt_one.trans_le hp.1
  have hf := hp.unsheared_determinant_floor hN old
  have hdet : (unshearedOldBaseFrame p old).D.det ≠ 0 := by
    rw [unshearedOldBaseFrame_det]
    positivity
  have hfloor : ENNReal.ofReal (N^(-f (p.r (p.lev old)))*
      |(unshearedOldBaseFrame p old).D.det|/(p.κ*N^(2*δ₀*L))) ≤
      ν (p.γ old) (p.A old) := by
    apply (ENNReal.ofReal_le_ofReal ?_).trans (hp.assignment_mass_bounds hNp old).1
    rw [unshearedOldBaseFrame_det, abs_of_nonneg (sq_nonneg _)]
    calc
      _ = N^(-f (p.r (p.lev old)))*(N^(-(2*δ₀*L))*
          (((2 : ℝ)^p.T (p.lev old))⁻¹)^2)/p.κ := by
        simp only [Real.rpow_neg hNp.le, div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ _ := by gcongr
  change (ν (p.γ old) (p.A old)*ENNReal.ofReal (unshearedOldBaseFrame p old).q)⁻¹ •
    μ.map (unshearedPacketBase p old) ≤ _
  have hh := base_cap_in_old_packet_units μ originalPhysicalBase
    (by unfold originalPhysicalBase xp; fun_prop) (unshearedOldBaseFrame p old)
    (by change 0 < ((2 : ℝ)^p.T (p.lev old))⁻¹; positivity) hdet
    hNp (by positivity : 0 < p.κ*N^(2*δ₀*L)) (f (p.r (p.lev old)))
    (ν (p.γ old) (p.A old)) C hfloor hcap
  simpa only [unshearedOldBaseFrame_obsBase] using hh

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
