-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.AncestorSignalJointCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/AncestorSignalJointCaps.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AncestorSignalCellCaps
import Submission.Lib.K4OriginalGeometricReference.JointSupport

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native
open Submission.Lib.K4ReferenceMeshPreparation
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
open scoped ENNReal

noncomputable section

/-- The cap code and the actual support-menu code have the same literal
base and hidden entries. No coordinate map or new grid is involved. -/
theorem ancestor_native_signal_cell_components {W : ℕ}
    (N χ r t : ℝ) (p : PathData W) (root child : Fin p.C) (z : Ev) :
    nativeSignalCell (N^χ) r t (parentUnshearedCoordinates N p child (p.R root))
      (MvPolynomial.X 3) z=
      ((fun j => jointCode ((N^χ)^(-r)) ((N^χ)^(-t))
        (fun i => unshearedPacketBase p child z i)
        (physicalParentSignal N p child (p.R root) z) j.castSucc),
       jointCode ((N^χ)^(-r)) ((N^χ)^(-t))
        (fun i => unshearedPacketBase p child z i)
        (physicalParentSignal N p child (p.R root) z) (Fin.last 3)) := by
  apply Prod.ext
  · ext j
    simp [nativeSignalCell,parentUnshearedCoordinates,jointCode,baseCode,
      Submission.Lib.K4AffineMeshCaps.baseMesh,Submission.Lib.K4MovingMeshBoxes.baseMesh]
  · simp [nativeSignalCell,parentUnshearedCoordinates,jointCode,Fin.snoc]

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ ε : ℝ}
    (Q : PreparedAngularPath d k p m H u τ) (hpure : Q.uniformPureCeiling ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hpure hd hp

/-- The actual original-law pure caps apply directly to the literal
joint support-menu fibers, with FULL child reference restored. This is
exactly the numerator consumed by retained-history palette pruning. -/
theorem Native.PreparedAngularPath.ancestor_joint_signal_child_power_caps
    (root child : Fin p.C) (hworld : p.γ child=p.γ root)
    (hscale : δ (d.N k) (p.r (p.lev child)) ≤ δ (d.N k) (p.r (p.lev root)))
    (hr : 0 ≤ p.r (p.lev child))
    (χ finest : ℝ) (hχ : 0 ≤ χ) (hdepth : p.r (p.lev child)+χ*finest ≤ d.L)
    (μ : Measure Ev) (hμ : μ ≤ d.μ k (p.γ root))
    (hbase : ∀ᵐ z ∂μ, z∈Q.base (p.γ root))
    (hFroot : ∀ᵐ z ∂μ, z∈p.F root) (hFchild : ∀ᵐ z ∂μ, z∈p.F child)
    {dimension f₀ error Kcap : ℝ} (hdim : 0 ≤ dimension)
    (hprofile : ∀ a, 0 ≤ a → a ≤ d.L → |d.f a-f₀-dimension*a| ≤ error)
    (hbudget : 512*(max p.κ (d.K k))^2*p.κ*4^dimension*
      d.N k^(2*error+(τ+2*δ₀*d.L)+ε) ≤ Kcap) :
    let reference := d.ν k (p.γ child) (p.A child)*
      ENNReal.ofReal (((2:ℝ)^p.T (p.lev child))⁻¹);
    ∀ r t, finest⁻¹ ≤ r → r ≤ finest → 0 ≤ t → t ≤ finest → ∀ q,
      μ {z | jointCode ((d.N k^χ)^(-r)) ((d.N k^χ)^(-t))
        (fun j => unshearedPacketBase p child z j)
        (physicalParentSignal (d.N k) p child (p.R root) z)=q} ≤
          ENNReal.ofReal (Kcap*(d.N k^χ)^(-3*r-dimension*t))*reference := by
  intro reference r t hrl hrh ht htf q
  have hN : 0 < d.N k := by linarith [hd.1 k]
  have href0 : reference ≠ 0 := mul_ne_zero (hp.assignment_mass_pos hN child).ne'
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hAtop : d.ν k (p.γ child) (p.A child) ≠ ⊤ :=
    ne_of_lt ((hp.assignment_mass_bounds hN child).2.trans_lt ENNReal.ofReal_lt_top)
  have hreftop : reference ≠ ⊤ := ENNReal.mul_ne_top hAtop ENNReal.ofReal_ne_top
  have hcap := Q.ancestor_signal_child_power_caps hpure hd hp root child hworld hscale hr
    χ finest hχ hdepth μ hμ hbase hFroot hFchild hdim hprofile hbudget
    r t hrl hrh ht htf (fun j => q j.castSucc,q (Fin.last 3))
  have hsub : {z | jointCode ((d.N k^χ)^(-r)) ((d.N k^χ)^(-t))
      (fun j => unshearedPacketBase p child z j)
      (physicalParentSignal (d.N k) p child (p.R root) z)=q} ⊆
      {z | nativeSignalCell (d.N k^χ) r t
        (parentUnshearedCoordinates (d.N k) p child (p.R root)) (MvPolynomial.X 3) z=
          (fun j => q j.castSucc,q (Fin.last 3))} := by
    intro z hz
    change nativeSignalCell (d.N k^χ) r t
      (parentUnshearedCoordinates (d.N k) p child (p.R root)) (MvPolynomial.X 3) z=_
    rw [ancestor_native_signal_cell_components]
    change jointCode ((d.N k^χ)^(-r)) ((d.N k^χ)^(-t))
      (fun j => unshearedPacketBase p child z j)
      (physicalParentSignal (d.N k) p child (p.R root) z)=q at hz
    rw [hz]
  simp only [Measure.smul_apply,smul_eq_mul] at hcap
  calc
    _ = reference*(reference⁻¹*μ {z | jointCode ((d.N k^χ)^(-r)) ((d.N k^χ)^(-t))
        (fun j => unshearedPacketBase p child z j)
        (physicalParentSignal (d.N k) p child (p.R root) z)=q}) := by
      rw [←mul_assoc,ENNReal.mul_inv_cancel href0 hreftop,one_mul]
    _ ≤ reference*(reference⁻¹*μ {z | nativeSignalCell (d.N k^χ) r t
        (parentUnshearedCoordinates (d.N k) p child (p.R root)) (MvPolynomial.X 3) z=
          (fun j => q j.castSucc,q (Fin.last 3))}) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl (measure_mono hsub))
    _ ≤ reference*ENNReal.ofReal (Kcap*(d.N k^χ)^(-3*r-dimension*t)) :=
      mul_le_mul' le_rfl hcap
    _ = _ := mul_comm _ _

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
