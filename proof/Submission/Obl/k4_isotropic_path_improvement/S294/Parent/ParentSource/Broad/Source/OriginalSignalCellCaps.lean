-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.OriginalSignalCellCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/OriginalSignalCellCaps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1046 (branch x0943), commit 1fcc75a78b90aa1b479052c83612b68563af73b6,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/OriginalSignalCellCaps.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalPowerGridCaps
import Submission.Lib.K4ReferenceMeshPreparation.NativeCaps

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Native
open Submission.Lib.K4ReferenceMeshPreparation
open scoped ENNReal

noncomputable section

/-- Split a literal anisotropic physical code into its base and signal indices. -/
theorem anisotropic_code_eq_snoc_iff (x : Fin 4 → ℝ) (baseMesh hidden : ℝ)
    (q : (Fin 3 → ℤ) × ℤ) :
    (fun j => ⌊x j / (if j = 3 then hidden else baseMesh)⌋) = Fin.snoc q.1 q.2 ↔
      ((fun j : Fin 3 => ⌊x j.castSucc / baseMesh⌋), ⌊x 3 / hidden⌋) = q := by
  constructor
  · intro h
    apply Prod.ext
    · funext j
      have hh := congrFun h j.castSucc
      have hj3 : (j.castSucc : Fin 4) ≠ 3 := Fin.castSucc_ne_last j
      simpa only [if_neg hj3, Fin.snoc_castSucc] using hh
    · have hh := congrFun h (Fin.last 3)
      change ⌊x 3 / hidden⌋ = q.2 at hh
      exact hh
  · intro h
    funext j
    fin_cases j
    · change ⌊x 0 / baseMesh⌋ = q.1 0
      exact congrFun (congrArg Prod.fst h) 0
    · change ⌊x 1 / baseMesh⌋ = q.1 1
      exact congrFun (congrArg Prod.fst h) 1
    · change ⌊x 2 / baseMesh⌋ = q.1 2
      exact congrFun (congrArg Prod.fst h) 2
    · change ⌊x 3 / hidden⌋ = q.2
      exact congrArg Prod.snd h

theorem Native.PathData.original_signal_cell_fiber {W : ℕ} (p : PathData W)
    (Nk Nmesh r t : ℝ) (old : Fin p.C) (q : NativeSignalCell) :
    {z | nativeSignalCell Nmesh r t
      (fun z => WithLp.ofLp (packetPhysicalPoint Nk p old z)) (MvPolynomial.X 3) z = q} =
    (p.originalPhysicalCode Nk old (Nmesh^(-r)) (Nmesh^(-t))) ⁻¹' {Fin.snoc q.1 q.2} := by
  ext z
  rw [mem_preimage, mem_singleton_iff, p.originalPhysicalCode_coordinates]
  rw [anisotropic_code_eq_snoc_iff]
  simp only [mem_setOf_eq, nativeSignalCell, MvPolynomial.eval_X]
  rfl

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ ε : ℝ}
    (Q : PreparedAngularPath d k p m H u τ) (hpure : Q.uniformPureCeiling ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hpure hd hp

/-- The genuine original source supplies the complete pure-cell input
of the accepted joint record/palette pruner, on every auxiliary spatial
and signal mesh at once. The prior and old-clock normalization is fixed. -/
theorem Native.PreparedAngularPath.original_signal_power_caps
    (old : Fin p.C) (hr : 0 ≤ p.r (p.lev old))
    (χ finest : ℝ) (hχ : 0 ≤ χ) (hdepth : p.r (p.lev old)+χ*finest ≤ d.L)
    (μ : Measure Ev) (hμ : μ ≤ d.μ k (p.γ old))
    (hbase : ∀ᵐ z ∂μ, z ∈ Q.base (p.γ old)) (hF : ∀ᵐ z ∂μ, z ∈ p.F old)
    {dimension f₀ error Kcap : ℝ}
    (hprofile : ∀ a, 0 ≤ a → a ≤ d.L → |d.f a-f₀-dimension*a| ≤ error)
    (hbudget : 512*(max p.κ (d.K k))^2*p.κ*d.N k^(2*error+τ+ε) ≤ Kcap) :
    let α := (d.ν k (p.γ old) (p.A old) *
      ENNReal.ofReal (((2 : ℝ)^p.T (p.lev old))⁻¹))⁻¹
    ∀ r t, finest⁻¹ ≤ r → r ≤ finest → 0 ≤ t → t ≤ finest → ∀ q,
      (α • μ) {z | nativeSignalCell (d.N k^χ) r t
        (fun z => WithLp.ofLp (packetPhysicalPoint (d.N k) p old z)) (MvPolynomial.X 3) z=q} ≤
          ENNReal.ofReal (Kcap*(d.N k^χ)^(-3*r-dimension*t)) := by
  intro α r t _hrl _hrh ht htf q
  have htarget : p.r (p.lev old)+χ*t ≤ d.L := by
    nlinarith [mul_le_mul_of_nonneg_left htf hχ]
  have holdL : p.r (p.lev old) ≤ d.L :=
    (le_add_of_nonneg_right (mul_nonneg hχ ht)).trans htarget
  rw [p.original_signal_cell_fiber, Measure.smul_apply, smul_eq_mul]
  exact Q.original_power_grid_cap hpure hd hp old hr χ r t hχ ht htarget
    μ hμ hbase hF (hprofile _ hr holdL)
    (hprofile _ (add_nonneg hr (mul_nonneg hχ ht)) htarget) hbudget _

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
