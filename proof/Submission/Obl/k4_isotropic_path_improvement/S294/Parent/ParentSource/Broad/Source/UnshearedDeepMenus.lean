-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.UnshearedDeepMenus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/UnshearedDeepMenus.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1046 (branch x0943), commit 1fcc75a78b90aa1b479052c83612b68563af73b6,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/UnshearedDeepMenus.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.UnshearedOldBase
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.DeepBaseMenus
import Submission.Lib.K4OriginalGeometricReference.JointSupport
import Submission.Lib.K4SignalMeshSupport.Terminal

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Native
open Submission.Lib.K4ListedExceptions
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells

noncomputable section

def Native.PathData.unshearedDeepRadius {W : ℕ} (p : PathData W) (old deep : Fin p.C) : ℝ :=
  (1+p.κ^2+‖p.u deep‖)*((2:ℝ)^p.T (p.lev old)/(2:ℝ)^p.T (p.lev deep))

section Path

variable {W : ℕ} {p : PathData W} {N L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

/-- A whole deeper packet fits in a small box in unsheared old units.
Only its actual center velocity and the clock ratio are charged. -/
theorem Native.PathData.Valid.deep_unsheared_base_box (old deep : Fin p.C) :
    ∃ anchor : Fin 3 → ℝ, ∀ z∈p.F deep, ∀ j,
      |unshearedPacketBase p old z j-anchor j| ≤ p.unshearedDeepRadius old deep := by
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  let hOld := ((2:ℝ)^p.T (p.lev old))⁻¹
  let hDeep := ((2:ℝ)^p.T (p.lev deep))⁻¹
  let tOld := (p.j old:ℝ)*hOld
  let tDeep := (p.j deep:ℝ)*hDeep
  let ratio := (2:ℝ)^p.T (p.lev old)/(2:ℝ)^p.T (p.lev deep)
  let centerOld := p.c old+tOld • p.u old
  let centerDeep := p.c deep+tDeep • p.u deep
  have hhOld : 0 < hOld := by dsimp [hOld]; positivity
  have hhDeep : 0 < hDeep := by dsimp [hDeep]; positivity
  have hratio : 0 ≤ ratio := by dsimp [ratio]; positivity
  have hratioEq : hDeep/hOld=ratio := by
    dsimp [hDeep,hOld,ratio]
    simp only [div_eq_mul_inv,inv_inv]
    ring
  let anchor : Fin 3 → ℝ := ![(tDeep-tOld)/hOld,
    (centerDeep 0-centerOld 0)/hOld,(centerDeep 1-centerOld 1)/hOld]
  refine ⟨anchor,?_⟩
  intro z hz j
  rcases hp.2.2.2.2.2.2.2 deep with
    ⟨_,_,hdet,_,_,hsize,_,_,_,_,_,hfit,hF,_⟩
  have ht := (hF z hz).2.2.1
  have htime : tDeep ≤ z.2 ∧ z.2 ≤ tDeep+hDeep := by
    simpa only [tDeep,hDeep,div_eq_mul_inv,add_mul,one_mul,mem_Icc] using ht
  have hdt : |z.2-tDeep| ≤ hDeep := by rw [abs_le]; constructor <;> linarith
  have herror : ‖y z.1 z.2-p.c deep-z.2 • p.u deep‖ ≤ p.κ^2*hDeep := by
    apply physical_error_le_of_frame hdet hκ hhDeep
      (by simpa only [hDeep,div_eq_mul_inv] using hsize)
    exact ((hfit z.1 (hF z hz).2.1).2.2 z.2 ht).1
  have hposition : ‖y z.1 z.2-centerDeep‖ ≤ (p.κ^2+‖p.u deep‖)*hDeep := by
    have heq : y z.1 z.2-centerDeep=
        (y z.1 z.2-p.c deep-z.2 • p.u deep)+(z.2-tDeep) • p.u deep := by
      dsimp only [centerDeep]
      module
    calc
      _ ≤ ‖y z.1 z.2-p.c deep-z.2 • p.u deep‖+‖(z.2-tDeep) • p.u deep‖ :=
        heq ▸ norm_add_le _ _
      _ = ‖y z.1 z.2-p.c deep-z.2 • p.u deep‖+|z.2-tDeep| * ‖p.u deep‖ := by
        rw [norm_smul,Real.norm_eq_abs]
      _ ≤ p.κ^2*hDeep+hDeep*‖p.u deep‖ :=
        add_le_add herror (mul_le_mul_of_nonneg_right hdt (norm_nonneg _))
      _ = _ := by ring
  have hR : ratio ≤ p.unshearedDeepRadius old deep := by
    change ratio ≤ (1+p.κ^2+‖p.u deep‖)*ratio
    nlinarith [sq_nonneg p.κ,norm_nonneg (p.u deep)]
  have hspatial (i : Fin 2) :
      |(y z.1 z.2 i-centerOld i)/hOld-(centerDeep i-centerOld i)/hOld| ≤
        p.unshearedDeepRadius old deep := by
    have hc : |y z.1 z.2 i-centerDeep i| ≤ (p.κ^2+‖p.u deep‖)*hDeep := by
      exact (show |y z.1 z.2 i-centerDeep i| ≤ ‖y z.1 z.2-centerDeep‖ from by
        simpa only [PiLp.sub_apply,Real.norm_eq_abs] using
          PiLp.norm_apply_le (y z.1 z.2-centerDeep) i).trans hposition
    calc
      _ = |y z.1 z.2 i-centerDeep i|/hOld := by
        rw [←sub_div,abs_div,abs_of_pos hhOld]
        congr 1
        ring
      _ ≤ ((p.κ^2+‖p.u deep‖)*hDeep)/hOld :=
        div_le_div_of_nonneg_right hc hhOld.le
      _ = (p.κ^2+‖p.u deep‖)*ratio := by rw [mul_div_assoc,hratioEq]
      _ ≤ p.unshearedDeepRadius old deep := by
        change _ ≤ (1+p.κ^2+‖p.u deep‖)*ratio
        nlinarith
  have htimeCoord : |(z.2-tOld)/hOld-(tDeep-tOld)/hOld| ≤
      p.unshearedDeepRadius old deep := by
    calc
      _ = |z.2-tDeep|/hOld := by
        rw [←sub_div,abs_div,abs_of_pos hhOld]
        congr 1
        ring
      _ ≤ hDeep/hOld := div_le_div_of_nonneg_right hdt hhOld.le
      _ ≤ _ := hratioEq.trans_le hR
  fin_cases j
  · exact htimeCoord
  · exact hspatial 0
  · exact hspatial 1

/-- The same whole-packet box supplies a Euclidean diameter. -/
theorem Native.PathData.Valid.deep_unsheared_base_diameter
    (old deep : Fin p.C) (z : Ev) (hz : z∈p.F deep) (z' : Ev) (hz' : z'∈p.F deep) :
    ‖unshearedPacketBase p old z-unshearedPacketBase p old z'‖ ≤
      6*p.unshearedDeepRadius old deep := by
  obtain ⟨anchor,hanchor⟩ := hp.deep_unsheared_base_box old deep
  have hc (j : Fin 3) :
      |unshearedPacketBase p old z j-unshearedPacketBase p old z' j| ≤
        2*p.unshearedDeepRadius old deep := by
    calc
      _ ≤ |unshearedPacketBase p old z j-anchor j|+
          |anchor j-unshearedPacketBase p old z' j| := abs_sub_le _ _ _
      _ ≤ _ := by rw [abs_sub_comm (anchor j)]; linarith [hanchor z hz j,hanchor z' hz' j]
  calc
    _ ≤ ∑ j : Fin 3, |(unshearedPacketBase p old z-unshearedPacketBase p old z') j| :=
      euclidean_norm_le_sum_abs _
    _ ≤ ∑ _j : Fin 3, 2*p.unshearedDeepRadius old deep :=
      Finset.sum_le_sum (fun j _ => hc j)
    _ = _ := by simp; ring

/-- Small actual deeper packets meet at most 27 unsheared base cells. -/
theorem Native.PathData.Valid.exists_deep_unsheared_base_menu
    (old deep : Fin p.C) {mesh : ℝ} (hmesh : 0 < mesh)
    (hsmall : p.unshearedDeepRadius old deep ≤ mesh) :
    ∃ Menu : Finset (Fin 3 → ℤ), Menu.card=27 ∧
      ∀ z∈p.F deep, baseCode mesh (fun j => unshearedPacketBase p old z j)∈Menu := by
  obtain ⟨anchor,hanchor⟩ := hp.deep_unsheared_base_box old deep
  let Menu := integerCodeBox 1 (fun j => ⌊anchor j/mesh⌋)
  refine ⟨Menu,by simp only [Menu,card_integerCodeBox]; norm_num,?_⟩
  intro z hz
  apply floor_code_mem_integerCodeBox 1 (fun j => unshearedPacketBase p old z j)
    anchor (fun _ => mesh) (fun _ => hmesh)
  intro j
  simpa only [Nat.cast_one,one_mul] using (hanchor z hz j).trans hsmall

/-- An arbitrary physical signal with one hidden mesh of oscillation on
the later original subset has a fixed 108-code joint menu. -/
theorem Native.PathData.Valid.exists_deep_unsheared_signal_menu
    (old deep : Fin p.C) {base hidden : ℝ} (hbase : 0 < base) (hhidden : 0 < hidden)
    (hsmall : p.unshearedDeepRadius old deep ≤ base)
    (signal : Ev → ℝ) (U : Set Ev) (hU : U⊆p.F deep)
    (hosc : ∀ z∈U, ∀ z'∈U, |signal z-signal z'| ≤ hidden) :
    ∃ Menu : Finset (Fin 4 → ℤ), (Menu.card:ℝ) ≤ 108 ∧
      ∀ z∈U, jointCode base hidden (fun j => unshearedPacketBase p old z j) (signal z)∈Menu := by
  classical
  obtain ⟨Base,hBase,hcover⟩ := hp.exists_deep_unsheared_base_menu old deep hbase hsmall
  obtain ⟨S,hS,hSc⟩ := Submission.Lib.K4SignalMeshSupport.terminal_support_of_fiber_oscillation
    U (fun z => baseCode base (fun j => unshearedPacketBase p old z j)) signal Base
      hhidden (show (0:ℝ) ≤ 1 by norm_num) (fun z hz => hcover z (hU hz))
      (fun z hz z' hz' _ => by simpa only [one_mul] using hosc z hz z' hz')
  let pack : (Fin 3 → ℤ) × ℤ → Fin 4 → ℤ := fun q => Fin.snoc q.1 q.2
  refine ⟨S.image pack,?_,?_⟩
  · calc
      _ ≤ (S.card:ℝ) := by exact_mod_cast Finset.card_image_le
      _ ≤ (Base.card:ℝ)*(2*1+2) := hS
      _ = 108 := by rw [hBase]; norm_num
  · intro z hz
    exact Finset.mem_image.mpr ⟨_,hSc z hz,rfl⟩

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
