-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.RetainedAncestorBreadth, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.RetainedAncestorHistories
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.CurrentReferenceCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Forward.StripTransfer

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette
open Submission.Obl.k4_isotropic_path_improvement.S294.Forward
open scoped ENNReal

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A : ℝ} {θ : ENNReal}
    (F : PaletteFamily Q i stop a A θ) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hd hp

/-- Actual intrinsic breadth and retention of an original fine history
bound every strip of the ORIGINAL physical velocity. The reference is
that same full fineOriginalEvent, rather than a selected record. -/
theorem Native.PaletteFamily.fine_original_physical_strip_cap
    (hHE : ∀ w, H w⊆d.E k w)
    (hH : ∀ w, H w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (root fine : Fin p.C) (hactive : F.active root)
    (hf : p.lev fine=stop) (hw : p.γ fine=p.γ root)
    {r fraction : ℝ} (hfr : 0 ≤ fraction)
    (hwide : F.coding.code fine∉Q.intrinsicNarrowStates F.code stop F.U r fraction root)
    (hretained : F.coding.code fine∉fineRetentionFailures
      (Q.coarseLaw (p.lev root) (F.code root)) (finitePacketHistory p.lev p.γ p.F stop)
      (F.U root) (ENNReal.ofReal (1/8:ℝ)))
    (n : EuclideanSpace ℝ (Fin 2)) (hn : ‖n‖=1) (offset : ℝ) {width : ℝ}
    (hwidth : width*(∑ j : Fin 2, ∑ l : Fin 2, |p.Q root j l|) ≤
      r*((2:ℝ)^p.T (p.lev root)*|(p.Q root).det|)) :
    ((d.ν k (p.γ root)).prod volume)
      (F.fineOriginalEvent root fine univ∩{z | |inner ℝ n (v z.1)-offset| ≤ width}) ≤
      ENNReal.ofReal (8*fraction)*((d.ν k (p.γ root)).prod volume)
        (F.fineOriginalEvent root fine univ) := by
  let raw := (d.ν k (p.γ root)).prod (volume : Measure ℝ)
  let D := {z | finitePacketHistory p.lev p.γ p.F stop z=F.coding.code fine ∧ z∈F.U root}
  have transfer : TransferData Q F root := {
    active := hactive
    measurable_F := fun b => (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
    finite_world := fun w => ne_top_of_le_ne_top (by simp : (1:ENNReal)≠⊤)
      (Q.world_mass_le_one hd hHE w)
    measurable_residual := Q.residual_measurable }
  have hAE : worldSection (p.γ root) D =ᵐ[raw] F.fineOriginalEvent root fine univ := by
    have heq : worldSection (p.γ root) D=
        Q.residual (p.γ root)∩worldSection (p.γ root) D := by
      apply Set.Subset.antisymm
      · intro z hz
        exact ⟨(F.subset_coarse root hactive hz.2).1,hz⟩
      · exact inter_subset_right
    rw [heq]
    exact F.fine_original_source_ae hp hH root hactive fine hf hw
  have hcap := world_breadth_original F transfer hfr (And.intro hwide hretained)
    (hp.2.2.2.2.2.2.2 root).2.2.1 n hn offset hwidth
  have hnumAE :
      (worldSection (p.γ root) D∩{z | |inner ℝ n (v z.1)-offset| ≤ width}) =ᵐ[raw]
        (F.fineOriginalEvent root fine univ∩{z | |inner ℝ n (v z.1)-offset| ≤ width}) := by
    filter_upwards [hAE] with z hz
    simp only [mem_inter_iff]
    rw [hz]
  have hnumEq : worldSection (p.γ root)
      {z | finitePacketHistory p.lev p.γ p.F stop z=F.coding.code fine ∧ z∈F.U root ∧
        |inner ℝ n (v z.2.1)-offset| ≤ width}=
      worldSection (p.γ root) D∩{z | |inner ℝ n (v z.1)-offset| ≤ width} := by
    ext z
    simp only [worldSection,D,mem_inter_iff,mem_setOf_eq]
    tauto
  rw [hnumEq] at hcap
  rw [measure_congr hnumAE,measure_congr hAE] at hcap
  exact hcap

/-- The original whole-history floor already supplied by the palette
pruning preserves strip breadth on its current record. No further
state-dependent restriction is selected. -/
theorem Native.PaletteFamily.current_record_physical_strip_cap
    (hHE : ∀ w, H w⊆d.E k w)
    (hH : ∀ w, H w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (root fine : Fin p.C) (hactive : F.active root)
    (hf : p.lev fine=stop) (hw : p.γ fine=p.γ root)
    {r fraction : ℝ} (hfr : 0 ≤ fraction)
    (hwide : F.coding.code fine∉Q.intrinsicNarrowStates F.code stop F.U r fraction root)
    (hretained : F.coding.code fine∉fineRetentionFailures
      (Q.coarseLaw (p.lev root) (F.code root)) (finitePacketHistory p.lev p.γ p.F stop)
      (F.U root) (ENNReal.ofReal (1/8:ℝ)))
    (μ : Measure Ev) (hμ : μ ≤ (d.ν k (p.γ root)).prod volume)
    (piece : Set Ev) (hsub : piece⊆F.fineOriginalEvent root fine univ)
    (cut : ℝ) (hcut : 0 < cut)
    (hfloor : μ piece=0 ∨ ENNReal.ofReal cut*((d.ν k (p.γ root)).prod volume)
      (F.fineOriginalEvent root fine univ) ≤ μ piece)
    (n : EuclideanSpace ℝ (Fin 2)) (hn : ‖n‖=1) (offset : ℝ) {width : ℝ}
    (hwidth : width*(∑ j : Fin 2, ∑ l : Fin 2, |p.Q root j l|) ≤
      r*((2:ℝ)^p.T (p.lev root)*|(p.Q root).det|)) :
    μ (piece∩{z | |inner ℝ n (v z.1)-offset| ≤ width}) ≤
      ENNReal.ofReal ((8*fraction)/cut)*μ piece := by
  have hcap := F.fine_original_physical_strip_cap hd hp hHE hH root fine hactive hf hw
    hfr hwide hretained n hn offset hwidth
  have hh := current_record_ratio_of_history_cap ((d.ν k (p.γ root)).prod volume) μ hμ
    piece (F.fineOriginalEvent root fine univ) {z | |inner ℝ n (v z.1)-offset| ≤ width}
    hsub (ENNReal.ofReal_pos.mpr hcut).ne' ENNReal.ofReal_ne_top hfloor hcap
  simpa only [ENNReal.ofReal_div_of_pos hcut] using hh

/-- Transfer a genuine world-section event cap to the literal full
original fine-history event. The history identification is AE under the
unchanged original product law. -/
theorem Native.PaletteFamily.fine_original_event_cap_of_world
    (hH : ∀ w, H w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (root fine : Fin p.C) (hactive : F.active root)
    (hf : p.lev fine=stop) (hw : p.γ fine=p.γ root)
    (B : Set Ev) (cap : ENNReal)
    (hcap : ((d.ν k (p.γ root)).prod volume)
      (worldSection (p.γ root) {z | finitePacketHistory p.lev p.γ p.F stop z=F.coding.code fine ∧ z∈F.U root}∩B) ≤
      cap*((d.ν k (p.γ root)).prod volume)
        (worldSection (p.γ root) {z | finitePacketHistory p.lev p.γ p.F stop z=F.coding.code fine ∧ z∈F.U root})) :
    ((d.ν k (p.γ root)).prod volume) (F.fineOriginalEvent root fine univ∩B) ≤
      cap*((d.ν k (p.γ root)).prod volume) (F.fineOriginalEvent root fine univ) := by
  let raw := (d.ν k (p.γ root)).prod (volume : Measure ℝ)
  let D := {z | finitePacketHistory p.lev p.γ p.F stop z=F.coding.code fine ∧ z∈F.U root}
  have hAE : worldSection (p.γ root) D =ᵐ[raw] F.fineOriginalEvent root fine univ := by
    have heq : worldSection (p.γ root) D=Q.residual (p.γ root)∩worldSection (p.γ root) D := by
      apply Set.Subset.antisymm
      · intro z hz
        exact ⟨(F.subset_coarse root hactive hz.2).1,hz⟩
      · exact inter_subset_right
    rw [heq]
    exact F.fine_original_source_ae hp hH root hactive fine hf hw
  have hnumAE : worldSection (p.γ root) D∩B =ᵐ[raw] F.fineOriginalEvent root fine univ∩B := by
    filter_upwards [hAE] with z hz
    simp only [mem_inter_iff]
    rw [hz]
  rwa [measure_congr hnumAE,measure_congr hAE] at hcap

/-- The original fine-history law inherits the front's normalized
ancestor-velocity strip cap, using its actual non-narrow/retained flags. -/
theorem Native.PaletteFamily.fine_original_normalized_strip_cap
    (hHE : ∀ w, H w⊆d.E k w)
    (hH : ∀ w, H w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (root fine : Fin p.C) (hactive : F.active root)
    (hf : p.lev fine=stop) (hw : p.γ fine=p.γ root)
    {r fraction : ℝ} (hfr : 0 ≤ fraction)
    (hwide : F.coding.code fine∉Q.intrinsicNarrowStates F.code stop F.U r fraction root)
    (hretained : F.coding.code fine∉fineRetentionFailures
      (Q.coarseLaw (p.lev root) (F.code root)) (finitePacketHistory p.lev p.γ p.F stop)
      (F.U root) (ENNReal.ofReal (1/8:ℝ)))
    (n : EuclideanSpace ℝ (Fin 2)) (hn : ‖n‖=1) (offset : ℝ) :
    ((d.ν k (p.γ root)).prod volume)
      (F.fineOriginalEvent root fine univ∩{z | p.normalizedVelocity root z∈
        Submission.Lib.K4VelocityStrips.affineStrip n offset r}) ≤
      ENNReal.ofReal (8*fraction)*((d.ν k (p.γ root)).prod volume)
        (F.fineOriginalEvent root fine univ) := by
  have transfer : TransferData Q F root := {
    active := hactive
    measurable_F := fun b => (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
    finite_world := fun w => ne_top_of_le_ne_top (by simp : (1:ENNReal)≠⊤)
      (Q.world_mass_le_one hd hHE w)
    measurable_residual := Q.residual_measurable }
  have hc := world_breadth F transfer hfr (And.intro hwide hretained) n hn offset
  have heq : worldSection (p.γ root)
      {z | finitePacketHistory p.lev p.γ p.F stop z=F.coding.code fine ∧ z∈F.U root ∧
        p.normalizedVelocity root z.2∈Submission.Lib.K4VelocityStrips.affineStrip n offset r}=
      worldSection (p.γ root) {z | finitePacketHistory p.lev p.γ p.F stop z=F.coding.code fine ∧ z∈F.U root}∩
        {z | p.normalizedVelocity root z∈Submission.Lib.K4VelocityStrips.affineStrip n offset r} := by
    ext z
    simp only [worldSection,mem_inter_iff,mem_ofPred_eq]
    tauto
  rw [heq] at hc
  exact F.fine_original_event_cap_of_world hd hp hH root fine hactive hf hw _ _ hc

/-- The exact scaled normalized-velocity strip estimate consumed by the
ancestor graph stage. Its only width condition is6κ radius≤frontRadius.
The current-record palette floor pays the same cut once. -/
theorem Native.PaletteFamily.current_record_scaled_normalized_strip_cap
    (hHE : ∀ w, H w⊆d.E k w)
    (hH : ∀ w, H w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (root fine : Fin p.C) (hactive : F.active root)
    (hf : p.lev fine=stop) (hw : p.γ fine=p.γ root)
    {r fraction : ℝ} (hfr : 0 ≤ fraction)
    (hwide : F.coding.code fine∉Q.intrinsicNarrowStates F.code stop F.U r fraction root)
    (hretained : F.coding.code fine∉fineRetentionFailures
      (Q.coarseLaw (p.lev root) (F.code root)) (finitePacketHistory p.lev p.γ p.F stop)
      (F.U root) (ENNReal.ofReal (1/8:ℝ)))
    (μ : Measure Ev) (hμ : μ ≤ (d.ν k (p.γ root)).prod volume)
    (piece : Set Ev) (hsub : piece⊆F.fineOriginalEvent root fine univ)
    (cut : ℝ) (hcut : 0 < cut)
    (hfloor : μ piece=0 ∨ ENNReal.ofReal cut*((d.ν k (p.γ root)).prod volume)
      (F.fineOriginalEvent root fine univ) ≤ μ piece)
    (radius : ℝ) (hwidth : (6*p.κ)*radius ≤ r)
    (n center : EuclideanSpace ℝ (Fin 2)) (hn : ‖n‖=1) :
    μ (piece∩{z | |Inner.inner ℝ n ((6*p.κ)⁻¹ • p.normalizedVelocity root z-center)| ≤ radius}) ≤
      ENNReal.ofReal ((8*fraction)/cut)*μ piece := by
  have hc : 0 < 6*p.κ := by linarith [hp.1]
  let B := {z | |Inner.inner ℝ n ((6*p.κ)⁻¹ • p.normalizedVelocity root z-center)| ≤ radius}
  have hstrip : B⊆{z | p.normalizedVelocity root z∈
      Submission.Lib.K4VelocityStrips.affineStrip n ((6*p.κ)*Inner.inner ℝ n center) r} := by
    intro z hz
    change |Inner.inner ℝ (p.normalizedVelocity root z) n-(6*p.κ)*Inner.inner ℝ n center| ≤ r
    have heq : Inner.inner ℝ (p.normalizedVelocity root z) n-(6*p.κ)*Inner.inner ℝ n center=
        (6*p.κ)*Inner.inner ℝ n ((6*p.κ)⁻¹ • p.normalizedVelocity root z-center) := by
      rw [inner_sub_right,real_inner_smul_right,real_inner_comm (p.normalizedVelocity root z) n]
      rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    rw [heq,abs_mul,abs_of_pos hc]
    exact (mul_le_mul_of_nonneg_left hz hc.le).trans hwidth
  have hcap := (measure_mono (show F.fineOriginalEvent root fine univ∩B⊆
      F.fineOriginalEvent root fine univ∩{z | p.normalizedVelocity root z∈
        Submission.Lib.K4VelocityStrips.affineStrip n ((6*p.κ)*Inner.inner ℝ n center) r}
      from fun z hz => ⟨hz.1,hstrip hz.2⟩)).trans
    (F.fine_original_normalized_strip_cap hd hp hHE hH root fine hactive hf hw hfr hwide hretained
      n hn ((6*p.κ)*Inner.inner ℝ n center))
  have hh := current_record_ratio_of_history_cap ((d.ν k (p.γ root)).prod volume) μ hμ
    piece (F.fineOriginalEvent root fine univ) B hsub (ENNReal.ofReal_pos.mpr hcut).ne'
    ENNReal.ofReal_ne_top hfloor hcap
  simpa only [ENNReal.ofReal_div_of_pos hcut] using hh

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
