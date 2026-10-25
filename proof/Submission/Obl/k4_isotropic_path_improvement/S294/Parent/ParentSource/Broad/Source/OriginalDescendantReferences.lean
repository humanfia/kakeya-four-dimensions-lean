-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.OriginalDescendantReferences, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/OriginalDescendantReferences.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PreparedAncestry
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketTransfer

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native
open scoped ENNReal BigOperators

noncomputable section

/-- A packet's full original assignment, throughout its full original block. -/
def Native.PathData.fullCylinder {W : ℕ} (p : PathData W) (b : Fin p.C) : Set Ev :=
  p.A b ×ˢ Icc ((p.j b : ℝ) / (2 : ℝ)^p.T (p.lev b))
    (((p.j b : ℝ)+1) / (2 : ℝ)^p.T (p.lev b))

/-- True descendants retain the specified original parent, not only a
nonempty intersection with its counted set. -/
def Native.PathData.trueDescendants {W : ℕ} (p : PathData W)
    (old : Fin p.C) (level : ℕ) : Finset (Fin p.C) :=
  Finset.univ.filter (fun b => p.lev b=level ∧
    p.par^[p.lev b-p.lev old] b=old)

def Native.PathData.oldEndpoints {W : ℕ} (p : PathData W)
    (old : Fin p.C) : Set Ev :=
  {z | ∃ n : ℕ, z.2=(n : ℝ)/(2 : ℝ)^p.T (p.lev old)}

theorem Native.PathData.oldEndpoints_measurable {W : ℕ} (p : PathData W)
    (old : Fin p.C) : MeasurableSet (p.oldEndpoints old) := by
  have heq : p.oldEndpoints old=(univ : Set Ln) ×ˢ
      range (fun n : ℕ => (n : ℝ)/(2 : ℝ)^p.T (p.lev old)) := by
    ext z
    simp [oldEndpoints,eq_comm]
  rw [heq]
  exact MeasurableSet.univ.prod (countable_range _).measurableSet

/-- The existing original-product endpoint theorem removes the closed
block ambiguity with exactly zero mass loss. -/
theorem Native.PathData.remove_oldEndpoints_mass {W : ℕ} (p : PathData W)
    (μ : Measure Ln) (old : Fin p.C) (source : Set Ev) :
    (μ.prod volume) (source\p.oldEndpoints old)=(μ.prod volume) source := by
  exact measure_sdiff_null' (measure_mono_null inter_subset_right
    (Broad.prod_endpoints_null μ (p.T (p.lev old))))

theorem Native.PathData.fullCylinder_mass {W : ℕ} (p : PathData W)
    (μ : Measure Ln) (b : Fin p.C) :
    (μ.prod volume) (p.fullCylinder b)=
      μ (p.A b)*ENNReal.ofReal (((2 : ℝ)^p.T (p.lev b))⁻¹) := by
  rw [fullCylinder,Measure.prod_prod,Real.volume_Icc]
  congr 2
  field_simp
  ring

section Path

variable {W : ℕ} {p : PathData W} {N L κ₁ δ₀ σ : ℝ}
    {m Mp Dp : ℕ} {s : ℕ → ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ} {f : ℝ → ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

theorem Native.PathData.Valid.fullCylinder_measurable (b : Fin p.C) :
    MeasurableSet (p.fullCylinder b) := by
  obtain ⟨-, -, hch⟩ := hp.2.2.2.2.2.2.2 b
  exact hch.2.2.2.2.2.2.1.prod measurableSet_Icc

theorem Native.PathData.Valid.counted_subset_fullCylinder (b : Fin p.C) :
    p.F b ⊆ p.fullCylinder b := by
  obtain ⟨-, -, hch⟩ := hp.2.2.2.2.2.2.2 b
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hF, -⟩ := hch
  intro z hz
  exact ⟨(hF z hz).2.1,(hF z hz).2.2.1⟩

/-- Original block nesting holds on the entire cylinders, independently
of every later incidence restriction. -/
theorem Native.PathData.Valid.iterate_par_fullCylinder (n : ℕ) :
    ∀ b : Fin p.C, n ≤ p.lev b →
      p.fullCylinder b ⊆ p.fullCylinder (p.par^[n] b) := by
  induction n with
  | zero => intro b _; simp
  | succ n ih =>
    intro b hn
    obtain ⟨-, -, hch⟩ := hp.2.2.2.2.2.2.2 b
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hparent⟩ := hch
    obtain ⟨hl, -, hA, -, ht0, ht1⟩ := hparent (by omega)
    rw [Function.iterate_succ_apply]
    apply Subset.trans _ (ih (p.par b) (by omega))
    intro z hz
    exact ⟨hA hz.1,ht0.trans hz.2.1,hz.2.2.trans ht1⟩

/-- Full original references of true descendants have exactly one
parent reference budget. No saturation or packet-count factor occurs. -/
theorem Native.PathData.Valid.true_descendant_reference_sum
    (old : Fin p.C) (level : ℕ) (hlevel : p.lev old ≤ level) :
    (∑ b ∈ p.trueDescendants old level,
      ν (p.γ old) (p.A b)*ENNReal.ofReal (((2 : ℝ)^p.T level)⁻¹)) ≤
        ν (p.γ old) (p.A old)*ENNReal.ofReal (((2 : ℝ)^p.T (p.lev old))⁻¹) := by
  classical
  let S := p.trueDescendants old level
  let μ : Measure Ev := (ν (p.γ old)).prod volume
  have hspec (b : Fin p.C) (hb : b∈S) :
      p.lev b=level ∧ p.γ b=p.γ old ∧ p.fullCylinder b⊆p.fullCylinder old := by
    obtain ⟨hl,ha⟩ := (Finset.mem_filter.mp hb).2
    obtain ⟨-,hg,-⟩ := Broad.iterate_par_spec hp.toOriginal (p.lev b-p.lev old) b
      (Nat.sub_le _ _)
    change p.γ (p.par^[p.lev b-p.lev old] b)=p.γ b at hg
    refine ⟨hl,?_,?_⟩
    · simpa only [ha] using hg.symm
    · simpa only [ha] using hp.iterate_par_fullCylinder (p.lev b-p.lev old) b (Nat.sub_le _ _)
  have hdisjoint : (S : Set (Fin p.C)).Pairwise
      (Function.onFun (AEDisjoint μ) p.fullCylinder) := by
    intro b hb c hc hne
    obtain ⟨hlb,hgb,-⟩ := hspec b hb
    obtain ⟨hlc,hgc,-⟩ := hspec c hc
    by_cases hj : p.j b=p.j c
    · exact Broad.aedisjoint_of_lines
        (hp.2.2.2.2.2.2.1 b c hne (hlb.trans hlc.symm) (hgb.trans hgc.symm) hj)
        (fun _ hz => hz.1) (fun _ hz => hz.1)
    · apply Broad.aedisjoint_of_blocks (T:=p.T level) hj
      · intro z hz
        simpa only [hlb] using hz.2
      · intro z hz
        simpa only [hlc] using hz.2
  calc
    _ = ∑ b∈S, μ (p.fullCylinder b) := by
      apply Finset.sum_congr rfl
      intro b hb
      dsimp only [μ]
      rw [p.fullCylinder_mass, (hspec b hb).1]
    _ = μ (⋃ b∈S, p.fullCylinder b) :=
      (measure_biUnion_finset₀ hdisjoint (fun b _ => (hp.fullCylinder_measurable b).nullMeasurableSet)).symm
    _ ≤ μ (p.fullCylinder old) := measure_mono (iUnion₂_subset (fun b hb => (hspec b hb).2.2))
    _ = _ := p.fullCylinder_mass _ old

/-- Away from original block endpoints, a counted incidence identifies
its actual original packet at a fixed level and world. -/
theorem Native.PathData.Valid.eq_of_common_nonendpoint
    (old other : Fin p.C) (hlevel : p.lev other=p.lev old)
    (hworld : p.γ other=p.γ old) {z : Ev}
    (hzo : z∈p.F old) (hzt : z∈p.F other)
    (hboundary : z∉p.oldEndpoints old) : other=old := by
  by_contra hne
  have hzo := hp.counted_subset_fullCylinder old hzo
  have hzt := hp.counted_subset_fullCylinder other hzt
  by_cases hj : p.j other=p.j old
  · exact (disjoint_left.mp (hp.2.2.2.2.2.2.1 other old hne hlevel hworld hj)) hzt.1 hzo.1
  · have ht : z.2∈Icc ((p.j other : ℝ)/(2 : ℝ)^p.T (p.lev old))
        (((p.j other : ℝ)+1)/(2 : ℝ)^p.T (p.lev old)) := by
      simpa only [hlevel] using hzt.2
    have hden : 0 < (2 : ℝ)^p.T (p.lev old) := by positivity
    apply hboundary
    rcases lt_or_gt_of_ne hj with hlo | hhi
    · refine ⟨p.j old,le_antisymm ?_ hzo.2.1⟩
      apply ht.2.trans
      apply div_le_div_of_nonneg_right _ hden.le
      exact_mod_cast hlo
    · refine ⟨p.j other,le_antisymm ?_ ht.1⟩
      apply hzo.2.2.trans
      apply div_le_div_of_nonneg_right _ hden.le
      exact_mod_cast hhi

/-- Any source inside one original root and the original terminal
cover lies on its TRUE descendants, after the zero-loss boundary cut. -/
theorem Native.PathData.Valid.true_descendants_cover
    (old : Fin p.C) (level : ℕ) (hlevel : p.lev old ≤ level) (hlast : level ≤ m-1)
    (source : Set Ev) (hsource : source⊆p.F old)
    (hterminal : ∀ z∈source, ∃ terminal : Fin p.C,
      p.lev terminal=m-1 ∧ p.γ terminal=p.γ old ∧ z∈p.F terminal) :
    source\p.oldEndpoints old ⊆ ⋃ b∈p.trueDescendants old level, p.F b := by
  classical
  intro z hz
  obtain ⟨terminal,ht,hw,hzt⟩ := hterminal z hz.1
  let b := p.par^[p.lev terminal-level] terminal
  obtain ⟨hlb,hgb,hFb⟩ := Broad.iterate_par_spec hp.toOriginal
    (p.lev terminal-level) terminal (Nat.sub_le _ _)
  change p.lev b=p.lev terminal-(p.lev terminal-level) at hlb
  change p.γ b=p.γ terminal at hgb
  change p.F terminal⊆p.F b at hFb
  have hlb' : p.lev b=level := by omega
  let a := p.par^[p.lev b-p.lev old] b
  obtain ⟨hla,hga,hFa⟩ := Broad.iterate_par_spec hp.toOriginal
    (p.lev b-p.lev old) b (Nat.sub_le _ _)
  change p.lev a=p.lev b-(p.lev b-p.lev old) at hla
  change p.γ a=p.γ b at hga
  change p.F b⊆p.F a at hFa
  have hae : a=old := hp.eq_of_common_nonendpoint old a (by omega)
    (hga.trans (hgb.trans hw)) (hsource hz.1) (hFa (hFb hzt)) hz.2
  have hb : b∈p.trueDescendants old level :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ b,hlb',hae⟩
  exact mem_iUnion₂.mpr ⟨b,hb,hFb hzt⟩

/-- A dense source in a single chosen root selects a later original
descendant at the SAME full-reference density. The original laws and
assignment denominators are unchanged. -/
theorem Native.PathData.Valid.exists_dense_true_descendant
    (old : Fin p.C) [IsFiniteMeasure (ν (p.γ old))]
    (hA : ν (p.γ old) (p.A old)≠0)
    (level : ℕ) (hlevel : p.lev old ≤ level) (hlast : level ≤ m-1)
    (source : Set Ev) (hsource : source⊆p.F old)
    (hterminal : ∀ z∈source, ∃ terminal : Fin p.C,
      p.lev terminal=m-1 ∧ p.γ terminal=p.γ old ∧ z∈p.F terminal)
    {density : ℝ} (hdensity : 0 < density)
    (hmass : ENNReal.ofReal density*
      (ν (p.γ old) (p.A old)*ENNReal.ofReal (((2 : ℝ)^p.T (p.lev old))⁻¹)) ≤
        ((ν (p.γ old)).prod volume) source) :
    ∃ b : Fin p.C, b∈p.trueDescendants old level ∧
      p.lev b=level ∧ p.γ b=p.γ old ∧ p.A b⊆p.A old ∧ p.F b⊆p.F old ∧
      p.fullCylinder b⊆p.fullCylinder old ∧ ν (p.γ old) (p.A b)≠0 ∧
      ENNReal.ofReal density*
        (ν (p.γ old) (p.A b)*ENNReal.ofReal (((2 : ℝ)^p.T level)⁻¹)) ≤
          ((ν (p.γ old)).prod volume) (source∩p.F b) := by
  classical
  let S := p.trueDescendants old level
  let μ : Measure Ev := (ν (p.γ old)).prod volume
  let reference := ν (p.γ old) (p.A old)*ENNReal.ofReal (((2 : ℝ)^p.T (p.lev old))⁻¹)
  let capacity := fun b : Fin p.C => ν (p.γ old) (p.A b)*ENNReal.ofReal (((2 : ℝ)^p.T level)⁻¹)
  let mass := fun b : Fin p.C => μ (source∩p.F b)
  have href : reference≠0 := mul_ne_zero hA (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hrefTop : reference≠∞ := ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  have hcover : source\p.oldEndpoints old ⊆ ⋃ b∈S, source∩p.F b := by
    intro z hz
    obtain ⟨b,hb,hzb⟩ := mem_iUnion₂.mp
      (hp.true_descendants_cover old level hlevel hlast source hsource hterminal hz)
    exact mem_iUnion₂.mpr ⟨b,hb,hz.1,hzb⟩
  have hmassSum : ENNReal.ofReal density*reference ≤ ∑ b∈S, mass b := by
    calc
      _ ≤ μ source := hmass
      _ = μ (source\p.oldEndpoints old) := (p.remove_oldEndpoints_mass _ old source).symm
      _ ≤ μ (⋃ b∈S, source∩p.F b) := measure_mono hcover
      _ ≤ _ := measure_biUnion_finset_le _ _
  have hcapSum : (∑ b∈S,capacity b) ≤ ENNReal.ofReal (1 : ℝ)*reference := by
    simpa only [ENNReal.ofReal_one,one_mul] using hp.true_descendant_reference_sum old level hlevel
  have hdom (b : Fin p.C) (hb : b∈S) : mass b ≤ capacity b := by
    have hl := (Finset.mem_filter.mp hb).2.1
    apply (measure_mono (inter_subset_right.trans (hp.counted_subset_fullCylinder b))).trans_eq
    dsimp only [μ,capacity]
    rw [p.fullCylinder_mass,hl]
  obtain ⟨b,hb,hpos,hfloor⟩ := exists_packet_of_capacity_bound_ennreal S capacity mass
    href hrefTop hdensity (by norm_num : (0 : ℝ) < 1)
    (fun b _ => ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top)
    hdom hmassSum hcapSum
  obtain ⟨hl,ha⟩ := (Finset.mem_filter.mp hb).2
  obtain ⟨-,hg,hF⟩ := Broad.iterate_par_spec hp.toOriginal (p.lev b-p.lev old) b (Nat.sub_le _ _)
  change p.γ (p.par^[p.lev b-p.lev old] b)=p.γ b at hg
  change p.F b⊆p.F (p.par^[p.lev b-p.lev old] b) at hF
  have hCylinder : p.fullCylinder b⊆p.fullCylinder old := by
    simpa only [ha] using hp.iterate_par_fullCylinder (p.lev b-p.lev old) b (Nat.sub_le _ _)
  refine ⟨b,hb,hl,?_,?_,?_,?_,(mul_ne_zero_iff.mp hpos).1,?_⟩
  · simpa only [ha] using hg.symm
  · intro l hl
    apply (hCylinder (show (l,(p.j b : ℝ)/(2 : ℝ)^p.T (p.lev b))∈p.fullCylinder b from ?_)).1
    refine ⟨hl,le_rfl,?_⟩
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  · simpa only [ha] using hF
  · exact hCylinder
  · simpa only [div_one] using hfloor

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
