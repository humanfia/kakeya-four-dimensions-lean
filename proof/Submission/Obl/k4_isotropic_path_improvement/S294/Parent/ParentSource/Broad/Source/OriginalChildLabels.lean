-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.OriginalChildLabels, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/OriginalChildLabels.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalDescendantReferences
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.NativePacketModel
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketPhysical
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
import Submission.Obl.k4_critical_conditional_row_preparation.Pruning
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.Dyadic
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldJetDiscovery

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native
open scoped ENNReal

noncomputable section

local instance (C : ℕ) : MeasurableSpace (Option (Fin C)) := ⊤
local instance (C : ℕ) : MeasurableSingletonClass (Option (Fin C)) := ⟨fun _ => trivial⟩

/-- Original full assignment and half-open time block at one level and world. -/
def Native.PathData.childCylinder {W : ℕ} (p : PathData W)
    (level : ℕ) (world : Fin W) (b : Fin p.C) : Set Ev :=
  {z | p.lev b=level ∧ p.γ b=world ∧ z.1∈p.A b ∧
    z.2∈Ico ((p.j b : ℝ)/(2 : ℝ)^p.T (p.lev b))
      (((p.j b : ℝ)+1)/(2 : ℝ)^p.T (p.lev b))}

/-- A true original child label. It reads the full original assignment,
not an evolving physical-state code or the retained incidence density. -/
def Native.PathData.childLabel {W : ℕ} (p : PathData W)
    (level : ℕ) (world : Fin W) : Ev → Option (Fin p.C) :=
  Submission.Obl.k4_critical_conditional_row_preparation.coverLabel
    (p.childCylinder level world)

def Native.PathData.levelEndpoints {W : ℕ} (p : PathData W) (level : ℕ) : Set Ev :=
  {z | ∃ n : ℕ, z.2=(n : ℝ)/(2 : ℝ)^p.T level}

/-- The fixed preceding source, with just the original endpoint ambiguity removed. -/
def Native.PathData.childReference {W : ℕ} (p : PathData W)
    (root : Fin p.C) (level : ℕ) (source : Set Ev) : Set Ev :=
  (source\p.oldEndpoints root)\p.levelEndpoints level

/-- Undo only the actual root clock; the original indexed line is retained. -/
def Native.PathData.childClockPoint {W : ℕ} (p : PathData W)
    (root : Fin p.C) (z : Ev) : Ev :=
  (z.1,(z.2+(p.j root : ℝ))/(2 : ℝ)^p.T (p.lev root))

def Native.PathData.childClockReference {W : ℕ} (p : PathData W)
    (root : Fin p.C) (level : ℕ) (source : Set Ev) : Set Ev :=
  p.childClockPoint root ⁻¹' p.childReference root level source

def Native.PathData.childClockLabel {W : ℕ} (p : PathData W)
    (root : Fin p.C) (level : ℕ) (world : Fin W) : Ev → Option (Fin p.C) :=
  p.childLabel level world ∘ p.childClockPoint root

theorem Native.PathData.childClockPoint_measurable {W : ℕ} (p : PathData W) (root : Fin p.C) :
    Measurable (p.childClockPoint root) := by unfold childClockPoint; fun_prop

theorem Native.PathData.levelEndpoints_measurable {W : ℕ} (p : PathData W) (level : ℕ) :
    MeasurableSet (p.levelEndpoints level) := by
  have heq : p.levelEndpoints level=(univ : Set Ln) ×ˢ
      range (fun n : ℕ => (n : ℝ)/(2 : ℝ)^p.T level) := by
    ext z
    simp [levelEndpoints,eq_comm]
  rw [heq]
  exact MeasurableSet.univ.prod (countable_range _).measurableSet

theorem Native.PathData.remove_levelEndpoints_mass {W : ℕ} (p : PathData W)
    (μ : Measure Ln) (level : ℕ) (source : Set Ev) :
    (μ.prod volume) (source\p.levelEndpoints level)=(μ.prod volume) source := by
  exact measure_sdiff_null' (measure_mono_null inter_subset_right
    (Broad.prod_endpoints_null μ (p.T level)))

theorem Native.PathData.childReference_measurable {W : ℕ} (p : PathData W)
    (root : Fin p.C) (level : ℕ) {source : Set Ev} (hsource : MeasurableSet source) :
    MeasurableSet (p.childReference root level source) :=
  (hsource.diff (p.oldEndpoints_measurable root)).diff (p.levelEndpoints_measurable level)

theorem Native.PathData.childReference_mass {W : ℕ} (p : PathData W)
    (μ : Measure Ln) (root : Fin p.C) (level : ℕ) (source : Set Ev) :
    (μ.prod volume) (p.childReference root level source)=(μ.prod volume) source := by
  rw [childReference,p.remove_levelEndpoints_mass,p.remove_oldEndpoints_mass]

theorem Native.PathData.childClockReference_measurable {W : ℕ} (p : PathData W)
    (root : Fin p.C) (level : ℕ) {source : Set Ev} (hsource : MeasurableSet source) :
    MeasurableSet (p.childClockReference root level source) :=
  (p.childReference_measurable root level hsource).preimage (p.childClockPoint_measurable root)

theorem packetTime_eq_dyadic {W : ℕ} (p : PathData W) (root : Fin p.C) (z : Ev) :
    packetTime p root z=(2 : ℝ)^p.T (p.lev root)*z.2-p.j root := by
  dsimp [packetTime,nativeOldBaseFrame]
  field_simp

theorem Native.PathData.packetTime_childClockPoint {W : ℕ} (p : PathData W)
    (root : Fin p.C) (z : Ev) : packetTime p root (p.childClockPoint root z)=z.2 := by
  rw [packetTime_eq_dyadic]
  dsimp only [childClockPoint]
  field_simp
  ring

theorem Native.PathData.childClockPoint_packetTime {W : ℕ} (p : PathData W)
    (root : Fin p.C) (z : Ev) : p.childClockPoint root (z.1,packetTime p root z)=z := by
  rw [packetTime_eq_dyadic]
  dsimp only [childClockPoint]
  apply Prod.ext
  · rfl
  · dsimp only
    field_simp
    ring

section Path

variable {W : ℕ} {p : PathData W} {N L κ₁ δ₀ σ : ℝ}
    {m Mp Dp : ℕ} {s : ℕ → ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ} {f : ℝ → ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

/-- This is precisely the inverse of the original frozen packet's time
change, with the same original indexed line. -/
theorem Native.PathData.Valid.childClockPoint_eq_timeChange_symm (root : Fin p.C) :
    p.childClockPoint root=((hp.frozenPacket root).timeChange.symm : Ev → Ev) := by
  funext z
  apply (hp.frozenPacket root).timeChange.injective
  rw [MeasurableEquiv.apply_symm_apply]
  have he (x : Ev) : (hp.frozenPacket root).timeChange x=(x.1,packetTime p root x) := by
    rw [(hp.frozenPacket root).timeChange_apply]
    have hframe : (hp.frozenPacket root).unitFrame=nativeOldBaseFrame p root := rfl
    rw [hframe]
    simp only [packetTime,div_eq_mul_inv,mul_comm]
  rw [he,p.packetTime_childClockPoint]
  rfl

theorem Native.PathData.Valid.childClockReference_eq_timeChange_image
    (root : Fin p.C) (level : ℕ) (source : Set Ev) :
    p.childClockReference root level source=
      (hp.frozenPacket root).timeChange '' p.childReference root level source := by
  rw [childClockReference,hp.childClockPoint_eq_timeChange_symm root]
  ext z
  constructor
  · intro hz
    exact ⟨(hp.frozenPacket root).timeChange.symm z,hz,MeasurableEquiv.apply_symm_apply _ z⟩
  · rintro ⟨x,hx,rfl⟩
    simpa only [mem_preimage,MeasurableEquiv.symm_apply_apply] using hx

theorem Native.PathData.Valid.childCylinder_measurable (level : ℕ) (world : Fin W)
    (b : Fin p.C) : MeasurableSet (p.childCylinder level world b) := by
  classical
  by_cases hl : p.lev b=level
  · by_cases hw : p.γ b=world
    · have hA := (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.1
      change MeasurableSet (p.A b) at hA
      convert hA.prod (measurableSet_Ico : MeasurableSet
        (Ico ((p.j b : ℝ)/(2 : ℝ)^p.T (p.lev b))
          (((p.j b : ℝ)+1)/(2 : ℝ)^p.T (p.lev b)))) using 1
      ext z
      simp only [childCylinder,hl,hw,true_and,mem_ofPred_eq,mem_prod]
    · simpa only [childCylinder,hl,hw,true_and,false_and,ofPred_false] using MeasurableSet.empty
  · simpa only [childCylinder,hl,false_and,ofPred_false] using MeasurableSet.empty

theorem Native.PathData.Valid.childCylinder_disjoint (level : ℕ) (world : Fin W) :
    Pairwise (fun b b' => Disjoint (p.childCylinder level world b) (p.childCylinder level world b')) := by
  intro b b' hne
  apply disjoint_left.mpr
  rintro z ⟨hl,hw,hA,ht⟩ ⟨hl',hw',hA',ht'⟩
  have hlevel : p.lev b=p.lev b' := hl.trans hl'.symm
  have hworld : p.γ b=p.γ b' := hw.trans hw'.symm
  by_cases hj : p.j b=p.j b'
  · exact (disjoint_left.mp (hp.2.2.2.2.2.2.1 b b' hne hlevel hworld hj)) hA hA'
  · have hden : 0 < (2 : ℝ)^p.T (p.lev b') := by positivity
    rw [hlevel] at ht
    rcases lt_or_gt_of_ne hj with hlo | hhi
    · have hh : ((p.j b : ℝ)+1)/(2 : ℝ)^p.T (p.lev b') ≤
          (p.j b' : ℝ)/(2 : ℝ)^p.T (p.lev b') := by
        apply div_le_div_of_nonneg_right _ hden.le
        exact_mod_cast hlo
      linarith [ht.2,ht'.1]
    · have hh : ((p.j b' : ℝ)+1)/(2 : ℝ)^p.T (p.lev b') ≤
          (p.j b : ℝ)/(2 : ℝ)^p.T (p.lev b') := by
        apply div_le_div_of_nonneg_right _ hden.le
        exact_mod_cast hhi
      linarith [ht'.2,ht.1]

theorem Native.PathData.Valid.childLabel_measurable (level : ℕ) (world : Fin W) :
    Measurable (p.childLabel level world) :=
  Submission.Obl.k4_critical_conditional_row_preparation.measurable_coverLabel _
    (hp.childCylinder_measurable level world) (hp.childCylinder_disjoint level world)

theorem Native.PathData.Valid.childClockLabel_measurable (root : Fin p.C)
    (level : ℕ) (world : Fin W) : Measurable (p.childClockLabel root level world) :=
  (hp.childLabel_measurable level world).comp (p.childClockPoint_measurable root)

theorem Native.PathData.Valid.childLabel_eq_some (level : ℕ) (world : Fin W)
    (z : Ev) (b : Fin p.C) :
    p.childLabel level world z=some b ↔ z∈p.childCylinder level world b :=
  Submission.Obl.k4_critical_conditional_row_preparation.coverLabel_eq_some _
    (hp.childCylinder_disjoint level world) z b

/-- The endpoint cut makes every counted child's original time interior. -/
theorem Native.PathData.Valid.counted_time_interior (b : Fin p.C) {z : Ev}
    (hz : z∈p.F b) (haway : z∉p.levelEndpoints (p.lev b)) :
    z.2∈Ioo ((p.j b : ℝ)/(2 : ℝ)^p.T (p.lev b))
      (((p.j b : ℝ)+1)/(2 : ℝ)^p.T (p.lev b)) := by
  have ht := (hp.counted_subset_fullCylinder b hz).2
  refine ⟨lt_of_le_of_ne ht.1 ?_,lt_of_le_of_ne ht.2 ?_⟩
  · intro heq
    exact haway ⟨p.j b,heq.symm⟩
  · intro heq
    apply haway
    refine ⟨p.j b+1,?_⟩
    simpa only [Nat.cast_add,Nat.cast_one] using heq

/-- A true descendant's block, read in its actual root's time, is the
relative dyadic block of exponent T_child-T_root. -/
theorem Native.PathData.Valid.true_child_relative_block
    (root b : Fin p.C) (level : ℕ) (hb : b∈p.trueDescendants root level)
    {z : Ev} (hz : z∈p.F b) (haway : z∉p.levelEndpoints level) (t : ℝ) :
    packetTime p root (z.1,t)∈
      Qualification.Jets2.dyadicBlock (p.T level-p.T (p.lev root)) (packetTime p root z) ↔
      t∈Icc ((p.j b : ℝ)/(2 : ℝ)^p.T level) (((p.j b : ℝ)+1)/(2 : ℝ)^p.T level) := by
  classical
  obtain ⟨hl,hancestor⟩ := (Finset.mem_filter.mp hb).2
  have hCylinder : p.fullCylinder b⊆p.fullCylinder root := by
    simpa only [hancestor] using hp.iterate_par_fullCylinder (p.lev b-p.lev root) b (Nat.sub_le _ _)
  have hzA := (hp.counted_subset_fullCylinder b hz).1
  have hblocks :
      Submission.Obl.k4_contact_affine_residual_candidate_transfer.dyadicBlock (p.T level) (p.j b) ⊆
      Submission.Obl.k4_contact_affine_residual_candidate_transfer.dyadicBlock
        (p.T (p.lev root)) (p.j root) := by
    intro v hv
    exact (hCylinder (show (z.1,v)∈p.fullCylinder b from
      ⟨hzA,by simpa only [hl,
        Submission.Obl.k4_contact_affine_residual_candidate_transfer.dyadicBlock] using hv⟩)).2
  have hT := Submission.Obl.k4_contact_affine_residual_candidate_transfer.dyadic_exponent_le hblocks
  have hoff := Submission.Obl.k4_contact_affine_residual_candidate_transfer.dyadic_offset hblocks
  let offset := p.j b-p.j root*2^(p.T level-p.T (p.lev root))
  have hcast : (offset : ℝ)=(p.j b : ℝ)-(p.j root : ℝ)*(2 : ℝ)^(p.T level-p.T (p.lev root)) := by
    dsimp only [offset]
    rw [Nat.cast_sub hoff.1]
    push_cast
    rfl
  have hsplit : (2 : ℝ)^p.T level=(2 : ℝ)^p.T (p.lev root)*(2 : ℝ)^(p.T level-p.T (p.lev root)) := by
    rw [←pow_add,Nat.add_sub_cancel' hT]
  have ht := hp.counted_time_interior b hz (by simpa only [hl] using haway)
  rw [hl] at ht
  have hnorm : packetTime p root z∈Ioo
      ((offset : ℝ)/(2 : ℝ)^(p.T level-p.T (p.lev root)))
      (((offset : ℝ)+1)/(2 : ℝ)^(p.T level-p.T (p.lev root))) := by
    rw [packetTime_eq_dyadic]
    constructor
    · rw [div_lt_iff₀ (by positivity),hcast]
      have hh := (div_lt_iff₀ (by positivity : 0 < (2 : ℝ)^p.T level)).mp ht.1
      rw [hsplit] at hh
      nlinarith only [hh]
    · rw [lt_div_iff₀ (by positivity),hcast]
      have hh := (lt_div_iff₀ (by positivity : 0 < (2 : ℝ)^p.T level)).mp ht.2
      rw [hsplit] at hh
      nlinarith only [hh]
  have hread : Qualification.Jets2.dyadicBlock (p.T level-p.T (p.lev root)) (packetTime p root z)=
      Submission.Obl.k4_contact_affine_residual_candidate_transfer.dyadicBlock
        (p.T level-p.T (p.lev root)) offset := by
    exact Submission.Obl.k4_scalar_graph_residual_discovery.dyadicBlock_eq_timeBlock_of_interior
      _ ⟨offset,hoff.2⟩ hnorm
  rw [hread,packetTime_eq_dyadic]
  exact (Submission.Obl.k4_contact_affine_residual_candidate_transfer.dyadic_parent_time hblocks t).symm

/-- Every reference point has its actual true descendant as child label.
The source's full original mass is unchanged by the two null cuts. -/
theorem Native.PathData.Valid.childReference_spec
    (root : Fin p.C) (level : ℕ) (hlevel : p.lev root ≤ level) (hlast : level ≤ m-1)
    (source : Set Ev) (hsource : source⊆p.F root)
    (hterminal : ∀ z∈source, ∃ terminal : Fin p.C,
      p.lev terminal=m-1 ∧ p.γ terminal=p.γ root ∧ z∈p.F terminal)
    {z : Ev} (hz : z∈p.childReference root level source) :
    ∃ b : Fin p.C, b∈p.trueDescendants root level ∧
      p.childLabel level (p.γ root) z=some b ∧ z∈p.F b := by
  obtain ⟨b,hb,hzb⟩ := mem_iUnion₂.mp
    (hp.true_descendants_cover root level hlevel hlast source hsource hterminal hz.1)
  obtain ⟨hl,ha⟩ := (Finset.mem_filter.mp hb).2
  obtain ⟨-,hg,-⟩ := Broad.iterate_par_spec hp.toOriginal (p.lev b-p.lev root) b (Nat.sub_le _ _)
  change p.γ (p.par^[p.lev b-p.lev root] b)=p.γ b at hg
  have hw : p.γ b=p.γ root := by simpa only [ha] using hg.symm
  have ht := hp.counted_time_interior b hzb (by simpa only [hl] using hz.2)
  refine ⟨b,hb,(hp.childLabel_eq_some level _ z b).mpr ?_,hzb⟩
  exact ⟨hl,hw,(hp.counted_subset_fullCylinder b hzb).1,ht.1.le,ht.2⟩

/-- The true child label is constant on each same-line relative dyadic
block in the fixed reference, independently of all later source cuts. -/
theorem Native.PathData.Valid.childLabel_same_relative_block
    (root : Fin p.C) (level : ℕ) (hlevel : p.lev root ≤ level) (hlast : level ≤ m-1)
    (source : Set Ev) (hsource : source⊆p.F root)
    (hterminal : ∀ z∈source, ∃ terminal : Fin p.C,
      p.lev terminal=m-1 ∧ p.γ terminal=p.γ root ∧ z∈p.F terminal)
    {z : Ev} (hz : z∈p.childReference root level source) (t : ℝ)
    (htref : (z.1,t)∈p.childReference root level source)
    (htblock : packetTime p root (z.1,t)∈
      Qualification.Jets2.dyadicBlock (p.T level-p.T (p.lev root)) (packetTime p root z)) :
    p.childLabel level (p.γ root) (z.1,t)=p.childLabel level (p.γ root) z := by
  obtain ⟨b,hb,hlab,hzb⟩ := hp.childReference_spec root level hlevel hlast source hsource hterminal hz
  have hl := (Finset.mem_filter.mp hb).2.1
  have ht := (hp.true_child_relative_block root b level hb hzb hz.2 t).mp htblock
  have hne : t≠((p.j b : ℝ)+1)/(2 : ℝ)^p.T level := by
    intro heq
    apply htref.2
    refine ⟨p.j b+1,?_⟩
    simpa only [Nat.cast_add,Nat.cast_one] using heq
  rw [hlab]
  apply (hp.childLabel_eq_some level _ _ b).mpr
  have hzc := (hp.childLabel_eq_some level _ z b).mp hlab
  exact ⟨hl,hzc.2.1,hzc.2.2.1,by simpa only [hl] using
    (show t∈Ico ((p.j b : ℝ)/(2 : ℝ)^p.T level)
      (((p.j b : ℝ)+1)/(2 : ℝ)^p.T level) from ⟨ht.1,lt_of_le_of_ne ht.2 hne⟩)⟩

/-- Literal higher-jets label premise in the actual root-normalized clock. -/
theorem Native.PathData.Valid.childClockLabel_same_block
    (root : Fin p.C) (level : ℕ) (hlevel : p.lev root ≤ level) (hlast : level ≤ m-1)
    (source : Set Ev) (hsource : source⊆p.F root)
    (hterminal : ∀ z∈source, ∃ terminal : Fin p.C,
      p.lev terminal=m-1 ∧ p.γ terminal=p.γ root ∧ z∈p.F terminal) :
    ∀ z∈p.childClockReference root level source, ∀ t : ℝ,
      (z.1,t)∈p.childClockReference root level source →
      t∈Qualification.Jets2.dyadicBlock (p.T level-p.T (p.lev root)) z.2 →
      p.childClockLabel root level (p.γ root) (z.1,t)=p.childClockLabel root level (p.γ root) z := by
  intro z hz t ht hb
  have hh := hp.childLabel_same_relative_block root level hlevel hlast source hsource hterminal
    hz ((p.childClockPoint root (z.1,t)).2) ht
  apply hh
  change packetTime p root (p.childClockPoint root (z.1,t))∈
    Qualification.Jets2.dyadicBlock (p.T level-p.T (p.lev root))
      (packetTime p root (p.childClockPoint root z))
  simpa only [p.packetTime_childClockPoint] using hb

/-- Reading the clock reference returns the SAME actual child's counted
source. This applies to every later retained qualification world. -/
theorem Native.PathData.Valid.childClockReference_spec
    (root : Fin p.C) (level : ℕ) (hlevel : p.lev root ≤ level) (hlast : level ≤ m-1)
    (source : Set Ev) (hsource : source⊆p.F root)
    (hterminal : ∀ z∈source, ∃ terminal : Fin p.C,
      p.lev terminal=m-1 ∧ p.γ terminal=p.γ root ∧ z∈p.F terminal)
    {z : Ev} (hz : z∈p.childClockReference root level source) :
    ∃ b : Fin p.C, b∈p.trueDescendants root level ∧
      p.childClockLabel root level (p.γ root) z=some b ∧
      p.childClockPoint root z∈source∩p.F b := by
  obtain ⟨b,hb,hlab,hzb⟩ := hp.childReference_spec root level hlevel hlast source hsource hterminal hz
  exact ⟨b,hb,hlab,hz.1.1,hzb⟩

end Path
end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
