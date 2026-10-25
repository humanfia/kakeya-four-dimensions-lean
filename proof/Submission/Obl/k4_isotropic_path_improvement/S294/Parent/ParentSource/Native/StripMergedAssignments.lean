-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripMergedAssignments, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripMergedAssignments.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripMergedAssignments.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripMergedAssignments.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripMergedAssignments.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripMergedCells

/-! Whole-block trajectory assignments using merged parameter bins. Their
mass partition is exact under every original law. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MeasureTheory
open Submission.Lib.K4VelocityStrips
open scoped RealInnerProductSpace BigOperators

def mergedStripAssignment {X : Type*} {m : ℕ} (A : Set X) (V M : X → StripSpace)
    (r : ℝ) (n : Fin m → StripSpace) (β : Fin m → ℝ) (w : ℝ)
    (q : StripCodeLabel r n β) (z : ℤ) : Set X :=
  (A ∩ V ⁻¹' mergedStripCell r n β w q) ∩
    {x | ⌊inner ℝ (M x) (n (canonicalStripIndex r n β q)) / r⌋ = z}

theorem measurableSet_mergedStripAssignment {X : Type*} [MeasurableSpace X] {m : ℕ}
    (A : Set X) (V M : X → StripSpace) (r : ℝ)
    (n : Fin m → StripSpace) (β : Fin m → ℝ) (w : ℝ)
    (q : StripCodeLabel r n β) (z : ℤ) (hA : MeasurableSet A)
    (hV : Measurable V) (hM : Measurable M) :
    MeasurableSet (mergedStripAssignment A V M r n β w q z) := by
  exact (hA.inter ((measurableSet_mergedStripCell r n β w q).preimage hV)).inter
    (measurableSet_eq_fun (by fun_prop) measurable_const)

theorem mergedStripAssignment_disjoint {X : Type*} {m : ℕ}
    (A : Set X) (V M : X → StripSpace) (r : ℝ)
    (n : Fin m → StripSpace) (β : Fin m → ℝ) (w : ℝ)
    {q q' : StripCodeLabel r n β} {z z' : ℤ} (hne : (q, z) ≠ (q', z')) :
    Disjoint (mergedStripAssignment A V M r n β w q z)
      (mergedStripAssignment A V M r n β w q' z') := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  by_cases hq : q = q'
  · subst q'
    exact hne (Prod.ext rfl (hx.2.symm.trans hy.2))
  · exact Set.disjoint_left.mp (mergedStripCell_disjoint r n β w hq) hx.1.2 hy.1.2

theorem iUnion_mergedStripAssignment {X : Type*} {m Z : ℕ}
    (A : Set X) (V M : X → StripSpace) {r : ℝ}
    (n : Fin m → StripSpace) (β : Fin m → ℝ) (w : ℝ)
    (hr : 0 < r) (hn : ∀ i, ‖n i‖ = 1)
    (hM : ∀ x ∈ A, ‖M x‖ ≤ (Z : ℝ) * r) :
    (⋃ a : StripCodeLabel r n β × {z : ℤ // z ∈ stripBinRange Z},
      mergedStripAssignment A V M r n β w a.1 a.2) =
      A ∩ V ⁻¹' (⋃ i, affineStrip (n i) (β i) w) := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
    refine ⟨ha.1.1, ?_⟩
    rw [← iUnion_mergedStripCell r n β w]
    exact Set.mem_iUnion.mpr ⟨a.1, ha.1.2⟩
  · intro hx
    have hcells : V x ∈ ⋃ q, mergedStripCell r n β w q := by
      rw [iUnion_mergedStripCell]
      exact hx.2
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hcells
    let z := ⌊inner ℝ (M x) (n (canonicalStripIndex r n β q)) / r⌋
    have hz : z ∈ stripBinRange Z :=
      floor_inner_mem_stripBinRange hr (hn _) (hM x hx.1)
    exact Set.mem_iUnion.mpr ⟨(q, ⟨z, hz⟩), ⟨⟨hx.1, hq⟩, rfl⟩⟩

theorem sum_mergedStripAssignment_measure {X : Type*} [MeasurableSpace X] {m Z : ℕ}
    (μ : Measure X) (A : Set X) (V M : X → StripSpace) {r : ℝ}
    (n : Fin m → StripSpace) (β : Fin m → ℝ) (w : ℝ)
    (hr : 0 < r) (hn : ∀ i, ‖n i‖ = 1) (hA : MeasurableSet A)
    (hV : Measurable V) (hM : Measurable M)
    (hbound : ∀ x ∈ A, ‖M x‖ ≤ (Z : ℝ) * r) :
    (∑ a : StripCodeLabel r n β × {z : ℤ // z ∈ stripBinRange Z},
      μ (mergedStripAssignment A V M r n β w a.1 a.2)) =
      μ (A ∩ V ⁻¹' (⋃ i, affineStrip (n i) (β i) w)) := by
  classical
  rw [← iUnion_mergedStripAssignment A V M n β w hr hn hbound]
  rw [measure_iUnion]
  · exact (tsum_fintype _).symm
  · intro a b hab
    apply mergedStripAssignment_disjoint A V M r n β w
    intro h
    apply hab
    exact Prod.ext (congrArg (fun q : StripCodeLabel r n β × ℤ => q.1) h)
      (Subtype.ext (congrArg (fun q : StripCodeLabel r n β × ℤ => q.2) h))
  · intro a
    exact measurableSet_mergedStripAssignment A V M r n β w a.1 a.2 hA hV hM

/-- Merging adds only a parameter-bin diameter to the normal velocity
error. The selected frame still contains every whole assigned trajectory. -/
theorem mergedStripAssignment_whole_block_fit {X : Type*} {m : ℕ}
    {A : Set X} {a V : X → StripSpace} {n e : Fin m → StripSpace} {β : Fin m → ℝ}
    {K D r w T : ℝ} (hK : 0 < K) (hD : 0 ≤ D) (hr : 0 < r) (hT : 0 ≤ T)
    (he : ∀ i, ‖e i‖ = 1) (hn : ∀ i, ‖n i‖ = 1) (hen : ∀ i, inner ℝ (e i) (n i) = 0)
    (hV : ∀ x ∈ A, ‖V x‖ ≤ T) (hwidth : w + 3 * (1 + T) * r ≤ D * r)
    (hfit : ∀ x ∈ A, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖a x + t • V x‖ ≤ K)
    {x : X} {q : StripCodeLabel r n β} {z : ℤ}
    (hx : x ∈ mergedStripAssignment A V (fun x => a x + (1 / 2 : ℝ) • V x)
      r n β w q z) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖Matrix.toEuclideanLin
      (stripLocalFrame K D r (e (canonicalStripIndex r n β q))
        (n (canonicalStripIndex r n β q)))⁻¹
      (a x + t • V x - stripCenter (n (canonicalStripIndex r n β q)) ((z : ℝ) * r)
        (β (canonicalStripIndex r n β q)) -
        t • stripVelocity (n (canonicalStripIndex r n β q))
          (β (canonicalStripIndex r n β q)))‖ ≤ 2 := by
  apply strip_whole_block_fit hK hD hr (he _) (hn _) (hen _) (hfit x hx.1.1)
    ((mergedStripCell_velocity_bound hr hT (hV x hx.1.1) hx.1.2).trans hwidth) _ ht
  have h := midpoint_floor_center_bound hr
    (inner ℝ (a x + (1 / 2 : ℝ) • V x) (n (canonicalStripIndex r n β q)))
  rw [hx.2] at h
  exact h

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
