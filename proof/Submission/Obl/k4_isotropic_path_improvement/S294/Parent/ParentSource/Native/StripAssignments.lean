-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripAssignments, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripAssignments.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripAssignments.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripAssignments.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripAssignments.lean.
   Original comments and attributions are preserved below. -/
import Submission.Lib.K4VelocityStrips
import Submission.Lib.K4FinitePlankAtlases.Assignments

/-! Whole-trajectory priority assignments for narrow velocity strips.
This is a finite partition under the original law, with no posterior denominator. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MeasureTheory
open Submission.Lib.K4VelocityStrips
open scoped RealInnerProductSpace BigOperators

def stripBinRange (Z : ℕ) : Finset ℤ := Finset.Icc (-(Z : ℤ)) Z

theorem stripBinRange_card (Z : ℕ) : (stripBinRange Z).card = 2 * Z + 1 := by
  rw [stripBinRange, Int.card_Icc]
  have hid : (Z : ℤ) + 1 - -(Z : ℤ) = (2 * Z + 1 : ℕ) := by omega
  rw [hid, Int.toNat_natCast]

theorem floor_inner_mem_stripBinRange {r : ℝ} {Z : ℕ} {Y n : StripSpace}
    (hr : 0 < r) (hn : ‖n‖ = 1) (hY : ‖Y‖ ≤ (Z : ℝ) * r) :
    ⌊inner ℝ Y n / r⌋ ∈ stripBinRange Z := by
  have hinner : |inner ℝ Y n| ≤ (Z : ℝ) * r := by
    exact (abs_real_inner_le_norm _ _).trans (by simpa only [hn, mul_one] using hY)
  have hquot : |inner ℝ Y n / r| ≤ (Z : ℝ) := by
    rwa [abs_div, abs_of_pos hr, div_le_iff₀ hr]
  have hlo : ((-(Z : ℤ)) : ℝ) ≤ inner ℝ Y n / r := by
    simpa using (abs_le.mp hquot).1
  have hhi : inner ℝ Y n / r ≤ (Z : ℝ) := (abs_le.mp hquot).2
  have hhi' := Int.floor_mono hhi
  rw [stripBinRange, Finset.mem_Icc]
  constructor
  · apply Int.le_floor.mpr
    simpa only [Int.cast_neg] using hlo
  · simpa using hhi'

/-- The strip representative is chosen by velocity alone. The midpoint bin is
then a trajectory label, constant over the entire parent time block. -/
def stripAssignment {X : Type*} {m : ℕ} (A : Set X) (V M : X → StripSpace)
    (n : Fin m → StripSpace) (β : Fin m → ℝ) (w r : ℝ) (i : Fin m) (z : ℤ) : Set X :=
  (A ∩ V ⁻¹' Submission.Lib.K4FinitePlankAtlases.firstAssignment
    (fun j => affineStrip (n j) (β j) w) i) ∩
      {x | ⌊inner ℝ (M x) (n i) / r⌋ = z}

theorem measurableSet_stripAssignment {X : Type*} [MeasurableSpace X] {m : ℕ}
    (A : Set X) (V M : X → StripSpace) (n : Fin m → StripSpace) (β : Fin m → ℝ)
    (w r : ℝ) (i : Fin m) (z : ℤ) (hA : MeasurableSet A)
    (hV : Measurable V) (hM : Measurable M) :
    MeasurableSet (stripAssignment A V M n β w r i z) := by
  apply MeasurableSet.inter
  · exact hA.inter ((Submission.Lib.K4FinitePlankAtlases.measurableSet_firstAssignment _
      (fun j => measurableSet_affineStrip _ _ _) i).preimage hV)
  · exact measurableSet_eq_fun (by fun_prop) measurable_const

theorem stripAssignment_disjoint {X : Type*} {m : ℕ}
    (A : Set X) (V M : X → StripSpace) (n : Fin m → StripSpace) (β : Fin m → ℝ)
    (w r : ℝ) {i j : Fin m} {z z' : ℤ} (hne : (i, z) ≠ (j, z')) :
    Disjoint (stripAssignment A V M n β w r i z)
      (stripAssignment A V M n β w r j z') := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  by_cases hij : i = j
  · subst j
    exact hne (Prod.ext rfl (hx.2.symm.trans hy.2))
  · exact Set.disjoint_left.mp
      (Submission.Lib.K4FinitePlankAtlases.firstAssignment_disjoint
        (fun j => affineStrip (n j) (β j) w) hij) hx.1.2 hy.1.2

/-- The finite trajectory partition covers exactly the part of the parent
assignment whose velocity lies in one of the selected strips. -/
theorem iUnion_stripAssignment {X : Type*} {m Z : ℕ}
    (A : Set X) (V M : X → StripSpace) (n : Fin m → StripSpace) (β : Fin m → ℝ)
    {w r : ℝ} (hr : 0 < r) (hn : ∀ i, ‖n i‖ = 1)
    (hM : ∀ x ∈ A, ‖M x‖ ≤ (Z : ℝ) * r) :
    (⋃ q : Fin m × {z : ℤ // z ∈ stripBinRange Z},
      stripAssignment A V M n β w r q.1 q.2) =
      A ∩ V ⁻¹' (⋃ i, affineStrip (n i) (β i) w) := by
  ext x
  constructor
  · intro hx
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx
    exact ⟨hq.1.1, Set.mem_iUnion.mpr ⟨q.1, hq.1.2.1⟩⟩
  · intro hx
    have hfirst : V x ∈ ⋃ i, Submission.Lib.K4FinitePlankAtlases.firstAssignment
        (fun j => affineStrip (n j) (β j) w) i := by
      rw [Submission.Lib.K4FinitePlankAtlases.iUnion_firstAssignment]
      exact hx.2
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hfirst
    let z := ⌊inner ℝ (M x) (n i) / r⌋
    have hz : z ∈ stripBinRange Z := floor_inner_mem_stripBinRange hr (hn i) (hM x hx.1)
    exact Set.mem_iUnion.mpr ⟨(i, ⟨z, hz⟩), ⟨⟨hx.1, hi⟩, rfl⟩⟩

/-- The priority partition keeps its entire original mass, before any later
incidence selection or encoding. -/
theorem sum_stripAssignment_measure {X : Type*} [MeasurableSpace X] {m Z : ℕ}
    (μ : Measure X) (A : Set X) (V M : X → StripSpace)
    (n : Fin m → StripSpace) (β : Fin m → ℝ) {w r : ℝ}
    (hr : 0 < r) (hn : ∀ i, ‖n i‖ = 1) (hA : MeasurableSet A)
    (hV : Measurable V) (hM : Measurable M)
    (hbound : ∀ x ∈ A, ‖M x‖ ≤ (Z : ℝ) * r) :
    (∑ q : Fin m × {z : ℤ // z ∈ stripBinRange Z},
      μ (stripAssignment A V M n β w r q.1 q.2)) =
      μ (A ∩ V ⁻¹' (⋃ i, affineStrip (n i) (β i) w)) := by
  classical
  rw [← iUnion_stripAssignment A V M n β hr hn hbound]
  rw [measure_iUnion]
  · exact (tsum_fintype _).symm
  · intro i j hij
    apply stripAssignment_disjoint A V M n β w r
    intro h
    apply hij
    exact Prod.ext (congrArg (fun q : Fin m × ℤ => q.1) h)
      (Subtype.ext (congrArg (fun q : Fin m × ℤ => q.2) h))
  · intro q
    exact measurableSet_stripAssignment A V M n β w r q.1 q.2 hA hV hM

/-- Every assigned trajectory obeys the narrower frame on the entire block;
the center parameter is the actual midpoint floor bin. -/
theorem stripAssignment_whole_block_fit {X : Type*} {m : ℕ}
    {A : Set X} {a V : X → StripSpace} {n e : Fin m → StripSpace} {β : Fin m → ℝ}
    {K D r : ℝ} (hK : 0 < K) (hD : 0 ≤ D) (hr : 0 < r)
    (he : ∀ i, ‖e i‖ = 1) (hn : ∀ i, ‖n i‖ = 1) (hen : ∀ i, inner ℝ (e i) (n i) = 0)
    (hfit : ∀ x ∈ A, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖a x + t • V x‖ ≤ K)
    {x : X} {i : Fin m} {z : ℤ}
    (hx : x ∈ stripAssignment A V (fun x => a x + (1 / 2 : ℝ) • V x)
      n β (D * r) r i z) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖Matrix.toEuclideanLin (stripLocalFrame K D r (e i) (n i))⁻¹
      (a x + t • V x - stripCenter (n i) ((z : ℝ) * r) (β i) -
        t • stripVelocity (n i) (β i))‖ ≤ 2 := by
  apply strip_whole_block_fit hK hD hr (he i) (hn i) (hen i) (hfit x hx.1.1)
    hx.1.2.1 _ ht
  have h := midpoint_floor_center_bound hr (inner ℝ (a x + (1 / 2 : ℝ) • V x) (n i))
  rw [hx.2] at h
  exact h

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
