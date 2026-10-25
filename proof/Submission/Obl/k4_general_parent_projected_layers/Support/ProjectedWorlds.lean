/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/ProjectedWorlds.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.MeshProjection
import Submission.Obl.k4_quadratic_atlas_normalization.AssignmentMass
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Finite disjoint coefficient groups on the original trajectory prior. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open MeasureTheory Set

noncomputable section

def projectedWorldTag (chi g : ℝ) (b : Fin 6 → ℝ) : Fin 4 → ℤ :=
  ![⌊b 3 / chi⌋, ⌊b 0 / chi⌋, ⌊b 1 / g⌋, ⌊b 4 / g⌋]

theorem measurable_projectedWorldTag (chi g : ℝ) : Measurable (projectedWorldTag chi g) := by
  unfold projectedWorldTag
  fun_prop

def projectedWorldCrop {α : Type*} (C : Set α) (b : α → Fin 6 → ℝ)
    (chi g : ℝ) (q : Fin 4 → ℤ) : Set α :=
  C ∩ {l | projectedWorldTag chi g (b l) = q}

theorem measurableSet_projectedWorldCrop {α : Type*} [MeasurableSpace α]
    {C : Set α} (hC : MeasurableSet C) (b : α → Fin 6 → ℝ) (hb : Measurable b)
    (chi g : ℝ) (q : Fin 4 → ℤ) : MeasurableSet (projectedWorldCrop C b chi g q) := by
  exact hC.inter (measurableSet_eq_fun ((measurable_projectedWorldTag chi g).comp hb) measurable_const)

theorem projectedWorldCrop_disjoint {α : Type*} (C : Set α) (b : α → Fin 6 → ℝ)
    (chi g : ℝ) {q q' : Fin 4 → ℤ} (hne : q ≠ q') :
    Disjoint (projectedWorldCrop C b chi g q) (projectedWorldCrop C b chi g q') := by
  apply disjoint_left.mpr
  intro l hl hl'
  exact hne (hl.2.symm.trans hl'.2)

theorem finite_projected_worlds {α : Type*} (C : Set α) (b : α → Fin 6 → ℝ)
    {K chi g : ℝ} (hK : 0 ≤ K) (hc : 0 < chi) (hg : 0 < g)
    (hbound : ∀ l ∈ C, |b l 0| + |b l 1| + |b l 3| + |b l 4| ≤ K) :
    ∃ F : Finset (Fin 4 → ℤ),
      (F.card : ℝ) ≤ (4 * K / chi + 2) ^ 2 * (4 * K / g + 2) ^ 2 ∧
      ∀ l ∈ C, projectedWorldTag chi g (b l) ∈ F := by
  classical
  obtain ⟨Fc, hFc, hccover⟩ := interval_mesh_cover hc hK 0
  obtain ⟨Fg, hFg, hgcover⟩ := interval_mesh_cover hg hK 0
  let Q : Fin 4 → Finset ℤ := ![Fc, Fc, Fg, Fg]
  let F := Fintype.piFinset Q
  refine ⟨F, ?_, ?_⟩
  · have hcard : (F.card : ℝ) = (Fc.card : ℝ) ^ 2 * (Fg.card : ℝ) ^ 2 := by
      simp [F, Fintype.card_piFinset, Q, Fin.prod_univ_succ] <;> ring
    rw [hcard]
    exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hFc 2)
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hFg 2) (sq_nonneg _) (sq_nonneg _)
  · intro l hl
    have h := hbound l hl
    have h0 : |b l 0| ≤ K := by linarith [abs_nonneg (b l 1), abs_nonneg (b l 3), abs_nonneg (b l 4)]
    have h1 : |b l 1| ≤ K := by linarith [abs_nonneg (b l 0), abs_nonneg (b l 3), abs_nonneg (b l 4)]
    have h3 : |b l 3| ≤ K := by linarith [abs_nonneg (b l 0), abs_nonneg (b l 1), abs_nonneg (b l 4)]
    have h4 : |b l 4| ≤ K := by linarith [abs_nonneg (b l 0), abs_nonneg (b l 1), abs_nonneg (b l 3)]
    apply Fintype.mem_piFinset.mpr
    intro i
    fin_cases i
    · exact hccover _ (by simpa only [sub_zero] using h3)
    · exact hccover _ (by simpa only [sub_zero] using h0)
    · exact hgcover _ (by simpa only [sub_zero] using h1)
    · exact hgcover _ (by simpa only [sub_zero] using h4)

theorem sum_projected_crop_prior_le_one {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] {C : Set α} (hC : MeasurableSet C)
    (b : α → Fin 6 → ℝ) (hb : Measurable b) (chi g : ℝ) (F : Finset (Fin 4 → ℤ)) :
    ∑ q : F, ν (projectedWorldCrop C b chi g q) ≤ 1 := by
  classical
  have h := Submission.Obl.k4_quadratic_atlas_normalization.sum_measure_assignment_fiber_le
    ν (fun _q : F => ()) (fun q : F => projectedWorldCrop C b chi g q) ()
    (fun q => measurableSet_projectedWorldCrop hC b hb chi g q)
    (fun q q' hne _ => projectedWorldCrop_disjoint C b chi g
      (fun heq => hne (Subtype.ext heq)))
  simpa using h

end

end Submission.Obl.k4_general_parent_projected_layers
