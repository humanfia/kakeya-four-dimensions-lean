-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.Jets2.CoarseGeometry, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/Jets2/CoarseGeometry.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit 2f02dabfaa4891833d78772b63f6d98e404e9c6c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/Jets2/CoarseGeometry.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2.VelocityGeometry
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.VisitedCells

/-! # Coarse cells visited by a coefficient trajectory

Only derivatives control the number of cells. Signal and spatial
intercepts remain arbitrary.
-/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
open MeasureTheory Set SourceGeometry Broad.Velocity
noncomputable section

theorem coefficient_signal_lipschitz {H : ℝ} (hH : 0≤H) {c : Fin 7 → ℝ}
    (h1 : |c 1|≤H) (h2 : |c 2|≤H) {s t : ℝ}
    (hs : s∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
    |zx c s-zx c t|≤3*H*|s-t| := by
  have hsum : |s+t|≤2 := by
    rw [abs_of_nonneg (add_nonneg hs.1 ht.1)]
    linarith only [hs.2,ht.2]
  have hrate : |c 1+c 2*(s+t)|≤3*H := by
    calc
      _ ≤ |c 1|+|c 2*(s+t)| := abs_add_le _ _
      _ = |c 1| + |c 2| * |s+t| := by rw [abs_mul]
      _ ≤ H+H*2 := by gcongr
      _ = _ := by ring
  rw [show zx c s-zx c t=(s-t)*(c 1+c 2*(s+t)) by dsimp [zx]; ring,abs_mul]
  exact (mul_le_mul_of_nonneg_left hrate (abs_nonneg _)).trans_eq (by ring)

theorem coefficient_coordinate_lipschitz {H : ℝ} (hH : 1≤H) {c : Fin 7 → ℝ}
    (h1 : |c 1|≤H) (h2 : |c 2|≤H) (h4 : |c 4|≤H) (h6 : |c 6|≤H)
    {s t : ℝ} (hs : s∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) (j : Fin 4) :
    |coefficientPhysical c s j-coefficientPhysical c t j|≤3*H*|s-t| := by
  have hH0 : 0≤H := zero_le_one.trans hH
  have hbase (a b : ℝ) (hb : |b|≤H) :
      |(a+b*s)-(a+b*t)|≤3*H*|s-t| := by
    rw [show (a+b*s)-(a+b*t)=b*(s-t) by ring,abs_mul]
    exact (mul_le_mul_of_nonneg_right hb (abs_nonneg _)).trans
      (by nlinarith [abs_nonneg (s-t)])
  fin_cases j
  · change |s-t|≤3*H*|s-t|
    nlinarith [abs_nonneg (s-t)]
  · exact hbase (c 3) (c 4) h4
  · exact hbase (c 5) (c 6) h6
  · exact coefficient_signal_lipschitz hH0 h1 h2 hs ht

def coefficientGridCode {Λ : Type*} (c : Λ → Fin 7 → ℝ)
    (baseMesh hidden : ℝ) (z : Λ×ℝ) : Fin 4 → ℤ :=
  fun j => ⌊coefficientPhysical (c z.1) z.2 j/(if j=3 then hidden else baseMesh)⌋

theorem measurable_coefficientGridCode {Λ : Type*} [MeasurableSpace Λ]
    {c : Λ → Fin 7 → ℝ} (hc : Measurable c) (baseMesh hidden : ℝ) :
    Measurable (coefficientGridCode c baseMesh hidden) := by
  apply measurable_pi_iff.mpr
  intro j
  exact Int.measurable_floor.comp
    (((PiLp.continuous_apply 2 _ j).measurable.comp
      (measurable_coefficientPhysical hc)).div_const _)

/-- A single trajectory visits only order `1/q` coarse cells, regardless
of its absolute spatial position or constant signal coefficient. -/
theorem exists_coefficient_curve_cell_menu {H q : ℝ} (hH : 1≤H) (hq : 0<q)
    (c : Fin 7 → ℝ) (h1 : |c 1|≤H) (h2 : |c 2|≤H)
    (h4 : |c 4|≤H) (h6 : |c 6|≤H) :
    ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ)≤(2/q+3)*(6*H+5)^4 ∧
      ∀ label, label∈S ↔ ∃ t∈Icc (0:ℝ) 1,
        (fun j => (⌊coefficientPhysical c t j/q⌋ : ℤ))=label := by
  classical
  have hzero : (0:ℝ)∈Icc (0:ℝ) 1 := by norm_num
  have hspan (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (j : Fin 4) :
      |coefficientPhysical c t j-coefficientPhysical c 0 j|≤3*H := by
    have ht1 : |t-0|≤1 := by simpa only [sub_zero,abs_of_nonneg ht.1] using ht.2
    exact (coefficient_coordinate_lipschitz hH h1 h2 h4 h6 ht hzero j).trans
      ((mul_le_mul_of_nonneg_left ht1 (by positivity)).trans_eq (mul_one _))
  obtain ⟨S,hS⟩ := exists_curve_cell_table (fun t j => coefficientPhysical c t j)
    hq (by positivity : 0≤3*H) hspan
  let witness (label : Fin 4 → ℤ) : ℝ :=
    if h : label∈S then ((hS label).mp h).choose else 0
  have hw (label : Fin 4 → ℤ) (hl : label∈S) :
      witness label∈Icc (0:ℝ) 1 ∧
      (fun j => (⌊coefficientPhysical c (witness label) j/q⌋ : ℤ))=label := by
    simpa only [witness,dif_pos hl] using ((hS label).mp hl).choose_spec
  refine ⟨S,?_,hS⟩
  have hh := trajectory_cell_count (fun t j => coefficientPhysical c t j) S witness
    (3*H) q (by positivity) hq
    (fun s hs t ht j => coefficient_coordinate_lipschitz hH h1 h2 h4 h6 hs ht j)
    (fun label hl => (hw label hl).1) (fun label hl j => congrFun (hw label hl).2 j)
  simpa only [Fintype.card_fin,show 2*(3*H)+5=6*H+5 by ring] using hh

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
