/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, FullWitness.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.FrozenSupportInputs
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.ScalarSupportBasics
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.AffineEntries
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.NativeNormalization

/-! Adapted from this LOT tree, obligation o107, session x0734,
`Submission/Obl/k4_finite_narrowness_path_improvement/HorizontalRowGeometry.lean` and
`Submission/Obl/k4_finite_narrowness_path_improvement/HorizontalOriginalWitness.lean`
(commit e9d85a5f34). -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

theorem timeLength_pos (cfg : Data α) (k : ℕ) (s : ℝ) : 0 < cfg.timeLength k s := by
  unfold timeLength
  positivity

theorem timeLength_le_one (cfg : Data α) (k : ℕ) (s : ℝ) : cfg.timeLength k s ≤ 1 := by
  unfold timeLength
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

theorem mem_time_block_unit (T : ℕ) (j : Fin (2 ^ T)) {t : ℝ} (ht : t ∈ I T j) :
    t ∈ Set.Icc (0 : ℝ) 1 :=
  Submission.Obl.k4_scalar_initial_true_horizon.I_subset_unit T j ht

def blockMidpoint (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) : ℝ :=
  (((cfg.j k s i : ℕ) : ℝ) + 1 / 2) * cfg.timeLength k s

/-- The frozen tilted box has the critical H² transverse width on its
entire original trajectory assignment. -/
theorem AssignmentLevel.whole_horizontal_box (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s))
    (l : α) (hl : l ∈ cfg.A k s i) (t : ℝ)
    (ht : t ∈ I (cfg.T k s) (cfg.j k s i)) :
    ![t, (cfg.x k l t) 1, (cfg.x k l t) 2] ∈
      horizontalTrueBox (cfg.c k s i) (cfg.blockMidpoint k s i)
        (cfg.timeLength k s) (cfg.K k ^ 2) := by
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hK0 : 0 ≤ cfg.K k := by linarith
  have hK2 : cfg.K k ≤ cfg.K k ^ 2 := by nlinarith
  have hH : 0 ≤ cfg.timeLength k s := (cfg.timeLength_pos k s).le
  have hg : cfg.N k ^ (-cfg.ℓ * s) ≤ cfg.K k * cfg.timeLength k s := by
    rw [h.horizontal_rate]
    exact (time_length_comparison (by linarith [h.scale k]) (by linarith)
      a.time_lower a.time_upper).2
  have hgeom := a.geometry i l hl t ht
  have ht' : (((cfg.j k s i : ℕ) : ℝ) * cfg.timeLength k s) ≤ t ∧
      t ≤ (((cfg.j k s i : ℕ) : ℝ) + 1) * cfg.timeLength k s := by
    simpa only [I, timeLength, div_eq_mul_inv, Set.mem_Icc] using ht
  change |t - cfg.blockMidpoint k s i| ≤ cfg.timeLength k s / 2 ∧
    |(cfg.x k l t) 1 - cfg.c k s i 0 - t * cfg.c k s i 1| ≤
      cfg.K k ^ 2 * cfg.timeLength k s ∧
    |(cfg.x k l t) 2 - cfg.c k s i 2 - t * cfg.c k s i 3 -
      cfg.c k s i 4 * (cfg.x k l t) 1| ≤ cfg.K k ^ 2 * cfg.timeLength k s ^ 2
  refine ⟨?_, hgeom.1.trans (mul_le_mul_of_nonneg_right hK2 hH), ?_⟩
  · unfold blockMidpoint
    exact abs_le.mpr ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
  · exact hgeom.2.1.trans ((mul_le_mul_of_nonneg_left hg (by positivity)).trans_eq (by ring))

def FullLabelMassFloors (cfg : Data α) (k : ℕ) (s : ℝ) : Prop :=
  ∀ i : Fin (cfg.n k s), MeasurableSet (cfg.B k s i) ∧
    ENNReal.ofReal (cfg.timeLength k s ^ 4 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 3) ≤
      cfg.μ k (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i))

def originalWitness (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) : Set (α × ℝ) :=
  (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)) ∩
    {p | |(cfg.x k p.1 p.2) 3| ≤ cfg.K k}

theorem measurable_originalWitness (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (floors : cfg.FullLabelMassFloors k s) (i : Fin (cfg.n k s)) :
    MeasurableSet (cfg.originalWitness k s i) := by
  have hb := (h.basic k).1
  exact ((floors i).1.prod measurableSet_Icc).inter
    (measurableSet_le (by dsimp [x]; fun_prop) measurable_const)

/-- Only a null hidden-value tail is removed from each original witness. -/
theorem AssignmentLevel.originalWitness_mass (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) :
    cfg.μ k (cfg.originalWitness k s i) =
      cfg.μ k (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)) := by
  apply measure_congr
  filter_upwards [a.native_hidden_bounds h i] with p hp
  apply propext
  constructor
  · exact fun hh => hh.1
  · intro hh
    refine ⟨hh, ?_⟩
    simpa [x] using hp.2.2 p.2 (mem_time_block_unit _ _ hh.2)

theorem AssignmentLevel.originalWitness_floor (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (floors : cfg.FullLabelMassFloors k s)
    (i : Fin (cfg.n k s)) :
    ENNReal.ofReal (cfg.timeLength k s ^ 4 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 3) ≤
      cfg.μ k (cfg.originalWitness k s i) := by
  rw [a.originalWitness_mass h i]
  exact (floors i).2

theorem AssignmentLevel.originalWitness_nonempty (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (floors : cfg.FullLabelMassFloors k s)
    (i : Fin (cfg.n k s)) : (cfg.originalWitness k s i).Nonempty := by
  have hH := cfg.timeLength_pos k s
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 0 < cfg.K k := by linarith [h.subpower.1 k]
  have hpos : 0 < ENNReal.ofReal
      (cfg.timeLength k s ^ 4 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 3) := by
    exact ENNReal.ofReal_pos.mpr (by positivity)
  exact nonempty_of_measure_ne_zero (hpos.trans_le (a.originalWitness_floor h floors i)).ne'

/-- All fitted original trajectories retain their full true affine entry. -/
theorem AssignmentLevel.exists_affine_table (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (floors : cfg.FullLabelMassFloors k s) (hs : 0 ≤ s) :
    ∃ L : Fin (cfg.n k s) → Fin 4 → ℝ,
      (∀ i, ∀ e : Fin 3, |L i e.succ| ≤ 8 * cfg.K k ^ 4) ∧
      ∀ i l, l ∈ cfg.B k s i → ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
        |(cfg.x k l t) 3 - affineBaseEval (L i)
          ![t, (cfg.x k l t) 1, (cfg.x k l t) 2]| ≤ cfg.K k * cfg.N k ^ (-s) := by
  have hentry : ∀ i : Fin (cfg.n k s), ∃ L : Fin 4 → ℝ,
      (∀ e : Fin 3, |L e.succ| ≤ 8 * cfg.K k ^ 4) ∧
      ∀ l ∈ cfg.B k s i, ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
        |(cfg.x k l t) 3 - affineBaseEval L
          ![t, (cfg.x k l t) 1, (cfg.x k l t) 2]| ≤ cfg.K k * cfg.N k ^ (-s) := by
    intro i
    obtain ⟨p, hp⟩ := a.originalWitness_nonempty h floors i
    obtain ⟨L, _, hL, hfit⟩ := a.active_affine_entry h hs i p.1 hp.1.1 p.2 hp.1.2
    refine ⟨L, hL, ?_⟩
    intro l hl t ht
    convert hfit l hl t ht using 1 <;>
      dsimp [x, affineBaseEval, affineResidualIntercept, affineResidualSlope] <;> congr 1 <;> ring
  choose L hL hfit using hentry
  exact ⟨L, hL, hfit⟩

theorem AssignmentLevel.originalWitness_disjoint {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i i' : Fin (cfg.n k s))
    (hne : i ≠ i') (hj : cfg.j k s i = cfg.j k s i') :
    Disjoint (cfg.originalWitness k s i) (cfg.originalWitness k s i') := by
  apply Set.disjoint_left.mpr
  intro p hp hp'
  exact Set.disjoint_left.mp (a.disjoint i i' hne hj)
    (a.fitted_subset i hp.1.1) (a.fitted_subset i' hp'.1.1)

theorem blockMidpoint_bound (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) :
    |cfg.blockMidpoint k s i| ≤ 1 := by
  have hH := cfg.timeLength_pos k s
  have heq : cfg.blockMidpoint k s i = cfg.leftTime k s i + cfg.timeLength k s / 2 := by
    dsimp [blockMidpoint, leftTime, timeLength]
    ring
  have hm : cfg.blockMidpoint k s i ∈ I (cfg.T k s) (cfg.j k s i) := by
    rw [cfg.true_block_eq, heq]
    exact ⟨by linarith, by linarith⟩
  have hu := mem_time_block_unit _ _ hm
  rw [abs_of_nonneg hu.1]
  exact hu.2

end Data

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
