-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o234, session x0808, commit 93f941a4d95b2a652a5402772e0264d4924f12e4.
-- Source: Submission/Obl/k4_finite_positive_mixed_cover_realization/Path.lean.
import Submission.Obl.k4_finite_affine_parent_sources.Original
import Submission.Lib.K4XInterface
import Submission.Obl.k4_fixed_menu_density_pruning.ParentIncidences
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.FrozenBridge
import Submission.Obl.k4_coarsened_outer_horizon_composition.Finish

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Submission.Lib.K4XInterface
open Submission.Obl.k4_finite_forest_width_selection

/-- The original finite path data, without changing any label or assignment. -/
structure PathData (W : ℕ) where
  r : ℕ → ℝ
  T : ℕ → ℕ
  nw : ℕ → ℝ
  κ : ℝ
  C : ℕ
  lev : Fin C → ℕ
  par : Fin C → Fin C
  world : Fin C → Fin W
  bin : Fin C → ℕ
  center : Fin C → EuclideanSpace ℝ (Fin 2)
  velocity : Fin C → EuclideanSpace ℝ (Fin 2)
  frame : Fin C → Matrix (Fin 2) (Fin 2) ℝ
  test : Fin C → MvPolynomial (Fin 4) ℝ
  assigned : Fin C → Set Trajectory
  counted : Fin C → Set Incidence
  lists : ℕ → Fin W → Observation → Finset (Fin C)

/-- The path's exact frozen certificate. -/
def PathData.Valid {W : ℕ} (p : PathData W) (ℓ Nk L : ℝ)
    (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
    (E : Fin W → Set Incidence) (B : Fin W → ℝ) (f : ℝ → ℝ)
    (κ₁ : ℝ) (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ) (Mp Dp : ℕ) (σ : ℝ) : Prop :=
  PositivePath ℓ Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ
    p.r p.T p.nw p.κ p.C p.lev p.par p.world p.bin p.center p.velocity
    p.frame p.test p.assigned p.counted p.lists

/-- The list at a path level read off the unchanged original terminal observation. -/
noncomputable def PathData.terminalLists {W : ℕ} (p : PathData W)
    (Nk L : ℝ) (i : ℕ) (w : Fin W) (o : Observation) : Finset (Fin p.C) :=
  p.lists i w (coarsenObs (depthIdx Nk L - depthIdx Nk (p.r i)) o)

section PathFacts

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

lemma PathData.Valid.one_le_slack : 1 ≤ p.κ := hp.1
lemma PathData.Valid.slack_le : p.κ ≤ Nk ^ σ := hp.2.1
lemma PathData.Valid.count_le : (p.C : ℝ) ≤ Nk ^ Mp := hp.2.2.1
lemma PathData.Valid.last_depth : p.r (m - 1) = L := hp.2.2.2.1

lemma PathData.Valid.level_bounds (i : ℕ) (hi : i < m) :
    |p.r i - s i * L| ≤ δ₀ * L ∧ 0 < p.r i ∧
    Nk ^ ((κ₁ * s i - δ₀) * L) ≤ (2 : ℝ) ^ p.T i ∧
    (2 : ℝ) ^ p.T i ≤ Nk ^ ((κ₁ * s i + δ₀) * L) ∧
    |p.nw i - ℓ * s i * L| ≤ δ₀ * L ∧
    ENNReal.ofReal p.κ⁻¹ ≤ ∑ b, if p.lev b = i then
      ENNReal.ofReal (ω (p.world b)) * ((ν (p.world b)).prod volume) (p.counted b) else 0 :=
  hp.2.2.2.2.1 i hi

lemma PathData.Valid.list_bound (i : ℕ) (w : Fin W) (o : Observation) :
    ((p.lists i w o).card : ℝ) ≤ p.κ := hp.2.2.2.2.2.1 i w o

lemma PathData.Valid.assignment_disjoint (b b' : Fin p.C) (hne : b ≠ b')
    (hlev : p.lev b = p.lev b') (hw : p.world b = p.world b') (hj : p.bin b = p.bin b') :
    Disjoint (p.assigned b) (p.assigned b') := hp.2.2.2.2.2.2.1 b b' hne hlev hw hj

lemma PathData.Valid.label_level (b : Fin p.C) : p.lev b < m :=
  (hp.2.2.2.2.2.2.2 b).1

lemma PathData.Valid.label_bin (b : Fin p.C) : p.bin b < 2 ^ p.T (p.lev b) :=
  (hp.2.2.2.2.2.2.2 b).2.1

lemma PathData.Valid.chart (b : Fin p.C) :
    gchart Nk Mp Dp p.κ (p.T (p.lev b)) (p.bin b : ℝ) (p.r (p.lev b))
      (B (p.world b)) (E (p.world b)) (p.center b) (p.velocity b) (p.frame b)
      (p.test b) (p.assigned b) (p.counted b) True :=
  k4_coarsened_outer_horizon_composition.chart_extra_mono (fun _ => trivial)
    (hp.2.2.2.2.2.2.2 b).2.2

lemma PathData.Valid.saturation (b : Fin p.C) :
    ENNReal.ofReal (Nk ^ (-f (p.r (p.lev b))) * |(p.frame b).det| /
        ((2 : ℝ) ^ p.T (p.lev b) * p.κ)) ≤
      ((ν (p.world b)).prod volume) (p.counted b) ∧
    ν (p.world b) (p.assigned b) ≤ ENNReal.ofReal
      (p.κ * Nk ^ (-f (p.r (p.lev b))) * |(p.frame b).det|) := by
  have h := k4_native_calibrated_homogeneous_remainder.chart_extra
    (hp.2.2.2.2.2.2.2 b).2.2
  exact ⟨h.1, h.2.1⟩

lemma PathData.Valid.narrowness (b : Fin p.C) :
    Nk ^ (-(p.nw (p.lev b) + δ₀ * L)) ≤
      |(p.frame b).det| * (4 : ℝ) ^ p.T (p.lev b) ∧
    |(p.frame b).det| * (4 : ℝ) ^ p.T (p.lev b) ≤
      Nk ^ (-(p.nw (p.lev b) - δ₀ * L)) := by
  have h := k4_native_calibrated_homogeneous_remainder.chart_extra
    (hp.2.2.2.2.2.2.2 b).2.2
  exact ⟨h.2.2.1, h.2.2.2.1⟩

lemma PathData.Valid.known (b : Fin p.C) (z : Incidence) (hz : z ∈ p.counted b) :
    b ∈ p.lists (p.lev b) (p.world b)
      (gobs (B (p.world b)) (gδ Nk (p.r (p.lev b))) z) := by
  have h := k4_native_calibrated_homogeneous_remainder.chart_extra
    (hp.2.2.2.2.2.2.2 b).2.2
  exact h.2.2.2.2.1 z hz

lemma PathData.Valid.counted_support (b : Fin p.C) (z : Incidence)
    (hz : z ∈ p.counted b) :
    z ∈ E (p.world b) ∧ z.1 ∈ p.assigned b ∧
    z.2 ∈ Icc ((p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b))
      (((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)) ∧
    B (p.world b) / p.κ ≤ |MvPolynomial.eval (gx z.1 z.2)
      (MvPolynomial.pderiv (3 : Fin 4) (p.test b))| :=
  (hp.chart b).2.2.2.2.2.2.2.2.2.2.1 z hz

lemma PathData.Valid.terminal_list_bound (i : ℕ) (w : Fin W) (o : Observation) :
    ((p.terminalLists Nk L i w o).card : ℝ) ≤ p.κ :=
  hp.list_bound i w _

lemma PathData.Valid.terminal_known (hNk : 1 ≤ Nk) {b : Fin p.C} {i : ℕ}
    (hb : p.lev b = i) (hri : 0 ≤ p.r i) (hriL : p.r i ≤ L)
    {z : Incidence} (hz : z ∈ p.counted b) :
    b ∈ p.terminalLists Nk L i (p.world b)
      (gobs (B (p.world b)) (gδ Nk L) z) := by
  have h := hp.known b z hz
  rw [hb, gobs_coarsen hNk hri hriL] at h
  exact h

lemma PathData.Valid.parent (b : Fin p.C) (hb : 0 < p.lev b) :
    p.lev (p.par b) + 1 = p.lev b ∧ p.world (p.par b) = p.world b ∧
    p.assigned b ⊆ p.assigned (p.par b) ∧ p.counted b ⊆ p.counted (p.par b) ∧
    (p.bin (p.par b) : ℝ) / (2 : ℝ) ^ p.T (p.lev (p.par b)) ≤
      (p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b) ∧
    ((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b) ≤
      ((p.bin (p.par b) : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev (p.par b)) := by
  have h := k4_native_calibrated_homogeneous_remainder.chart_extra
    (hp.2.2.2.2.2.2.2 b).2.2
  exact h.2.2.2.2.2 hb

lemma PathData.Valid.ancestor (b : Fin p.C) (i : ℕ) (hi : i ≤ p.lev b) :
    p.lev (forestAncestor p.lev p.par b i) = i ∧
    p.world (forestAncestor p.lev p.par b i) = p.world b ∧
    p.counted b ⊆ p.counted (forestAncestor p.lev p.par b i) := by
  exact ⟨forestAncestor_level (fun b hb => (hp.parent b hb).1) b i hi,
    k4_fixed_menu_density_pruning.forestAncestor_incidence_subset
      p.lev p.par p.world p.counted (fun b hb => (hp.parent b hb).1)
      (fun b hb => (hp.parent b hb).2.1)
      (fun b hb => (hp.parent b hb).2.2.2.1) b i hi⟩

/-- On the interior of the old time block, the actual ancestor of a later
incidence is the old chart to which its trajectory was assigned. -/
lemma PathData.Valid.ancestor_eq_of_interior
    {b old : Fin p.C} {z : Incidence} (hi : p.lev old ≤ p.lev b)
    (hw : p.world b = p.world old) (hz : z ∈ p.counted b)
    (hzA : z.1 ∈ p.assigned old)
    (hzt : z.2 ∈ Ioo ((p.bin old : ℝ) / (2 : ℝ) ^ p.T (p.lev old))
      (((p.bin old : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev old))) :
    forestAncestor p.lev p.par b (p.lev old) = old := by
  let a := forestAncestor p.lev p.par b (p.lev old)
  obtain ⟨ha, haw, hsub⟩ := hp.ancestor b (p.lev old) hi
  have hza : z ∈ p.counted a := hsub hz
  have hsup := hp.counted_support a z hza
  have hzat := hsup.2.2.1
  rw [ha] at hzat
  have haj : p.bin old = p.bin a :=
    k4_fixed_menu_density_pruning.time_cell_unique (by positivity) hzt hzat
  by_contra hne
  exact Set.disjoint_left.mp
    (hp.assignment_disjoint a old hne ha (haw.trans hw) haj.symm) hsup.2.1 hzA

end PathFacts

end Submission.Obl.k4_finite_affine_parent_sources
