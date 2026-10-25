-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceGood

/-!
# The depth map of a source stage

Model depth `x` is sent to the deepest grid level whose nominal depth is at most
`s i₀ + u * clamp x`. The map is monotone, never goes above the parent level and its actual
depth increment differs from `u L x` by at most one mesh and two supplied depth errors.

Adapted from this LOT tree, o199, session x0831 (refs/merged/o199/x0831,
Submission/Obl/k4_finite_path_candidate_conversion/GridLabels.lean): the same monotone
rounding to nominal grid levels, rewritten over `ℕ`-indexed grids by x0891 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set

noncomputable section

/-- The deepest grid level with nominal depth at most `x` (or `0`). -/
def gridDepth (m : ℕ) (s : ℕ → ℝ) (x : ℝ) : ℕ :=
  ((Finset.range m).filter (fun i => s i ≤ x)).sup id

theorem gridDepth_lt {m : ℕ} (hm : 0 < m) (s : ℕ → ℝ) (x : ℝ) : gridDepth m s x < m := by
  unfold gridDepth
  rcases Finset.eq_empty_or_nonempty ((Finset.range m).filter (fun i => s i ≤ x)) with h | h
  · rw [h, Finset.sup_empty]; exact hm
  · obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup _ h id
    rw [hsup]
    exact Finset.mem_range.mp (Finset.mem_filter.mp hi).1

theorem le_gridDepth {m : ℕ} {s : ℕ → ℝ} {x : ℝ} {i : ℕ} (hi : i < m) (hs : s i ≤ x) :
    i ≤ gridDepth m s x :=
  Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hs⟩)

theorem gridDepth_le_target {m : ℕ} {s : ℕ → ℝ} {x : ℝ} {i : ℕ} (hi : i < m) (hs : s i ≤ x) :
    s (gridDepth m s x) ≤ x := by
  unfold gridDepth
  have hne : ((Finset.range m).filter (fun i => s i ≤ x)).Nonempty :=
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hs⟩⟩
  obtain ⟨j, hj, hsup⟩ := Finset.exists_mem_eq_sup _ hne id
  rw [hsup]
  exact (Finset.mem_filter.mp hj).2

theorem gridDepth_mono (m : ℕ) (s : ℕ → ℝ) : Monotone (gridDepth m s) := by
  intro x y hxy
  apply Finset.sup_mono
  intro i hi
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨h1, h2.trans hxy⟩

/-- The target is at most one mesh above the chosen nominal depth. -/
theorem target_le_gridDepth {m : ℕ} {s : ℕ → ℝ} {x mesh : ℝ} (hmesh0 : 0 ≤ mesh)
    (hmesh : ∀ i, i + 1 < m → s (i + 1) - s i ≤ mesh) (hm : 0 < m)
    (hlast : x ≤ s (m - 1)) :
    x ≤ s (gridDepth m s x) + mesh := by
  set g := gridDepth m s x
  have hg : g < m := gridDepth_lt hm s x
  by_cases hnext : g + 1 < m
  · have hlt : x < s (g + 1) := by
      by_contra hn
      push Not at hn
      have := le_gridDepth hnext hn
      omega
    have := hmesh g hnext
    linarith
  · have hgm : g = m - 1 := by omega
    rw [hgm]
    linarith

/-- The source depth map: model depth `x` goes to the grid level below `s i₀ + u * clamp x`. -/
def sourceDepth (m : ℕ) (s : ℕ → ℝ) (i₀ : ℕ) (u : ℝ) (x : ℝ) : ℕ :=
  gridDepth m s (s i₀ + u * max 0 (min x 1))

theorem sourceDepth_mono (m : ℕ) (s : ℕ → ℝ) (i₀ : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    Monotone (sourceDepth m s i₀ u) := by
  intro x y hxy
  apply gridDepth_mono
  have : max 0 (min x 1) ≤ max 0 (min y 1) := max_le_max le_rfl (min_le_min hxy le_rfl)
  nlinarith

theorem sourceDepth_ge {m : ℕ} (s : ℕ → ℝ) {i₀ : ℕ} (hi₀ : i₀ < m) {u : ℝ} (hu : 0 ≤ u)
    (x : ℝ) : i₀ ≤ sourceDepth m s i₀ u x := by
  apply le_gridDepth hi₀
  have : 0 ≤ max 0 (min x 1) := le_max_left _ _
  nlinarith

theorem sourceDepth_lt {m : ℕ} (hm : 0 < m) (s : ℕ → ℝ) (i₀ : ℕ) (u x : ℝ) :
    sourceDepth m s i₀ u x < m := gridDepth_lt hm s _

/-- Nominal error of the source depth map on `[0, 1]`. -/
theorem sourceDepth_nominal {m : ℕ} (hm : 0 < m) {s : ℕ → ℝ} {i₀ : ℕ} (hi₀ : i₀ < m)
    {u mesh : ℝ} (hu : 0 ≤ u) (hmesh0 : 0 ≤ mesh)
    (hmesh : ∀ i, i + 1 < m → s (i + 1) - s i ≤ mesh) (hroom : s i₀ + u ≤ s (m - 1))
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    s (sourceDepth m s i₀ u x) ≤ s i₀ + u * x ∧
      s i₀ + u * x ≤ s (sourceDepth m s i₀ u x) + mesh := by
  have hcl : max 0 (min x 1) = x := by
    rw [min_eq_left hx1, max_eq_right hx0]
  unfold sourceDepth
  rw [hcl]
  have htarget : s i₀ ≤ s i₀ + u * x := by nlinarith
  refine ⟨gridDepth_le_target hi₀ htarget, target_le_gridDepth hmesh0 hmesh hm ?_⟩
  nlinarith

section Path

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- **Actual depth error of the source depth map.** -/
theorem sourceDepth_actual (hm : 0 < m) {i₀ : ℕ} (hi₀ : i₀ < m) {u mesh : ℝ} (hu : 0 ≤ u)
    (hmesh0 : 0 ≤ mesh) (hmesh : ∀ i, i + 1 < m → sg (i + 1) - sg i ≤ mesh)
    (hroom : sg i₀ + u ≤ sg (m - 1)) (hL : 0 ≤ L) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |p.r (sourceDepth m sg i₀ u x) - p.r i₀ - u * L * x| ≤ (mesh + 2 * δ₀) * L ∧
      p.r (sourceDepth m sg i₀ u x) ≤ (sg i₀ + u + δ₀) * L := by
  obtain ⟨hlo, hhi⟩ := sourceDepth_nominal hm hi₀ hu hmesh0 hmesh hroom hx0 hx1
  set j := sourceDepth m sg i₀ u x
  have hj : j < m := sourceDepth_lt hm sg i₀ u x
  have hrj := (hp.level_bounds j hj).1
  have hri := (hp.level_bounds i₀ hi₀).1
  rw [abs_le] at hrj hri
  have h1 := mul_le_mul_of_nonneg_right hlo hL
  have h2 := mul_le_mul_of_nonneg_right hhi hL
  have hux : u * x ≤ u := by nlinarith
  have h3 := mul_le_mul_of_nonneg_right hux hL
  have h4 : mesh * L ≥ 0 := mul_nonneg hmesh0 hL
  constructor
  · rw [abs_le]
    constructor <;> nlinarith
  · nlinarith

end Path

end

end Submission.Obl.k4_finite_affine_parent_sources
