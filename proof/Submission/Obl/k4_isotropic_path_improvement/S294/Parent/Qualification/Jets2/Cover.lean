-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.Jets2.Cover, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/Jets2/Cover.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/Jets2/Cover.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/Jets2/Cover.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Basic

set_option autoImplicit false

/-!
# Covering scalar strips of `ℝ³ = (x, y)` by cubes (version 2)

The three-dimensional replacement of `Jets/Parallelogram.lean` of o229 (session x0801, branch
`x0801` at `b03d2c4a`), which covers a planar strip `{x - f y ∈ [s₀, s₀ + q)}` by squares.

* `col_cover`: in a `y`-box `∏ [b i, b i + q)`, the strip `{x - f · y ∈ [s₀, s₀ + q)}` with
  `‖f‖ ≤ K` lies in the `⌊4K + 1⌋₊ + 1` cubes `[colA + i q, colA + i q + q) × box`;
* `box_cover`: a sup-ball of radius `L` in `ℝ²` lies in `(⌊2L/q⌋₊ + 1)²` boxes of side `q`;
* `slab_cover`: a slab `{|e · y - y₀| ≤ L}` with `e k = 1`, `|e k'| ≤ 1` (`k'` the other index),
  inside `|y k'| ≤ B`, lies in `(⌊2B/q⌋₊ + 1) (⌊(2L + 2q)/q⌋₊ + 1)` boxes of side `q`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set

noncomputable section

/-- Column offset of the cube cover of a strip over the `y`-box with corner `b`. -/
def colA (s₀ : ℝ) (f b : Fin 2 → ℝ) (q : ℝ) : ℝ := s₀ + f ⬝ᵥ b - (|f 0| + |f 1|) * q

theorem col_cover {q s₀ K x : ℝ} {f y b : Fin 2 → ℝ} (hq : 0 < q) (hf : ‖f‖ ≤ K)
    (hs1 : s₀ ≤ x - f ⬝ᵥ y) (hs2 : x - f ⬝ᵥ y < s₀ + q) (hy : ∀ i, y i ∈ Ico (b i) (b i + q)) :
    ∃ i < ⌊4 * K + 1⌋₊ + 1, x ∈ Ico (colA s₀ f b q + i * q) (colA s₀ f b q + i * q + q) := by
  have hdiff : ∀ i, |f i * (y i - b i)| ≤ |f i| * q := by
    intro i
    obtain ⟨h1, h2⟩ := hy i
    rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ y i - b i)]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have hfy : f ⬝ᵥ y - f ⬝ᵥ b = f 0 * (y 0 - b 0) + f 1 * (y 1 - b 1) := by
    rw [dot_two, dot_two]; ring
  have h0 := hdiff 0
  have h1 := hdiff 1
  have hf0 : |f 0| ≤ K := (abs_le_norm f 0).trans hf
  have hf1 : |f 1| ≤ K := (abs_le_norm f 1).trans hf
  rw [abs_le] at h0 h1
  refine exists_bin hq ?_ ?_
  · simp only [colA]; nlinarith
  · simp only [colA]; nlinarith

/-- Each coordinate of a point of a sup-ball lies in one of `⌊2L/q⌋₊ + 1` bins. -/
theorem box_cover {q L : ℝ} {y y₀ : Fin 2 → ℝ} (hq : 0 < q) (hy : ∀ i, |y i - y₀ i| ≤ L) :
    ∃ j : Fin 2 → ℕ, (∀ i, j i < ⌊2 * L / q⌋₊ + 1) ∧
      ∀ i, y i ∈ Ico (y₀ i - L + j i * q) (y₀ i - L + j i * q + q) := by
  have h : ∀ i, ∃ j : ℕ, j < ⌊2 * L / q⌋₊ + 1 ∧
      y i ∈ Ico (y₀ i - L + j * q) (y₀ i - L + j * q + q) := by
    intro i
    have := hy i
    rw [abs_le] at this
    exact exists_bin hq (by linarith) (by rw [mul_div_cancel₀ _ hq.ne']; linarith)
  choose j hj hmem using h
  exact ⟨j, hj, hmem⟩

/-- The lower end of the `k`-coordinate range of a slab over the `k'`-bin with corner `b'`. -/
def slabLo (y₀ L q e' b' : ℝ) : ℝ := y₀ - L - e' * b' - q

/-- The box corner of a slab cover. -/
def slabCorner (k : Fin 2) (bk bk' : ℝ) : Fin 2 → ℝ := fun i => if i = k then bk else bk'

theorem slab_cover {q L B y₀ : ℝ} {e y : Fin 2 → ℝ} {k : Fin 2} (hq : 0 < q)
    (hek : e k = 1) (he' : |e (Fin.rev k)| ≤ 1) (hB : |y (Fin.rev k)| ≤ B)
    (hy : |e ⬝ᵥ y - y₀| ≤ L) :
    ∃ j' < ⌊2 * B / q⌋₊ + 1, ∃ j < ⌊(2 * L + 2 * q) / q⌋₊ + 1,
      ∀ i, y i ∈ Ico (slabCorner k
          (slabLo y₀ L q (e (Fin.rev k)) (-B + j' * q) + j * q) (-B + j' * q) i)
        (slabCorner k
          (slabLo y₀ L q (e (Fin.rev k)) (-B + j' * q) + j * q) (-B + j' * q) i + q) := by
  rw [abs_le] at hB hy
  obtain ⟨j', hj', hmem'⟩ := exists_bin (a := -B) (x := y (Fin.rev k)) (B := 2 * B / q) hq
    (by linarith) (by rw [mul_div_cancel₀ _ hq.ne']; linarith)
  set b' : ℝ := -B + j' * q
  have hd0 : 0 ≤ y (Fin.rev k) - b' := by linarith [hmem'.1]
  have hd1 : y (Fin.rev k) - b' < q := by linarith [hmem'.2]
  have hsplit := dot_split e y k
  rw [hek, one_mul] at hsplit
  have hed : |e (Fin.rev k) * (y (Fin.rev k) - b')| ≤ q := by
    rw [abs_mul, abs_of_nonneg hd0]
    calc |e (Fin.rev k)| * (y (Fin.rev k) - b') ≤ 1 * q :=
          mul_le_mul he' hd1.le hd0 zero_le_one
      _ = q := one_mul q
  rw [abs_le] at hed
  obtain ⟨j, hj, hmem⟩ := exists_bin (a := slabLo y₀ L q (e (Fin.rev k)) b') (x := y k)
    (B := (2 * L + 2 * q) / q) hq
    (by simp only [slabLo]; nlinarith)
    (by rw [mul_div_cancel₀ _ hq.ne']; simp only [slabLo]; nlinarith)
  refine ⟨j', hj', j, hj, fun i => ?_⟩
  rcases fin_two_eq k i with hi | hi
  · rw [hi]; simp only [slabCorner, ↓reduceIte]; exact hmem
  · rw [hi]; simp only [slabCorner, rev_ne k, ↓reduceIte]; exact hmem'

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
