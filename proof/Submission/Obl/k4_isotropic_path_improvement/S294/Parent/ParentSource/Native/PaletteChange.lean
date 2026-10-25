-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.PaletteChange, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/PaletteChange.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/PaletteChange.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/PaletteChange.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/PaletteChange.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.VelocityPalette

/-! Ambiguity of the normalized velocity palette given an original bin.
Only the normalized inverse frame bound enters the count. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped BigOperators

theorem velocityPalette_norm_sub_le {a : ℝ} (ha : 0 < a)
    {z z' : EuclideanSpace ℝ (Fin 2)}
    (h : velocityPalette a z = velocityPalette a z') : ‖z - z'‖ ≤ 2 * a := by
  have hcoord (j : Fin 2) : |z j - z' j| ≤ a := by
    have hfloor : ⌊z j / a⌋ = ⌊z' j / a⌋ := by
      fin_cases j
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h
    have hlt := Int.abs_sub_lt_one_of_floor_eq_floor hfloor
    rw [← sub_div, abs_div, abs_of_pos ha, div_lt_one ha] at hlt
    exact hlt.le
  calc
    _ ≤ ∑ j, |(z - z') j| := euclidean_norm_le_sum_abs _
    _ ≤ ∑ _ : Fin 2, a := Finset.sum_le_sum (fun j _ => hcoord j)
    _ = 2 * a := by simp

/-- A diameter estimate, rather than an absolute-coordinate envelope, bounds
the palette size. Absolute position is used only to prove finiteness. -/
theorem velocityPalette_card_of_diameter {Ω : Type*} (S : Set Ω) (hSne : S.Nonempty)
    (V : Ω → EuclideanSpace ℝ (Fin 2)) {a D : ℝ} (ha : 0 < a) (hD : 0 ≤ D)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖V x - V y‖ ≤ D * a) :
    ((fun x => velocityPalette a (V x)) '' S).Finite ∧
      (((fun x => velocityPalette a (V x)) '' S).ncard : ℝ) ≤ (2 * D + 6) ^ 2 := by
  classical
  obtain ⟨x₀, hx₀⟩ := hSne
  have hbound : ∀ x ∈ S, ∀ j, |V x j| ≤ D * a + ‖V x₀‖ := by
    intro x hx j
    have hcoord : |V x j| ≤ ‖V x‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (V x) j
    have hnorm : ‖V x‖ ≤ ‖V x - V x₀‖ + ‖V x₀‖ := by
      calc
        _ = ‖(V x - V x₀) + V x₀‖ := by congr 1; module
        _ ≤ _ := norm_add_le _ _
    exact hcoord.trans (hnorm.trans (add_le_add (hdiam x hx x₀ hx₀) le_rfl))
  obtain ⟨_, _, hfin, _, _⟩ := velocityPalette_card S ⟨x₀, hx₀⟩ (fun x => (V x : Fin 2 → ℝ))
    (K := D * a + ‖V x₀‖) (by positivity) ha hbound
  let P := hfin.toFinset
  have hpdiam : ∀ p ∈ P, ∀ p' ∈ P,
      |(p.1 : ℝ) - p'.1| ≤ D + 2 ∧ |(p.2 : ℝ) - p'.2| ≤ D + 2 := by
    intro p hp p' hp'
    obtain ⟨x, hx, rfl⟩ := hfin.mem_toFinset.mp hp
    obtain ⟨y, hy, rfl⟩ := hfin.mem_toFinset.mp hp'
    have hcoord (j : Fin 2) : |(⌊V x j / a⌋ : ℝ) - ⌊V y j / a⌋| ≤ D + 2 := by
      have hcoordnorm : |V x j - V y j| ≤ ‖V x - V y‖ := by
        simpa only [Real.norm_eq_abs, PiLp.sub_apply] using PiLp.norm_apply_le (V x - V y) j
      have hn : |V x j - V y j| ≤ D * a := hcoordnorm.trans (hdiam x hx y hy)
      have hd : |V x j / a - V y j / a| ≤ D := by
        rw [← sub_div, abs_div, abs_of_pos ha, div_le_iff₀ ha]
        exact hn
      exact (Submission.Obl.k4_finite_row_graph_assembly.abs_sub_floor_le _ _).trans
        (by linarith)
    exact ⟨hcoord 0, hcoord 1⟩
  have hc := Submission.Obl.k4_finite_row_graph_assembly.card_pair_grid_of_diameter P
    (R := D + 2) (by positivity) hpdiam
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  simpa only [P, show 2 * (D + 2) + 2 = 2 * D + 6 by ring] using hc

/-- One original velocity bin leaves only polynomially many bins after the
parent's affine velocity change, regardless of its translation or format. -/
theorem affine_velocity_palette_card_mesh {Ω : Type*} (S : Set Ω) (hSne : S.Nonempty)
    (V : Ω → EuclideanSpace ℝ (Fin 2)) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (shift : EuclideanSpace ℝ (Fin 2)) {q a b D : ℝ}
    (hq : 0 ≤ q) (ha : 0 < a) (hb : 0 < b) (hD : 0 ≤ D)
    (hmesh : (q * (∑ i, ∑ j, |M i j|)) * a ≤ D * b)
    (hbin : ∀ x ∈ S, ∀ y ∈ S, velocityPalette a (V x) = velocityPalette a (V y)) :
    ((fun x => velocityPalette b (q • Matrix.toEuclideanLin M (V x - shift))) '' S).Finite ∧
      (((fun x => velocityPalette b (q • Matrix.toEuclideanLin M (V x - shift))) '' S).ncard : ℝ) ≤
        (4 * D + 6) ^ 2 := by
  have hdiam : ∀ x ∈ S, ∀ y ∈ S,
      ‖q • Matrix.toEuclideanLin M (V x - shift) -
        q • Matrix.toEuclideanLin M (V y - shift)‖ ≤ (2 * D) * b := by
    intro x hx y hy
    have hid : q • Matrix.toEuclideanLin M (V x - shift) -
        q • Matrix.toEuclideanLin M (V y - shift) = q • Matrix.toEuclideanLin M (V x - V y) := by
      rw [← smul_sub, ← map_sub]
      congr 2
      module
    rw [hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq]
    calc
      _ ≤ q * ((∑ i, ∑ j, |M i j|) * ‖V x - V y‖) :=
        mul_le_mul_of_nonneg_left (matrix_action_norm_le_entry_sum M _) hq
      _ = (q * (∑ i, ∑ j, |M i j|)) * ‖V x - V y‖ := by ring
      _ ≤ (q * (∑ i, ∑ j, |M i j|)) * (2 * a) :=
        mul_le_mul le_rfl (velocityPalette_norm_sub_le ha (hbin x hx y hy))
          (norm_nonneg _) (by positivity)
      _ = 2 * ((q * (∑ i, ∑ j, |M i j|)) * a) := by ring
      _ ≤ 2 * (D * b) := mul_le_mul_of_nonneg_left hmesh (by norm_num)
      _ = (2 * D) * b := by ring
  have hc := velocityPalette_card_of_diameter S hSne _ hb
    (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hD) hdiam
  simpa only [WithLp.ofLp_smul, show 2 * (2 * D) + 6 = 4 * D + 6 by ring] using hc

/-- The simpler common-width estimate follows by discarding the mesh ratio. -/
theorem affine_velocity_palette_card {Ω : Type*} (S : Set Ω) (hSne : S.Nonempty)
    (V : Ω → EuclideanSpace ℝ (Fin 2)) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (shift : EuclideanSpace ℝ (Fin 2)) {q a b D : ℝ}
    (hq : 0 ≤ q) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (hD : 0 ≤ D)
    (hframe : q * (∑ i, ∑ j, |M i j|) ≤ D)
    (hbin : ∀ x ∈ S, ∀ y ∈ S, velocityPalette a (V x) = velocityPalette a (V y)) :
    ((fun x => velocityPalette b (q • Matrix.toEuclideanLin M (V x - shift))) '' S).Finite ∧
      (((fun x => velocityPalette b (q • Matrix.toEuclideanLin M (V x - shift))) '' S).ncard : ℝ) ≤
        (4 * D + 6) ^ 2 := by
  apply affine_velocity_palette_card_mesh S hSne V M shift hq ha hb hD _ hbin
  exact (mul_le_mul_of_nonneg_right hframe ha.le).trans
    (mul_le_mul_of_nonneg_left hab hD)

/-- The exact isotropic path supplies the required ambiguity bound with no
dependence on `Mp` or `Dp`. The source bin may be finer than the target bin. -/
theorem PathData.Valid.normalized_velocity_palette_card {W : ℕ} {p : PathData W}
    {Nk L : ℝ} {ω : Fin W → ℝ} {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {f : ℝ → ℝ}
    {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hNk : 1 ≤ Nk)
    (b : Fin p.C) (S : Set (ℕ × (Fin 6 → ℝ))) (hSne : S.Nonempty)
    {a₀ a₁ : ℝ} (ha₀ : 0 < a₀) (ha₁ : 0 < a₁) (haa : a₀ ≤ a₁)
    (hbin : ∀ x ∈ S, ∀ y ∈ S, velocityPalette a₀ (v x) = velocityPalette a₀ (v y)) :
    ((fun l => velocityPalette a₁ (((2 : ℝ) ^ p.T (p.lev b))⁻¹ •
      Matrix.toEuclideanLin (p.Q b)⁻¹ (v l - p.u b))) '' S).Finite ∧
    (((fun l => velocityPalette a₁ (((2 : ℝ) ^ p.T (p.lev b))⁻¹ •
      Matrix.toEuclideanLin (p.Q b)⁻¹ (v l - p.u b))) '' S).ncard : ℝ) ≤
        (4 * (p.κ * Nk ^ (2 * δ₀ * L)) + 6) ^ 2 := by
  have hκ : 0 ≤ p.κ := le_trans (by norm_num) h.1
  exact affine_velocity_palette_card S hSne v (p.Q b)⁻¹ (p.u b)
    (by positivity) ha₀ ha₁ haa (mul_nonneg hκ (Real.rpow_nonneg (by linarith) _))
    (h.normalized_inverse_bound hNk b) hbin

/-- Keeping the actual mesh ratio removes the fixed `delta0` exponent from
palette ambiguity. The source mesh pays the inverse-frame distortion. -/
theorem PathData.Valid.normalized_velocity_palette_card_mesh {W : ℕ} {p : PathData W}
    {Nk L : ℝ} {ω : Fin W → ℝ} {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {f : ℝ → ℝ}
    {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hNk : 1 ≤ Nk)
    (b : Fin p.C) (S : Set (ℕ × (Fin 6 → ℝ))) (hSne : S.Nonempty)
    {a₀ a₁ : ℝ} (ha₀ : 0 < a₀) (ha₁ : 0 < a₁)
    (hmesh : a₀ * Nk ^ (2 * δ₀ * L) ≤ a₁)
    (hbin : ∀ x ∈ S, ∀ y ∈ S, velocityPalette a₀ (v x) = velocityPalette a₀ (v y)) :
    ((fun l => velocityPalette a₁ (((2 : ℝ) ^ p.T (p.lev b))⁻¹ •
      Matrix.toEuclideanLin (p.Q b)⁻¹ (v l - p.u b))) '' S).Finite ∧
    (((fun l => velocityPalette a₁ (((2 : ℝ) ^ p.T (p.lev b))⁻¹ •
      Matrix.toEuclideanLin (p.Q b)⁻¹ (v l - p.u b))) '' S).ncard : ℝ) ≤
        (4 * p.κ + 6) ^ 2 := by
  have hκ : 0 ≤ p.κ := le_trans (by norm_num) h.1
  apply affine_velocity_palette_card_mesh S hSne v (p.Q b)⁻¹ (p.u b)
    (by positivity) ha₀ ha₁ hκ _ hbin
  calc
    _ ≤ (p.κ * Nk ^ (2 * δ₀ * L)) * a₀ :=
      mul_le_mul_of_nonneg_right (h.normalized_inverse_bound hNk b) ha₀.le
    _ = p.κ * (a₀ * Nk ^ (2 * δ₀ * L)) := by ring
    _ ≤ p.κ * a₁ := mul_le_mul_of_nonneg_left hmesh hκ

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
