-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.BallCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/BallCaps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/BallCaps.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/BallCaps.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/BallCaps.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PaletteChange

/-! Original angular-bin ceilings imply small-ball ceilings for the parent's
normalized velocity, using only the forward frame bound. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

theorem finite_palette_mass_le {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (z : Ω → I) (S : Set Ω) (hfin : (z '' S).Finite)
    (c : ENNReal) (hcap : ∀ i, μ {x | z x = i} ≤ c) :
    μ S ≤ ((z '' S).ncard : ENNReal) * c := by
  classical
  let P := hfin.toFinset
  have hsub : S ⊆ ⋃ i ∈ P, {x | z x = i} := by
    intro x hx
    exact mem_iUnion.mpr ⟨z x, mem_iUnion.mpr ⟨hfin.mem_toFinset.mpr ⟨x, hx, rfl⟩, rfl⟩⟩
  calc
    _ ≤ μ (⋃ i ∈ P, {x | z x = i}) := measure_mono hsub
    _ ≤ ∑ i ∈ P, μ {x | z x = i} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ P, c := Finset.sum_le_sum (fun i _ => hcap i)
    _ = _ := by rw [Set.ncard_eq_toFinset_card _ hfin]; simp [P]

/-- Any set with physical velocity diameter at most two original bin widths
meets at most one hundred bins. -/
theorem velocity_small_set_mass_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (V : Ω → EuclideanSpace ℝ (Fin 2)) (S : Set Ω)
    {a : ℝ} (ha : 0 < a) (c : ENNReal)
    (hcap : ∀ i, μ {x | velocityPalette a (V x) = i} ≤ c)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖V x - V y‖ ≤ 2 * a) :
    μ S ≤ 100 * c := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨hfin, hc⟩ := velocityPalette_card_of_diameter S hS V ha (by norm_num) hdiam
    have hc' : (((fun x => velocityPalette a (V x)) '' S).ncard : ENNReal) ≤ 100 := by
      have hn : (((fun x => velocityPalette a (V x)) '' S).ncard : ℝ) ≤ 100 := by norm_num at hc ⊢; exact hc
      exact_mod_cast hn
    exact (finite_palette_mass_le μ (fun x => velocityPalette a (V x)) S hfin c hcap).trans
      (mul_le_mul hc' le_rfl zero_le zero_le)
  · rw [Set.not_nonempty_iff_eq_empty.mp hS, measure_empty]
    exact zero_le

/-- A forward Lipschitz bound transfers original bin caps to normalized
velocity balls, without any absolute bound on their centers. -/
theorem normalized_velocity_ball_mass_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (V U : Ω → EuclideanSpace ℝ (Fin 2))
    {a r D : ℝ} (ha : 0 < a) (hD : 0 ≤ D) (hscale : D * r ≤ a)
    (hframe : ∀ x y, ‖V x - V y‖ ≤ D * ‖U x - U y‖)
    (c : ENNReal) (hcap : ∀ i, μ {x | velocityPalette a (V x) = i} ≤ c)
    (center : EuclideanSpace ℝ (Fin 2)) :
    μ {x | ‖U x - center‖ ≤ r} ≤ 100 * c := by
  apply velocity_small_set_mass_le μ V _ ha c hcap
  intro x hx y hy
  have hd : ‖U x - U y‖ ≤ 2 * r := by
    calc
      _ = ‖(U x - center) + (center - U y)‖ := by congr 1; module
      _ ≤ ‖U x - center‖ + ‖center - U y‖ := norm_add_le _ _
      _ = ‖U x - center‖ + ‖U y - center‖ := by rw [norm_sub_rev center (U y)]
      _ ≤ r + r := add_le_add hx hy
      _ = _ := by ring
  exact (hframe x y).trans ((mul_le_mul_of_nonneg_left hd hD).trans (by nlinarith))

/-- The normalized inverse-frame velocity map has forward distortion at most
`κ` when the old frame satisfies its original entry-sum bound. -/
theorem normalized_frame_forward_lipschitz (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (shift : EuclideanSpace ℝ (Fin 2)) {q κ : ℝ} (hq : 0 < q)
    (hQ : Q.det ≠ 0) (hsize : (∑ i, ∑ j, |Q i j|) ≤ κ * q)
    (V V' : EuclideanSpace ℝ (Fin 2)) :
    ‖V - V'‖ ≤ κ * ‖q • Matrix.toEuclideanLin Q⁻¹ (V - shift) -
      q • Matrix.toEuclideanLin Q⁻¹ (V' - shift)‖ := by
  let n := q • Matrix.toEuclideanLin Q⁻¹ (V - shift) -
    q • Matrix.toEuclideanLin Q⁻¹ (V' - shift)
  have hid (e : EuclideanSpace ℝ (Fin 2)) :
      Matrix.toEuclideanLin Q (Matrix.toEuclideanLin Q⁻¹ e) = e := by
    have hm := congrArg (fun L => L e) (Matrix.toLpLin_mul 2 2 2 Q Q⁻¹)
    rw [Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ), Matrix.toLpLin_one] at hm
    exact hm.symm
  have hn : Matrix.toEuclideanLin Q n = q • (V - V') := by
    dsimp only [n]
    rw [map_sub, map_smul, map_smul, hid, hid, ← smul_sub]
    congr 1
    module
  have hnorm : q * ‖V - V'‖ ≤ q * (κ * ‖n‖) := by
    calc
      _ = ‖Matrix.toEuclideanLin Q n‖ := by rw [hn, norm_smul, Real.norm_eq_abs, abs_of_pos hq]
      _ ≤ (∑ i, ∑ j, |Q i j|) * ‖n‖ := matrix_action_norm_le_entry_sum Q n
      _ ≤ (κ * q) * ‖n‖ := mul_le_mul_of_nonneg_right hsize (norm_nonneg _)
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ hq).mp hnorm

theorem PathData.Valid.normalized_velocity_forward_lipschitz {W : ℕ} {p : PathData W}
    {Nk L : ℝ} {ω : Fin W → ℝ} {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {f : ℝ → ℝ}
    {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (b : Fin p.C)
    (V V' : EuclideanSpace ℝ (Fin 2)) :
    ‖V - V'‖ ≤ p.κ * ‖((2 : ℝ) ^ p.T (p.lev b))⁻¹ •
      Matrix.toEuclideanLin (p.Q b)⁻¹ (V - p.u b) -
      ((2 : ℝ) ^ p.T (p.lev b))⁻¹ • Matrix.toEuclideanLin (p.Q b)⁻¹ (V' - p.u b)‖ := by
  have hb := h.2.2.2.2.2.2.2 b
  exact normalized_frame_forward_lipschitz (p.Q b) (p.u b) (by positivity)
    hb.2.2.1 (by simpa only [div_eq_mul_inv] using hb.2.2.2.2.2.1) V V'

/-- Counted two-coordinate angular bins and pair palettes give identical
ceilings, with no conversion loss. -/
theorem angular_bin_pair_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (V : Ω → EuclideanSpace ℝ (Fin 2)) (a : ℝ) (c : ENNReal)
    (hcap : ∀ i : Fin 2 → ℤ, μ {x | (fun j => ⌊V x j / a⌋) = i} ≤ c)
    (z : ℤ × ℤ) : μ {x | velocityPalette a (V x) = z} ≤ c := by
  have heq : {x | velocityPalette a (V x) = z} =
      {x | (fun j => ⌊V x j / a⌋) = ![z.1, z.2]} := by
    ext x
    simp [velocityPalette, funext_iff, Fin.forall_fin_two, Prod.ext_iff]
  rw [heq]
  exact hcap _

/-- The exact path's angular bins control balls for its normalized velocity
under ANY one fixed parent law. The radius condition is explicit. -/
theorem PathData.Valid.normalized_velocity_ball_cap {W : ℕ} {p : PathData W}
    {Nk L : ℝ} {ω : Fin W → ℝ} {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {f : ℝ → ℝ}
    {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (b : Fin p.C)
    (μ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) {a r : ℝ} (ha : 0 < a)
    (hscale : p.κ * r ≤ a) (c : ENNReal)
    (hcap : ∀ i : Fin 2 → ℤ, μ {q | (fun j => ⌊v q.1 j / a⌋) = i} ≤ c)
    (center : EuclideanSpace ℝ (Fin 2)) :
    μ {q | ‖((2 : ℝ) ^ p.T (p.lev b))⁻¹ •
      Matrix.toEuclideanLin (p.Q b)⁻¹ (v q.1 - p.u b) - center‖ ≤ r} ≤ 100 * c := by
  exact normalized_velocity_ball_mass_le μ (fun q => v q.1) _ ha (by linarith [h.1]) hscale
    (fun q q' => h.normalized_velocity_forward_lipschitz b (v q.1) (v q'.1))
    c (angular_bin_pair_cap μ (fun q => v q.1) a c hcap) center

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
