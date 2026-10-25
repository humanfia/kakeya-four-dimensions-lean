-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.NormDefs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Basic

/-!
# Normalization by a mild isotropic zoom: definitions

`GGX σ` is the conclusion of the global grains step with `δ ^ (-η)` constants: arbitrarily
small examples with a `δ ^ (-η)`-Lipschitz slope `f` and a plane map `V` that is
`δ ^ (-η)`-Lipschitz on the shaded union. `Grains σ` asks for constant `1`; it is obtained by
zooming about a point by `lam = 3 δ ^ (-η)` (`zoom`), replacing every tube through a small
ball by its zoomed unit piece (`pieceStart`, `subTube`).
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory
open scoped ENNReal

/-- Examples with Lipschitz constants `δ ^ (-η)` instead of `1`. -/
def GGX (σ : ℝ) : Prop :=
  ∀ η d0 : ℝ, 0 < η → 0 < d0 → ∃ δ : ℝ, 0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1 / 100 : ℝ) ∧
    ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Family η δ n x v Y ∧ Separated η δ n x v ∧
      ∃ (f : ℝ → ℝ) (V : Space → Space),
        (∀ a b : ℝ, dist (f a) (f b) ≤ δ ^ (-η) * dist a b) ∧
        (∀ z : ℝ, z ∈ Icc (-1) 1 →
          Covering δ (1 - σ) (δ ^ (-η)) (projectedSlice f (⋃ i, Y i) z)) ∧
        (∀ p, p ∈ (⋃ i, Y i) → ‖V p‖ = 1) ∧
        (∀ i p, p ∈ Y i → |inner ℝ (v i) (V p)| ≤ δ) ∧
        (∀ p, p ∈ (⋃ i, Y i) → ∀ q, q ∈ (⋃ i, Y i) → dist (V p) (V q) ≤ δ ^ (-η) * dist p q) ∧
        (∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 → ∀ p : Space, p ∈ (⋃ i, Y i) →
          Covering ρ (1 - σ) (δ ^ (-η))
            ((fun q : Space => inner ℝ (V p) q) '' ((⋃ i, Y i) ∩ ball p (Real.sqrt ρ))))

/-- Isotropic zoom about `c` by the factor `lam`. -/
noncomputable def zoom (c : Space) (lam : ℝ) (p : Space) : Space := lam • (p - c)

/-- The point of the line through `x` with unit direction `v` closest to `c`. -/
noncomputable def foot (c x v : Space) : Space := x + (inner ℝ (c - x) v) • v

/-- The start of the zoomed unit piece of the line through `x` with direction `v`. -/
noncomputable def pieceStart (c : Space) (lam : ℝ) (x v : Space) : Space :=
  lam • (foot c x v - c) - (1 / 2 : ℝ) • v

/-- The original piece: radius `δ`, length `1 / lam`, centred at the foot. -/
noncomputable def subTube (c : Space) (lam δ : ℝ) (x v : Space) : Set Space :=
  tube δ (foot c x v - (1 / (2 * lam)) • v) ((1 / lam) • v)

theorem mem_tube_iff {r : ℝ} {x v p : Space} :
    p ∈ tube r x v ↔ ∃ t ∈ Icc (0 : ℝ) 1, ‖p - (x + t • v)‖ < r := by
  constructor
  · intro hp
    obtain ⟨y, hy, hpy⟩ := mem_thickening_iff.mp hp
    rw [segment_eq_image'] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    refine ⟨t, ht, ?_⟩
    rw [← dist_eq_norm]
    simpa using hpy
  · rintro ⟨t, ht, hp⟩
    apply mem_thickening_iff.mpr
    refine ⟨x + t • v, ?_, ?_⟩
    · rw [segment_eq_image']
      exact ⟨t, ht, by simp⟩
    · rwa [dist_eq_norm]

theorem axis_mem_tube {r : ℝ} (hr : 0 < r) (x v : Space) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    x + t • v ∈ tube r x v :=
  mem_tube_iff.mpr ⟨t, ht, by simpa using hr⟩

/-- Reversing a segment does not change the tube. -/
theorem tube_reverse (r : ℝ) (x v : Space) : tube r (x + v) (-v) = tube r x v := by
  unfold tube
  rw [show x + v + -v = x by abel, segment_symm]

theorem tube_mono_radius {r r' : ℝ} (h : r ≤ r') (x v : Space) : tube r x v ⊆ tube r' x v :=
  thickening_mono h _

/-- Closest point identity: `c - (x + t v)` splits orthogonally at the foot. -/
theorem norm_sub_axis_sq {c x v : Space} (hv : ‖v‖ = 1) (t : ℝ) :
    ‖c - (x + t • v)‖ ^ 2 = ‖c - foot c x v‖ ^ 2 + (inner ℝ (c - x) v - t) ^ 2 := by
  have horth : inner ℝ (c - foot c x v) v = 0 := by
    simp only [foot, sub_add_eq_sub_sub, inner_sub_left, inner_smul_left,
      real_inner_self_eq_norm_sq, hv]
    simp
  have he : c - (x + t • v) = (c - foot c x v) + (inner ℝ (c - x) v - t) • v := by
    simp only [foot]; module
  rw [he, norm_add_sq_real, inner_smul_right, horth, norm_smul, Real.norm_eq_abs, hv, mul_one,
    sq_abs]
  ring

theorem norm_sub_foot_le {c x v : Space} (hv : ‖v‖ = 1) (t : ℝ) :
    ‖c - foot c x v‖ ≤ ‖c - (x + t • v)‖ := by
  have h := norm_sub_axis_sq (c := c) (x := x) hv t
  apply le_of_sq_le_sq _ (norm_nonneg _)
  · nlinarith [sq_nonneg (inner ℝ (c - x) v - t)]

theorem abs_param_sub_le {c x v : Space} (hv : ‖v‖ = 1) (t : ℝ) :
    |inner ℝ (c - x) v - t| ≤ ‖c - (x + t • v)‖ := by
  have h := norm_sub_axis_sq (c := c) (x := x) hv t
  apply abs_le_of_sq_le_sq' _ (norm_nonneg _) |>.elim (fun h1 h2 => abs_le.mpr ⟨h1, h2⟩)
  nlinarith [sq_nonneg ‖c - foot c x v‖, sq_abs (inner ℝ (c - x) v - t)]

theorem zoom_sub (c : Space) (lam : ℝ) (p q : Space) :
    zoom c lam p - zoom c lam q = lam • (p - q) := by
  simp only [zoom]; module

theorem norm_zoom_sub {c : Space} {lam : ℝ} (hlam : 0 ≤ lam) (p q : Space) :
    ‖zoom c lam p - zoom c lam q‖ = lam * ‖p - q‖ := by
  rw [zoom_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam]

/-- Points of the original piece zoom into the zoomed unit piece. -/
theorem zoom_mem_piece {c : Space} {lam δ : ℝ} (hlam : 0 < lam) {x v p : Space}
    (hp : p ∈ subTube c lam δ x v) :
    zoom c lam p ∈ tube (lam * δ) (pieceStart c lam x v) v := by
  obtain ⟨t, ht, hpt⟩ := mem_tube_iff.mp hp
  refine mem_tube_iff.mpr ⟨t, ht, ?_⟩
  have he : zoom c lam p - (pieceStart c lam x v + t • v) =
      lam • (p - (foot c x v - (1 / (2 * lam)) • v + t • (1 / lam) • v)) := by
    simp only [zoom, pieceStart, smul_sub, smul_add, smul_smul]
    have h1 : lam * (1 / (2 * lam)) = 1 / 2 := by field_simp
    have h2 : lam * (t * (1 / lam)) = t := by field_simp
    rw [h1, h2]
    module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
  exact mul_lt_mul_of_pos_left hpt hlam

/-- Conversely every point of the zoomed piece is the zoom of a point of the original piece. -/
theorem exists_zoom_eq_of_mem_piece {c : Space} {lam δ : ℝ} (hlam : 0 < lam) {x v q : Space}
    (hq : q ∈ tube (lam * δ) (pieceStart c lam x v) v) :
    ∃ p ∈ subTube c lam δ x v, zoom c lam p = q := by
  refine ⟨c + lam⁻¹ • q, ?_, ?_⟩
  · obtain ⟨t, ht, hqt⟩ := mem_tube_iff.mp hq
    refine mem_tube_iff.mpr ⟨t, ht, ?_⟩
    have he : c + lam⁻¹ • q - (foot c x v - (1 / (2 * lam)) • v + t • (1 / lam) • v) =
        lam⁻¹ • (q - (pieceStart c lam x v + t • v)) := by
      simp only [pieceStart, smul_sub, smul_add, smul_smul]
      have h1 : lam⁻¹ * lam = 1 := inv_mul_cancel₀ hlam.ne'
      have h2 : lam⁻¹ * (1 / 2) = 1 / (2 * lam) := by field_simp
      have h3 : t * (1 / lam) = lam⁻¹ * t := by field_simp
      rw [h1, h2, h3, one_smul]
      module
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam)]
    calc lam⁻¹ * ‖q - (pieceStart c lam x v + t • v)‖ < lam⁻¹ * (lam * δ) :=
          mul_lt_mul_of_pos_left hqt (inv_pos.mpr hlam)
      _ = δ := by field_simp
  · simp only [zoom, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]

/-- A zoomed piece of a line passing near the centre lies in the unit ball. -/
theorem piece_subset_ball {c : Space} {lam δ r : ℝ} (hlam : 0 < lam) {x v : Space}
    (hv : ‖v‖ = 1) (hc : ‖c - foot c x v‖ ≤ r) (hr : lam * r ≤ 1 / 4)
    (hδ : lam * δ ≤ 1 / 4) :
    tube (lam * δ) (pieceStart c lam x v) v ⊆ ball 0 1 := by
  intro q hq
  obtain ⟨t, ht, hqt⟩ := mem_tube_iff.mp hq
  rw [mem_ball_zero_iff]
  have he : pieceStart c lam x v + t • v = lam • (foot c x v - c) + (t - 1 / 2) • v := by
    simp only [pieceStart]; module
  have h1 : ‖pieceStart c lam x v + t • v‖ ≤ 3 / 4 := by
    rw [he]
    calc ‖lam • (foot c x v - c) + (t - 1 / 2) • v‖ ≤
          ‖lam • (foot c x v - c)‖ + ‖(t - 1 / 2) • v‖ := norm_add_le _ _
      _ = lam * ‖c - foot c x v‖ + |t - 1 / 2| := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlam, hv,
            mul_one, norm_sub_rev]
      _ ≤ lam * r + 1 / 2 := by
          gcongr
          rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      _ ≤ 3 / 4 := by linarith
  calc ‖q‖ = ‖(q - (pieceStart c lam x v + t • v)) + (pieceStart c lam x v + t • v)‖ := by
        congr 1; abel
    _ ≤ ‖q - (pieceStart c lam x v + t • v)‖ + ‖pieceStart c lam x v + t • v‖ :=
        norm_add_le _ _
    _ < lam * δ + 3 / 4 := by linarith
    _ ≤ 1 := by linarith

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
