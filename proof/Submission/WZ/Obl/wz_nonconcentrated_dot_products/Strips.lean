-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.Strips.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.TwoEnds
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Frostman

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

open Set Metric

attribute [local instance] Classical.propDecidable

def Strip (e : Plane) (c r : ℝ) : Set Plane := {x | |inner ℝ x e - c| < r}

theorem thickening_hyperplane_eq_strip {e : Plane} (he : ‖e‖ = 1) (c r : ℝ) :
    Metric.thickening r {x : Plane | inner ℝ x e = c} = Strip e c r := by
  ext x
  rw [Metric.mem_thickening_iff]
  have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  constructor
  · rintro ⟨z, hz, hdist⟩
    change inner ℝ z e = c at hz
    change |inner ℝ x e - c| < r
    calc |inner ℝ x e - c| = |inner ℝ (x - z) e| := by rw [inner_sub_left, hz]
      _ ≤ ‖x - z‖ * ‖e‖ := abs_real_inner_le_norm _ _
      _ = dist x z := by rw [he, mul_one, dist_eq_norm]
      _ < r := hdist
  · intro hx
    refine ⟨x - (inner ℝ x e - c) • e, ?_, ?_⟩
    · change inner ℝ (x - (inner ℝ x e - c) • e) e = c
      rw [inner_sub_left, real_inner_smul_left, hee]
      ring
    · have hs : x - (x - (inner ℝ x e - c) • e) = (inner ℝ x e - c) • e := by abel
      rw [dist_eq_norm, hs, norm_smul, he, mul_one, Real.norm_eq_abs]
      exact hx

/-- Finite-set two-ends reduction in strips, at all scales at least `δ`.
The selected strip retains a `w^ζ / 2` fraction of the points. -/
theorem exists_strip_localization (E : Finset Plane)
    (hE : InUnitSquare (↑E : Set Plane)) {δ ζ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hζ : 0 ≤ ζ) :
    ∃ (e : Plane) (c w : ℝ) (E' : Finset Plane), ‖e‖ = 1 ∧ δ ≤ w ∧ w ≤ 1 ∧
      E' = E.filter (fun x => x ∈ Strip e c w) ∧
      w ^ ζ * (E.card : ℝ) / 2 ≤ (E'.card : ℝ) ∧
      ∀ (u : Plane) (d r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ 1 →
        ((E'.filter (fun x => x ∈ Strip u d r)).card : ℝ) ≤
          2 * (r / w) ^ ζ * (E'.card : ℝ) := by
  let e₀ : {e : Plane // ‖e‖ = 1} := ⟨EuclideanSpace.single 0 1, by simp⟩
  let U (i : {e : Plane // ‖e‖ = 1} × ℝ) (r : ℝ) := Strip i.1.val i.2 r
  have hcover : ∀ x ∈ E, x ∈ U (e₀, 1 / 2) 1 := by
    intro x hx
    have hx0 := hE x hx 0
    change |inner ℝ x (EuclideanSpace.single 0 1) - (1 / 2 : ℝ)| < 1
    simpa only [EuclideanSpace.inner_single_right, conj_trivial, one_mul, abs_lt] using
      (show -1 < x 0 - 1 / 2 ∧ x 0 - 1 / 2 < 1 by constructor <;> linarith)
  obtain ⟨i, w, E', hδw, hw1, hE', hcard, htwo⟩ :=
    exists_weighted_localization E U (e₀, 1 / 2) hδ hδ1 hζ hcover
  refine ⟨i.1.val, i.2, w, E', i.1.property, hδw, hw1, ?_, hcard, ?_⟩
  · ext x
    exact (hE' x).trans Finset.mem_filter.symm
  · intro u d r hu hδr hr1
    exact htwo (⟨u, hu⟩, d) r hδr hr1

/-- Retaining a `θ` fraction of a Frostman set costs at most `θ⁻¹` in its
normalized counting constant. -/
theorem FiniteFrostman.subset {δ C θ : ℝ} {S T : Finset Plane}
    (h : FiniteFrostman δ C S) (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hθ : 0 < θ)
    (hTS : T ⊆ S) (hcard : θ * (S.card : ℝ) ≤ (T.card : ℝ)) :
    FiniteFrostman δ (C / θ) T := by
  intro x r hδr
  have hr : 0 ≤ r := hδ.trans hδr
  have hcount : (ballCount T x r : ℝ) ≤ ballCount S x r := by
    dsimp [ballCount]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hTS)
  calc (ballCount T x r : ℝ) ≤ (ballCount S x r : ℝ) := hcount
    _ ≤ C * r * (S.card : ℝ) := h x r hδr
    _ = (C / θ) * r * (θ * (S.card : ℝ)) := by field_simp
    _ ≤ (C / θ) * r * (T.card : ℝ) :=
      mul_le_mul_of_nonneg_left hcard (mul_nonneg (div_nonneg hC hθ.le) hr)

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
