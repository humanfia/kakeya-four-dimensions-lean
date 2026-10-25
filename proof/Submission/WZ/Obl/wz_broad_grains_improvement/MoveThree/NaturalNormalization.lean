-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.NaturalNormalization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/NaturalNormalization.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NearNormalization
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.TubeStretch
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BoxCover

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (boxAxis boxAxis_norm frozenBasis frozenBasis_apply inner_boxAxis
    ball_subset_frozen_prism frozen_prism_ends tubeFrame tubeFrame_symm_apply norm_le_coord_sum)
open WangZahlLot.Obl.wz_flat_factored_improvement
  (coordinateAffine coordinateAffine_apply diagonalMap_apply coordinateAffine_volume
    coordinateAffine_dist_lower coordinateAffine_dist_upper)

noncomputable section

/-- A natural expanded-plate neighborhood has a common affine normalization.
Every grain then has volume comparable to rho squared and a macroscopic
diameter, independently of its long-axis orientation within the plate. -/
theorem natural_grain_normalization_exact {n : ℕ} {a ρ c : ℝ}
    (ha : 0 < a) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hc : 0 < c) (hac : a ≤ ρ * c)
    (z : Fin n → V) (e : Fin n → V ≃ₗᵢ[ℝ] V) (z₀ : V) (e₀ : V ≃ₗᵢ[ℝ] V)
    (hnear : ∀ i, P (a / ρ) c c (z i) (e i) ⊆
      P (2 * a / ρ) (2 * c) (2 * c) z₀ e₀) :
    ∃ f : V ≃ᵃ[ℝ] V,
      (∀ W, μ (f '' W) = O (ρ / (64 * a * c ^ 2)) * μ W) ∧
      (∀ i, f '' P a (ρ * c) c (z i) (e i) ⊆ ball (0 : V) 1) ∧
      (∀ i, ball (f (z i)) (a / (8 * c)) ⊆ f '' P a (ρ * c) c (z i) (e i)) ∧
      (∀ i, ∃ p ∈ f '' P a (ρ * c) c (z i) (e i),
        ∃ q ∈ f '' P a (ρ * c) c (z i) (e i), (1 / 4 : ℝ) ≤ dist p q) ∧
      (∀ p q, dist p q / (4 * c) ≤ dist (f p) (f q)) ∧
      (∀ i, ball (f (z i)) (ρ / 100) ⊆ f '' P a (ρ * c) c (z i) (e i)) ∧
      (∀ p q, dist (f p) (f q) ≤ (ρ / (4 * a)) * dist p q) ∧
      (∀ p i, f p i = (![ρ / (4 * a), (4 * c)⁻¹, (4 * c)⁻¹] : Fin 3 → ℝ) i * e₀ (p - z₀) i) := by
  let s : Fin 3 → ℝ := ![ρ / (4 * a), (4 * c)⁻¹, (4 * c)⁻¹]
  have hs (j : Fin 3) : 0 < s j := by fin_cases j <;> dsimp [s] <;> positivity
  let f := coordinateAffine (tubeFrame (frozenBasis e₀) z₀) s (fun j => (hs j).ne')
  have hcoord (p : V) (j : Fin 3) : f p j = s j * e₀ (p - z₀) j := by
    simp only [f, coordinateAffine_apply, diagonalMap_apply, tubeFrame_symm_apply,
      OrthonormalBasis.repr_apply_apply, frozenBasis_apply, inner_boxAxis]
  have hprod : (∏ j, s j) = ρ / (64 * a * c ^ 2) := by
    rw [Fin.prod_univ_three]
    change ρ / (4 * a) * (4 * c)⁻¹ * (4 * c)⁻¹ = _
    field_simp
    <;> ring
  have hlow (j : Fin 3) : (4 * c)⁻¹ ≤ |s j| := by
    rw [abs_of_pos (hs j)]
    fin_cases j
    · change (4 * c)⁻¹ ≤ ρ / (4 * a)
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    · exact le_rfl
    · exact le_rfl
  have hdist (p q : V) : dist p q / (4 * c) ≤ dist (f p) (f q) := by
    simpa only [div_eq_mul_inv, mul_comm] using
      coordinateAffine_dist_lower (tubeFrame (frozenBasis e₀) z₀) (fun j => (hs j).ne')
        (by positivity : 0 ≤ (4 * c)⁻¹) hlow p q
  have hrc : ρ * c ≤ c := mul_le_of_le_one_left hc.le hρ1
  have haa : a ≤ a / ρ := (le_div_iff₀ hρ).mpr (by nlinarith)
  have hbox (i : Fin n) : P a (ρ * c) c (z i) (e i) ⊆
      P (2 * a / ρ) (2 * c) (2 * c) z₀ e₀ := by
    apply Subset.trans ?_ (hnear i)
    intro p hp
    exact ⟨hp.1.trans (by linarith), hp.2.1.trans (by linarith), hp.2.2⟩
  refine ⟨f, ?_, ?_, ?_, ?_, hdist, ?_, ?_, hcoord⟩
  · intro W
    simpa only [hprod] using coordinateAffine_volume (tubeFrame (frozenBasis e₀) z₀) s hs W
  · intro i p hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hb := hbox i hq
    have hj (j : Fin 3) : |f q j| ≤ 1 / 4 := by
      rw [hcoord, abs_mul, abs_of_pos (hs j)]
      fin_cases j
      · change ρ / (4 * a) * |e₀ (q - z₀) 0| ≤ 1 / 4
        have hh := mul_le_mul_of_nonneg_left hb.1 (by positivity : 0 ≤ ρ / (4 * a))
        convert hh using 1 <;> field_simp <;> ring
      · change (4 * c)⁻¹ * |e₀ (q - z₀) 1| ≤ 1 / 4
        have hh := mul_le_mul_of_nonneg_left hb.2.1 (by positivity : 0 ≤ (4 * c)⁻¹)
        convert hh using 1 <;> field_simp <;> ring
      · change (4 * c)⁻¹ * |e₀ (q - z₀) 2| ≤ 1 / 4
        have hh := mul_le_mul_of_nonneg_left hb.2.2 (by positivity : 0 ≤ (4 * c)⁻¹)
        convert hh using 1 <;> field_simp <;> ring
    rw [mem_ball_zero_iff]
    linarith [norm_le_coord_sum (f q), hj 0, hj 1, hj 2]
  · intro i p hp
    refine ⟨f.symm p, ball_subset_frozen_prism hac hrc (z i) (e i) ?_,
      f.apply_symm_apply p⟩
    have hh := hdist (f.symm p) (z i)
    rw [f.apply_symm_apply] at hh
    have hlt : dist (f.symm p) (z i) / (4 * c) < a / (8 * c) := hh.trans_lt hp
    rw [mem_ball]
    convert (div_lt_iff₀ (by positivity : 0 < 4 * c)).mp hlt using 1 <;>
      field_simp <;> ring
  · intro i
    let p := z i + (c / 2) • boxAxis (e i) 2
    let q := z i - (c / 2) • boxAxis (e i) 2
    have he := frozen_prism_ends ha.le (mul_pos hρ hc).le hc.le (z i) (e i)
    refine ⟨f p, mem_image_of_mem f he.1, f q, mem_image_of_mem f he.2, ?_⟩
    have hpq : dist p q = c := by
      rw [dist_eq_norm, show p - q = c • boxAxis (e i) 2 by dsimp [p, q]; module,
        norm_smul, Real.norm_eq_abs, abs_of_pos hc, boxAxis_norm, mul_one]
    have hh := hdist p q
    rw [hpq, show c / (4 * c) = (1 / 4 : ℝ) by field_simp] at hh
    exact hh

  · intro i
    exact near_plate_normalized_ball ha hρ hρ1 hc (z i) z₀ (e i) e₀ f (hnear i) hcoord hdist
  · intro p q
    apply coordinateAffine_dist_upper (tubeFrame (frozenBasis e₀) z₀)
      (fun j => (hs j).ne') (by positivity : 0 ≤ ρ / (4 * a)) _ p q
    intro j
    rw [abs_of_pos (hs j)]
    fin_cases j
    · exact le_rfl
    all_goals
      change (4 * c)⁻¹ ≤ ρ / (4 * a)
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith

/-- The exact normalization with the coordinate identity omitted. -/
theorem natural_grain_normalization_controlled {n : ℕ} {a ρ c : ℝ}
    (ha : 0 < a) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hc : 0 < c) (hac : a ≤ ρ * c)
    (z : Fin n → V) (e : Fin n → V ≃ₗᵢ[ℝ] V) (z₀ : V) (e₀ : V ≃ₗᵢ[ℝ] V)
    (hnear : ∀ i, P (a / ρ) c c (z i) (e i) ⊆
      P (2 * a / ρ) (2 * c) (2 * c) z₀ e₀) :
    ∃ f : V ≃ᵃ[ℝ] V,
      (∀ W, μ (f '' W) = O (ρ / (64 * a * c ^ 2)) * μ W) ∧
      (∀ i, f '' P a (ρ * c) c (z i) (e i) ⊆ ball (0 : V) 1) ∧
      (∀ i, ball (f (z i)) (a / (8 * c)) ⊆ f '' P a (ρ * c) c (z i) (e i)) ∧
      (∀ i, ∃ p ∈ f '' P a (ρ * c) c (z i) (e i),
        ∃ q ∈ f '' P a (ρ * c) c (z i) (e i), (1 / 4 : ℝ) ≤ dist p q) ∧
      (∀ p q, dist p q / (4 * c) ≤ dist (f p) (f q)) ∧
      (∀ i, ball (f (z i)) (ρ / 100) ⊆ f '' P a (ρ * c) c (z i) (e i)) ∧
      (∀ p q, dist (f p) (f q) ≤ (ρ / (4 * a)) * dist p q) := by
  obtain ⟨f, hv, hb, hi, hd, hlo, hr, hLip, _⟩ :=
    natural_grain_normalization_exact ha hρ hρ1 hc hac z e z₀ e₀ hnear
  exact ⟨f, hv, hb, hi, hd, hlo, hr, hLip⟩

/-- The round normalization, with its forward Lipschitz control omitted. -/
theorem natural_grain_normalization_round {n : ℕ} {a ρ c : ℝ}
    (ha : 0 < a) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hc : 0 < c) (hac : a ≤ ρ * c)
    (z : Fin n → V) (e : Fin n → V ≃ₗᵢ[ℝ] V) (z₀ : V) (e₀ : V ≃ₗᵢ[ℝ] V)
    (hnear : ∀ i, P (a / ρ) c c (z i) (e i) ⊆
      P (2 * a / ρ) (2 * c) (2 * c) z₀ e₀) :
    ∃ f : V ≃ᵃ[ℝ] V,
      (∀ W, μ (f '' W) = O (ρ / (64 * a * c ^ 2)) * μ W) ∧
      (∀ i, f '' P a (ρ * c) c (z i) (e i) ⊆ ball (0 : V) 1) ∧
      (∀ i, ball (f (z i)) (a / (8 * c)) ⊆ f '' P a (ρ * c) c (z i) (e i)) ∧
      (∀ i, ∃ p ∈ f '' P a (ρ * c) c (z i) (e i),
        ∃ q ∈ f '' P a (ρ * c) c (z i) (e i), (1 / 4 : ℝ) ≤ dist p q) ∧
      (∀ p q, dist p q / (4 * c) ≤ dist (f p) (f q)) ∧
      (∀ i, ball (f (z i)) (ρ / 100) ⊆ f '' P a (ρ * c) c (z i) (e i)) := by
  obtain ⟨f, hv, hb, hi, hd, hlo, hr, -⟩ :=
    natural_grain_normalization_controlled ha hρ hρ1 hc hac z e z₀ e₀ hnear
  exact ⟨f, hv, hb, hi, hd, hlo, hr⟩

/-- The original normalization interface, with the stronger round interior
available separately from `natural_grain_normalization_round`. -/
theorem natural_grain_normalization {n : ℕ} {a ρ c : ℝ}
    (ha : 0 < a) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hc : 0 < c) (hac : a ≤ ρ * c)
    (z : Fin n → V) (e : Fin n → V ≃ₗᵢ[ℝ] V) (z₀ : V) (e₀ : V ≃ₗᵢ[ℝ] V)
    (hnear : ∀ i, P (a / ρ) c c (z i) (e i) ⊆
      P (2 * a / ρ) (2 * c) (2 * c) z₀ e₀) :
    ∃ f : V ≃ᵃ[ℝ] V,
      (∀ W, μ (f '' W) = O (ρ / (64 * a * c ^ 2)) * μ W) ∧
      (∀ i, f '' P a (ρ * c) c (z i) (e i) ⊆ ball (0 : V) 1) ∧
      (∀ i, ball (f (z i)) (a / (8 * c)) ⊆ f '' P a (ρ * c) c (z i) (e i)) ∧
      (∀ i, ∃ p ∈ f '' P a (ρ * c) c (z i) (e i),
        ∃ q ∈ f '' P a (ρ * c) c (z i) (e i), (1 / 4 : ℝ) ≤ dist p q) ∧
      (∀ p q, dist p q / (4 * c) ≤ dist (f p) (f q)) := by
  obtain ⟨f, hv, hb, hi, hd, hdist, -⟩ :=
    natural_grain_normalization_round ha hρ hρ1 hc hac z e z₀ e₀ hnear
  exact ⟨f, hv, hb, hi, hd, hdist⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
