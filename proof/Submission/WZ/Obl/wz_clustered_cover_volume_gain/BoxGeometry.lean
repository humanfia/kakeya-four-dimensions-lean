-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.BoxGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Definitions

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric

def boxAxis (e : V ≃ₗᵢ[ℝ] V) (i : Fin 3) : V :=
  e.symm (EuclideanSpace.basisFun (Fin 3) ℝ i)

theorem boxAxis_norm (e : V ≃ₗᵢ[ℝ] V) (i : Fin 3) : ‖boxAxis e i‖ = 1 := by
  simp [boxAxis]

theorem inner_boxAxis (e : V ≃ₗᵢ[ℝ] V) (i : Fin 3) (p : V) :
    inner ℝ (boxAxis e i) p = e p i := by
  unfold boxAxis
  rw [← e.inner_map_map, e.apply_symm_apply, EuclideanSpace.basisFun_inner]

/-- The diagonal of a square prism leaves room for a small displacement inside
the doubled prism, regardless of the rotation of its two broad axes. -/
theorem prism_norm_le {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c)
    (z : V) (e : V ≃ₗᵢ[ℝ] V) {p : V} (hp : p ∈ P a c c z e) :
    ‖p - z‖ ≤ 7 * c / 8 := by
  have hc : 0 ≤ c := ha.trans hac
  have hcoord : ∀ i : Fin 3, |e (p - z) i| ≤ c / 2 := by
    intro i
    fin_cases i
    · exact hp.1.trans (by linarith)
    · exact hp.2.1
    · exact hp.2.2
  have hs : ∀ i : Fin 3, (e (p - z) i) ^ 2 ≤ (c / 2) ^ 2 := by
    intro i
    have hh := mul_self_le_mul_self (abs_nonneg (e (p - z) i)) (hcoord i)
    simpa only [← sq, sq_abs] using hh
  have hnorm := EuclideanSpace.real_norm_sq_eq (e (p - z))
  rw [e.norm_map, Fin.sum_univ_three] at hnorm
  nlinarith [hs 0, hs 1, hs 2, norm_nonneg (p - z)]

/-- Projective distance controls the change of an absolute normal coordinate. -/
theorem abs_inner_le_projective (u v p : V) :
    |inner ℝ u p| ≤ |inner ℝ v p| + min ‖u - v‖ ‖u + v‖ * ‖p‖ := by
  have hsub (v : V) : |inner ℝ u p| ≤ |inner ℝ v p| + ‖u - v‖ * ‖p‖ := by
    calc
      _ = |inner ℝ v p + inner ℝ (u - v) p| := by rw [inner_sub_left]; ring_nf
      _ ≤ |inner ℝ v p| + |inner ℝ (u - v) p| := abs_add_le _ _
      _ ≤ _ := add_le_add le_rfl (abs_real_inner_le_norm (u - v) p)
  have hplus : |inner ℝ u p| ≤ |inner ℝ v p| + ‖u + v‖ * ‖p‖ := by
    simpa only [inner_neg_left, abs_neg, sub_neg_eq_add] using hsub (-v)
  by_cases h : ‖u - v‖ ≤ ‖u + v‖
  · simpa only [min_eq_left h] using hsub v
  · simpa only [min_eq_right (le_of_not_ge h)] using hplus

/-- Close normal directions and close centers imply the containment needed to
apply the frozen local convex count with a single reference grain. -/
theorem prism_subset_doubled_of_close {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hac : a ≤ c) (z z₀ : V) (e e₀ : V ≃ₗᵢ[ℝ] V)
    (hcenter : ‖z - z₀‖ ≤ c / 8)
    (hshort : |e₀ (z - z₀) 0| ≤ a / 8)
    (hangle : min ‖boxAxis e₀ 0 - boxAxis e 0‖ ‖boxAxis e₀ 0 + boxAxis e 0‖ ≤ a / (8 * c)) :
    P a c c z e ⊆ P (2 * a) (2 * c) (2 * c) z₀ e₀ := by
  intro p hp
  have hnorm := prism_norm_le ha hac z e hp
  have hnorm' : ‖p - z‖ ≤ c := by linarith
  have hdiff : p - z₀ = (p - z) + (z - z₀) := by abel
  have htotal : ‖p - z₀‖ ≤ c := by
    rw [hdiff]
    exact (norm_add_le _ _).trans (by linarith)
  have hbroad (i : Fin 3) : |e₀ (p - z₀) i| ≤ c := by
    calc
      _ ≤ ‖e₀ (p - z₀)‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (e₀ (p - z₀)) i
      _ = ‖p - z₀‖ := e₀.norm_map _
      _ ≤ c := htotal
  have hnormal : |e₀ (p - z) 0| ≤ a / 2 + a / 8 := by
    have hh := abs_inner_le_projective (boxAxis e₀ 0) (boxAxis e 0) (p - z)
    rw [inner_boxAxis, inner_boxAxis] at hh
    have ha8 : 0 ≤ a / (8 * c) := by positivity
    have hprod := mul_le_mul hangle hnorm' (norm_nonneg _) ha8
    have heq : a / (8 * c) * c = a / 8 := by field_simp
    rw [heq] at hprod
    linarith [hp.1]
  have hshort' : |e₀ (p - z₀) 0| ≤ a := by
    rw [hdiff, map_add, PiLp.add_apply]
    exact (abs_add_le _ _).trans (by linarith)
  change |e₀ (p - z₀) 0| ≤ 2 * a / 2 ∧ |e₀ (p - z₀) 1| ≤ 2 * c / 2 ∧
    |e₀ (p - z₀) 2| ≤ 2 * c / 2
  simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
    And.intro hshort' (And.intro (hbroad 1) (hbroad 2))

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
