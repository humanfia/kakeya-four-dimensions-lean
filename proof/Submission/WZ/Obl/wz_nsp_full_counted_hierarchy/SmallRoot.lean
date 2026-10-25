-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.SmallRoot.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Localization

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open Set Metric LeanEval.Analysis.WangZahlKakeya

/-- Perturbing the initial point and the direction enlarges the tube by the
sum of the two perturbations. -/
theorem tube_subset_of_parameters {r s t : ℝ} {x v y w : Space}
    (hx : ‖x - y‖ ≤ s) (hv : ‖v - w‖ ≤ t) :
    Tube r x v ⊆ Tube (r + s + t) y w := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨θ, hθ, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq
  have hseg : y + θ • w ∈ segment ℝ y (y + w) := by
    rw [segment_eq_image']
    refine ⟨θ, hθ, ?_⟩
    simp only [add_sub_cancel_left]
  refine mem_thickening_iff.mpr ⟨y + θ • w, hseg, ?_⟩
  have hdist : dist (x + θ • v) (y + θ • w) ≤ s + t := by
    rw [dist_eq_norm]
    have he : x + θ • v - (y + θ • w) = (x - y) + θ • (v - w) := by module
    rw [he]
    calc
      _ ≤ ‖x - y‖ + ‖θ • (v - w)‖ := norm_add_le _ _
      _ = ‖x - y‖ + θ * ‖v - w‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
      _ ≤ s + 1 * ‖v - w‖ := add_le_add hx (mul_le_mul_of_nonneg_right hθ.2 (norm_nonneg _))
      _ ≤ s + t := by linarith
  exact (dist_triangle p (x + θ • v) (y + θ • w)).trans_lt (by linarith)

/-- Centering a unit core at the origin leaves exactly one half-unit for its
length, in addition to the tube radius. -/
theorem centered_tube_ball {r : ℝ} {v : Space} (hv : ‖v‖ = 1) :
    Tube r ((-(1 / 2 : ℝ)) • v) v ⊆ ball 0 (1 / 2 + r) := by
  have hleft : (-(1 / 2 : ℝ)) • v ∈ closedBall (0 : Space) (1 / 2) := by
    simp [mem_closedBall, dist_zero_right, norm_smul, hv]
  have hright : (-(1 / 2 : ℝ)) • v + v ∈ closedBall (0 : Space) (1 / 2) := by
    have he : (-(1 / 2 : ℝ)) • v + v = (1 / 2 : ℝ) • v := by module
    rw [he]
    simp [mem_closedBall, dist_zero_right, norm_smul, hv]
  have hseg := (convex_closedBall (0 : Space) (1 / 2)).segment_subset hleft hright
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  have hqnorm : ‖q‖ ≤ 1 / 2 := by simpa only [mem_closedBall, dist_zero_right] using hseg hq
  have hp : ‖p‖ < 1 / 2 + r := by
    have ht := dist_triangle p q 0
    simp only [dist_zero_right] at ht
    linarith
  simpa only [mem_ball, dist_zero_right] using hp

/-- One common translation centers the anchor segment and keeps every nearby
parameter pair inside a narrow tube about that anchor. -/
theorem translated_cell_in_root {n : ℕ} {x v : Fin n → Space}
    {S : Finset (Fin n)} {ε δ h : ℝ} (hS : S.Nonempty)
    (hparam : ∀ i ∈ S, ∀ j ∈ S, ‖x i - x j‖ < ε ∧ ‖v i - v j‖ < ε)
    (hunit : ∀ i, ‖v i‖ = 1) (hwidth : δ + 2 * ε ≤ h) :
    ∃ (D : Space ≃ᵃⁱ[ℝ] Space) (y w : Space), ‖w‖ = 1 ∧
      Tube h y w ⊆ ball 0 (1 / 2 + h) ∧
      ∀ i ∈ S, Tube δ (D (x i)) (D.linear (v i)) ⊆ Tube h y w := by
  obtain ⟨i₀, hi₀⟩ := hS
  let D := AffineIsometryEquiv.constVAdd ℝ Space (-(x i₀ + (1 / 2 : ℝ) • v i₀))
  let y := (-(1 / 2 : ℝ)) • v i₀
  refine ⟨D, y, v i₀, hunit i₀, centered_tube_ball (hunit i₀), ?_⟩
  intro i hi
  have hpos : ‖D (x i) - y‖ < ε := by
    have he : D (x i) - y = x i - x i₀ := by dsimp [D, y]; module
    rw [he]
    exact (hparam i hi i₀ hi₀).1
  have hdir : ‖D.linear (v i) - v i₀‖ < ε := by
    change ‖v i - v i₀‖ < ε
    exact (hparam i hi i₀ hi₀).2
  apply (tube_subset_of_parameters hpos.le hdir.le).trans
  apply thickening_mono
  linarith

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
