-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.CardLines.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Strips

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

theorem coverLower_of_finite_separated {δ : ℝ} (hδ : 0 < δ) {S : Set Plane}
    (hS : S.Finite) (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y) :
    CoverLower δ S ((S.ncard : ℝ) / 25) := by
  classical
  have h := coverLower_of_separated hδ hS.toFinset
    (fun x hx y hy hxy => hsep x (hS.mem_toFinset.mp hx) y (hS.mem_toFinset.mp hy) hxy)
  simpa only [hS.coe_toFinset, Set.ncard_eq_toFinset_card S hS] using h

/-- In the plane, the hyperplane perpendicular to one member of an
orthonormal pair is an affine line in the other direction. -/
theorem hyperplane_eq_orthogonal_line {e e' : Plane}
    (he : ‖e‖ = 1) (he' : ‖e'‖ = 1) (hee' : inner ℝ e e' = 0) (c : ℝ) :
    {x : Plane | inner ℝ x e' = c} = Set.range (fun t : ℝ => c • e' + t • e) := by
  letI : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩
  have he₀ : e ≠ 0 := by intro h; simp [h] at he
  have he'₀ : e' ≠ 0 := by intro h; simp [h] at he'
  have hself : inner ℝ e' e' = 1 := by rw [real_inner_self_eq_norm_sq, he']; norm_num
  have hsym : inner ℝ e' e = 0 := by rw [real_inner_comm]; exact hee'
  ext x
  constructor
  · intro hx
    have hzero : inner ℝ e' (x - c • e') = 0 := by
      rw [inner_sub_right, real_inner_smul_right, hself, real_inner_comm x e']
      change inner ℝ x e' = c at hx
      linarith
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
      (Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero he'₀ he₀ hzero hsym)
    refine ⟨t, ?_⟩
    change c • e' + t • e = x
    rw [ht]
    abel
  · rintro ⟨t, rfl⟩
    simp only [Set.mem_setOf_eq, inner_add_left, real_inner_smul_left, hself, hee', mul_one,
      mul_zero, add_zero]

/-- Counts in orthogonal strips give the covering-number form of the line
alternative, at the cost of at most 25 separated points per covering ball. -/
theorem lineConclusion_of_strip_counts {δ ε N : ℝ} {F G : Set Plane}
    (hδ : 0 < δ) (hF : F.Finite) (hG : G.Finite)
    (hFs : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → δ ≤ dist x y)
    (hGs : ∀ x ∈ G, ∀ y ∈ G, x ≠ y → δ ≤ dist x y)
    (hN : 25 * δ ^ (ε - 1) ≤ N)
    (h : ∃ e e' : Plane, ‖e‖ = 1 ∧ ‖e'‖ = 1 ∧ inner ℝ e e' = 0 ∧
      ∃ c c' : ℝ, N ≤ ({a ∈ F | |inner ℝ a e - c| < δ}.ncard : ℝ) ∧
        N ≤ ({b ∈ G | |inner ℝ b e' - c'| < δ}.ncard : ℝ)) :
    LineConclusion δ ε F G := by
  obtain ⟨e, e', he, he', hee', c, c', hFc, hGc⟩ := h
  have hFN := coverLower_of_finite_separated hδ (S := {a ∈ F | |inner ℝ a e - c| < δ})
    (hF.subset (by intro x hx; exact hx.1))
    (fun x hx y hy hxy => hFs x hx.1 y hy.1 hxy)
  have hGN := coverLower_of_finite_separated hδ (S := {b ∈ G | |inner ℝ b e' - c'| < δ})
    (hG.subset (by intro x hx; exact hx.1))
    (fun x hx y hy hxy => hGs x hx.1 y hy.1 hxy)
  have hFL : CoverLower δ {a ∈ F | |inner ℝ a e - c| < δ} (δ ^ (ε - 1)) :=
    hFN.weaken ((le_div_iff₀ (by norm_num : (0 : ℝ) < 25)).mpr (by nlinarith))
  have hGL : CoverLower δ {b ∈ G | |inner ℝ b e' - c'| < δ} (δ ^ (ε - 1)) :=
    hGN.weaken ((le_div_iff₀ (by norm_num : (0 : ℝ) < 25)).mpr (by nlinarith))
  refine ⟨e, c' • e', c, he, ?_, ?_⟩
  · rw [thickening_hyperplane_eq_strip he]
    simpa only [Strip, Set.inter_def, Set.mem_setOf_eq, and_comm] using hFL
  · rw [← hyperplane_eq_orthogonal_line he he' hee' c', thickening_hyperplane_eq_strip he']
    simpa only [Strip, Set.inter_def, Set.mem_setOf_eq, and_comm] using hGL

end WangZahlLot.Obl.wz_separated_projection_dichotomy
