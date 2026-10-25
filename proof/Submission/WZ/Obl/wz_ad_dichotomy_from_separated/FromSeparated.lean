-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_ad_dichotomy_from_separated.FromSeparated.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_ad_dichotomy_from_separated.NormalizedModel
import Submission.WZ.Obl.wz_ad_dichotomy_from_separated.CenterTriples

namespace WangZahlLot.Obl.wz_ad_dichotomy_from_separated

open Set Metric

/-- The final geometric reduction: the separated finite Frostman dichotomy
implies the finite model needed for the original AD theorem. -/
theorem center_dichotomy_of_separated {δ η ε θ : ℝ}
    (hη : 0 < η) (hε : 0 < ε) (hε1 : ε < 1) (hηθ : 84 * η < θ)
    (hbudget : LocalizationBudget δ η ε θ)
    (hcore : SeparatedDichotomyAt δ θ (ε / 4)) : CenterDichotomyAt δ η ε := by
  classical
  intro S T hSsq hTsq hSN hTN hSup hTup hSsep hTsep hSF hTF H hHN
  have hδ := hbudget.delta_pos
  have hHprod := centerFinset_subset H
  have hHpos : (0 : ℝ) < (centerFinset H).card := by
    rw [centerFinset_card]
    exact (Real.rpow_pos_of_pos hδ _).trans_le hHN
  have hHne : (centerFinset H).Nonempty := Finset.card_pos.mp (by exact_mod_cast hHpos)
  obtain ⟨D⟩ := exists_localized_model hη hbudget S T hSsq hTsq hSF hTF
    (centerFinset H) hHprod hHne (centerFinset_density hδ S T H hSup hTup hHN)
  obtain ⟨hsep₁, hsep₂, hsep₃⟩ := D.separated hHprod
    (fun x hx y hy hxy => (hSsep x hx y hy hxy).le)
    (fun x hx y hy hxy => (hTsep x hx y hy hxy).le)
  obtain ⟨hF₁, hF₂, hF₃⟩ := D.closed_frostman hbudget hHprod hSF hTF
  have hden := D.graph_density (θ := θ) hδ hbudget.delta_le_one (by linarith) hHprod
  rcases hcore D.leftVertices D.rightOne D.rightTwo D.left_norm D.rightOne_norm D.rightTwo_norm
      hsep₁ hsep₂ hsep₃ hF₁ hF₂ hF₃ D.standard_geometry D.graph D.graph_nonempty
      D.graph_subset hden with hl | hg
  · left
    have hleft : (↑D.leftVertices : Set Plane) ⊆ zoom 0 D.α '' (↑S : Set Plane) := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨p.1, (Finset.mem_product.mp (hHprod (D.subset hp))).1, rfl⟩
    have hright : (↑D.rightOne : Set Plane) ⊆ zoom D.b D.β '' (↑T : Set Plane) := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨p.2.1, (Finset.mem_product.mp (Finset.mem_product.mp (hHprod (D.subset hp))).2).1, rfl⟩
    exact (hl.mono_set hleft hright).of_expanding_zooms D.b hδ D.one_le_alpha D.one_le_beta
      (hbudget.line_bound D.alpha_pos D.alpha_sq_bound)
      (hbudget.line_bound D.beta_pos D.beta_sq_bound)
  · right
    have hsrc : ProjectionGain δ θ ((ε / 2) / 2) (↑D.graph : Set Triple) := by
      rw [show (ε / 2) / 2 = ε / 4 by ring]
      exact hg
    let k : ℝ := (D.α * D.β)⁻¹
    let M : ℝ := δ ^ (-24 * η)
    have hαβ : 0 < D.α * D.β := mul_pos D.alpha_pos D.beta_pos
    have hk : 0 < k := inv_pos.mpr hαβ
    have hM : 1 ≤ M := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ
      hbudget.delta_le_one (by nlinarith)
    have hMk : 1 ≤ M * k := by
      change 1 ≤ M * (D.α * D.β)⁻¹
      rw [← div_eq_mul_inv]
      exact (le_div_iff₀ hαβ).mpr (by simpa [M] using D.product_bound)
    have hscale : δ ≤ M * k * δ := by nlinarith
    apply hsrc.of_affine_rescaling (k := k) (u := 0) (M := M) hδ hδ hk hM
      (by positivity) (by linarith) hscale
      (hbudget.length_bound (by linarith)) hbudget.projection_bound
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    refine ⟨p, ?_, ?_⟩
    · have hmem : p ∈ (↑(centerFinset H) : Set Triple) := D.subset hp
      simpa only [coe_centerFinset] using hmem
    · rw [dotValue_zoomTriple, add_zero]
      simp only [k, ← mul_assoc, inv_mul_cancel₀ hαβ.ne', one_mul]

/-- Parameter-level form of the final reduction, matching the original frozen
statement through the established finite-model bridge. -/
theorem reduce_to_separated_dichotomy
    (hcore : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ θ d : ℝ, 0 < θ ∧ 0 < d ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d → SeparatedDichotomyAt δ θ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ F G : Set Plane,
        InUnitSquare F → InUnitSquare G → AD δ (δ ^ (-η)) F → AD δ (δ ^ (-η)) G →
          LineConclusion δ ε F G ∨ ProjectionConclusion δ η ε F G := by
  apply reduce_to_center_dichotomy
  intro ε hε hε1
  obtain ⟨θ, d, hθ, hd, H⟩ := hcore (ε / 4) (by positivity) (by linarith)
  obtain ⟨η, s, hη, hηsmall, hηθ, hs, hbudget⟩ := exists_localization_budget hε hθ
  refine ⟨η, min d s, hη, lt_min hd hs, ?_⟩
  intro δ hδ hδsmall
  exact center_dichotomy_of_separated hη hε hε1 hηθ
    (hbudget δ hδ (hδsmall.trans (min_le_right _ _)))
    (H δ hδ (hδsmall.trans (min_le_left _ _)))

end WangZahlLot.Obl.wz_ad_dichotomy_from_separated
