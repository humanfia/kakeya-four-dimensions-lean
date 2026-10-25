-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.NormalizedModel.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.LocalizedModel
import Submission.WZ.Obl.wz_separated_projection_dichotomy.SeparatedCore
import Submission.WZ.Obl.wz_separated_projection_dichotomy.FactorProjections

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

namespace LocalizedModel

variable {δ η : ℝ} {S T : Finset Plane} {H : Finset Triple}
variable (D : LocalizedModel δ η S T H)

noncomputable def leftVertices : Finset Plane := D.K.image (fun p => zoom 0 D.α p.1)
noncomputable def rightOne : Finset Plane := D.K.image (fun p => zoom D.b D.β p.2.1)
noncomputable def rightTwo : Finset Plane := D.K.image (fun p => zoom D.b D.β p.2.2)
noncomputable def graph : Finset Triple := D.K.image (zoomTriple D.b D.α D.β)

theorem alpha_pos : 0 < D.α := zero_lt_one.trans_le D.one_le_alpha
theorem beta_pos : 0 < D.β := zero_lt_one.trans_le D.one_le_beta

theorem left_eq_image : D.leftVertices = (D.K.image Prod.fst).image (zoom 0 D.α) := by
  simp only [leftVertices, Finset.image_image, Function.comp_def]

theorem rightOne_eq_image : D.rightOne =
    (D.K.image (fun p => p.2.1)).image (zoom D.b D.β) := by
  simp only [rightOne, Finset.image_image, Function.comp_def]

theorem rightTwo_eq_image : D.rightTwo =
    (D.K.image (fun p => p.2.2)).image (zoom D.b D.β) := by
  simp only [rightTwo, Finset.image_image, Function.comp_def]

theorem left_card : D.leftVertices.card = (D.K.image Prod.fst).card := by
  rw [D.left_eq_image, Finset.card_image_of_injective _ (zoom_injective 0 D.alpha_pos)]

theorem rightOne_card : D.rightOne.card = (D.K.image (fun p => p.2.1)).card := by
  rw [D.rightOne_eq_image, Finset.card_image_of_injective _ (zoom_injective D.b D.beta_pos)]

theorem rightTwo_card : D.rightTwo.card = (D.K.image (fun p => p.2.2)).card := by
  rw [D.rightTwo_eq_image, Finset.card_image_of_injective _ (zoom_injective D.b D.beta_pos)]

theorem graph_card : D.graph.card = D.K.card :=
  Finset.card_image_of_injective _ (zoomTriple_injective D.b D.alpha_pos D.beta_pos)

theorem graph_nonempty : D.graph.Nonempty := Finset.image_nonempty.mpr D.nonempty

theorem graph_subset : D.graph ⊆ D.leftVertices ×ˢ (D.rightOne ×ˢ D.rightTwo) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨q, hq, rfl⟩,
    Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨q, hq, rfl⟩,
      Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩⟩

theorem raw_left_subset (hH : H ⊆ S ×ˢ (T ×ˢ T)) : D.K.image Prod.fst ⊆ S := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  exact (Finset.mem_product.mp (hH (D.subset hp))).1

theorem raw_rightOne_subset (hH : H ⊆ S ×ˢ (T ×ˢ T)) :
    D.K.image (fun p => p.2.1) ⊆ T := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  exact (Finset.mem_product.mp (Finset.mem_product.mp (hH (D.subset hp))).2).1

theorem raw_rightTwo_subset (hH : H ⊆ S ×ˢ (T ×ˢ T)) :
    D.K.image (fun p => p.2.2) ⊆ T := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  exact (Finset.mem_product.mp (Finset.mem_product.mp (hH (D.subset hp))).2).2

theorem left_norm : ∀ x ∈ D.leftVertices, ‖x‖ ≤ 4 := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  exact norm_zoom_le_four_of_near D.alpha_pos.le D.centerA_norm.le (D.near p hp).1 D.alpha_ball

theorem rightOne_norm : ∀ x ∈ D.rightOne, ‖x‖ ≤ 4 := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  apply norm_zoom_le_four_of_near D.beta_pos.le (c := D.b)
  · simp [zoom]
  · exact (D.near p hp).2.1
  · exact D.beta_ball

theorem rightTwo_norm : ∀ x ∈ D.rightTwo, ‖x‖ ≤ 4 := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  exact norm_zoom_le_four_of_near D.beta_pos.le D.centerC_norm.le (D.near p hp).2.2 D.beta_ball

theorem standard_geometry : StandardTripleGeometry D.leftVertices D.rightOne D.rightTwo := by
  refine ⟨zoom 0 D.α D.a, zoom D.b D.β D.c, D.centerA_norm, D.centerC_norm, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    rw [zoom_dist 0 D.alpha_pos.le]
    exact (mul_le_mul_of_nonneg_left (D.near p hp).1 D.alpha_pos.le).trans D.alpha_ball
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    have hz : zoom D.b D.β D.b = 0 := by simp [zoom]
    rw [← hz, zoom_dist D.b D.beta_pos.le]
    exact (mul_le_mul_of_nonneg_left (D.near p hp).2.1 D.beta_pos.le).trans D.beta_ball
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    rw [zoom_dist D.b D.beta_pos.le]
    exact (mul_le_mul_of_nonneg_left (D.near p hp).2.2 D.beta_pos.le).trans D.beta_ball

theorem closed_frostman {ε θ : ℝ} (hbudget : LocalizationBudget δ η ε θ)
    (hH : H ⊆ S ×ˢ (T ×ˢ T))
    (hS : FiniteFrostman δ (225 * δ ^ (-4 * η)) S)
    (hT : FiniteFrostman δ (225 * δ ^ (-4 * η)) T) :
    ClosedFiniteFrostman δ (δ ^ (-θ)) D.leftVertices ∧
    ClosedFiniteFrostman δ (δ ^ (-θ)) D.rightOne ∧
    ClosedFiniteFrostman δ (δ ^ (-θ)) D.rightTwo := by
  have hδ := hbudget.delta_pos
  have hdensity : δ ^ (80 * η) * (S.card : ℝ) * (T.card : ℝ) * (T.card : ℝ) ≤
      (D.K.card : ℝ) := by simpa only [pow_two, mul_assoc] using D.density
  obtain ⟨h₁, h₂, h₃⟩ := FiniteFrostman.projected_factors hS hT hT hδ.le
    (by positivity) (by positivity) D.K (D.subset.trans hH) D.nonempty hdensity
  refine ⟨?_, ?_, ?_⟩
  · rw [D.left_eq_image]
    exact (h₁.map_expanding_zoom hδ.le 0 D.one_le_alpha).to_closed hδ hbudget.refined_frostman_bound
  · rw [D.rightOne_eq_image]
    exact (h₂.map_expanding_zoom hδ.le D.b D.one_le_beta).to_closed hδ hbudget.refined_frostman_bound
  · rw [D.rightTwo_eq_image]
    exact (h₃.map_expanding_zoom hδ.le D.b D.one_le_beta).to_closed hδ hbudget.refined_frostman_bound

theorem separated (hH : H ⊆ S ×ˢ (T ×ˢ T))
    (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y)
    (hT : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ ≤ dist x y) :
    (∀ x ∈ D.leftVertices, ∀ y ∈ D.leftVertices, x ≠ y → δ ≤ dist x y) ∧
    (∀ x ∈ D.rightOne, ∀ y ∈ D.rightOne, x ≠ y → δ ≤ dist x y) ∧
    (∀ x ∈ D.rightTwo, ∀ y ∈ D.rightTwo, x ≠ y → δ ≤ dist x y) := by
  rw [D.left_eq_image, D.rightOne_eq_image, D.rightTwo_eq_image]
  refine ⟨separated_map_expanding_zoom _ 0 D.one_le_alpha ?_,
    separated_map_expanding_zoom _ D.b D.one_le_beta ?_,
    separated_map_expanding_zoom _ D.b D.one_le_beta ?_⟩
  · exact fun x hx y hy hxy => hS x (D.raw_left_subset hH hx) y (D.raw_left_subset hH hy) hxy
  · exact fun x hx y hy hxy => hT x (D.raw_rightOne_subset hH hx) y (D.raw_rightOne_subset hH hy) hxy
  · exact fun x hx y hy hxy => hT x (D.raw_rightTwo_subset hH hx) y (D.raw_rightTwo_subset hH hy) hxy

theorem graph_density {θ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθη : 80 * η ≤ θ)
    (hH : H ⊆ S ×ˢ (T ×ˢ T)) :
    δ ^ θ * (D.leftVertices.card : ℝ) * (D.rightOne.card : ℝ) * (D.rightTwo.card : ℝ) ≤
      (D.graph.card : ℝ) := by
  have hpow : δ ^ θ ≤ δ ^ (80 * η) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hθη
  have h₁ : (D.leftVertices.card : ℝ) ≤ (S.card : ℝ) := by
    rw [D.left_card]
    exact_mod_cast Finset.card_le_card (D.raw_left_subset hH)
  have h₂ : (D.rightOne.card : ℝ) ≤ (T.card : ℝ) := by
    rw [D.rightOne_card]
    exact_mod_cast Finset.card_le_card (D.raw_rightOne_subset hH)
  have h₃ : (D.rightTwo.card : ℝ) ≤ (T.card : ℝ) := by
    rw [D.rightTwo_card]
    exact_mod_cast Finset.card_le_card (D.raw_rightTwo_subset hH)
  calc δ ^ θ * (D.leftVertices.card : ℝ) * (D.rightOne.card : ℝ) * (D.rightTwo.card : ℝ) ≤
        δ ^ (80 * η) * (S.card : ℝ) * (T.card : ℝ) * (T.card : ℝ) := by gcongr
    _ = δ ^ (80 * η) * (S.card : ℝ) * (T.card : ℝ) ^ 2 := by ring
    _ ≤ (D.K.card : ℝ) := D.density
    _ = (D.graph.card : ℝ) := by rw [D.graph_card]

end LocalizedModel

end WangZahlLot.Obl.wz_separated_projection_dichotomy
