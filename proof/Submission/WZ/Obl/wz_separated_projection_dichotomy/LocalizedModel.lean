-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.LocalizedModel.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.LocalScales
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Localization
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Normalization

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

structure LocalizedModel (δ η : ℝ) (S T : Finset Plane) (H : Finset Triple) where
  K : Finset Triple
  a : Plane
  b : Plane
  c : Plane
  α : ℝ
  β : ℝ
  subset : K ⊆ H
  nonempty : K.Nonempty
  density : δ ^ (80 * η) * (S.card : ℝ) * (T.card : ℝ) ^ 2 ≤ (K.card : ℝ)
  near : ∀ p ∈ K, dist p.1 a ≤ δ ^ (12 * η) ∧
    dist p.2.1 b ≤ δ ^ (12 * η) ∧ dist p.2.2 c ≤ δ ^ (12 * η)
  one_le_alpha : 1 ≤ α
  one_le_beta : 1 ≤ β
  alpha_sq_bound : α ^ 2 ≤ δ ^ (-24 * η)
  beta_sq_bound : β ^ 2 ≤ δ ^ (-24 * η)
  product_bound : α * β ≤ δ ^ (-24 * η)
  centerA_norm : ‖zoom 0 α a‖ = 2
  centerC_norm : ‖zoom b β c‖ = 2
  alpha_ball : α * δ ^ (12 * η) ≤ 1 / 100
  beta_ball : β * δ ^ (12 * η) ≤ 1 / 100

/-- Prepare a large, well separated local piece, together with the expanding
similarities and all the cardinality and scale bounds used to return later. -/
theorem exists_localized_model {δ η ε θ : ℝ} (hη : 0 < η)
    (hbudget : LocalizationBudget δ η ε θ) (S T : Finset Plane)
    (hSsq : InUnitSquare (↑S : Set Plane)) (hTsq : InUnitSquare (↑T : Set Plane))
    (hS : FiniteFrostman δ (225 * δ ^ (-4 * η)) S)
    (hT : FiniteFrostman δ (225 * δ ^ (-4 * η)) T)
    (H : Finset Triple) (hH : H ⊆ S ×ˢ (T ×ˢ T)) (hHne : H.Nonempty)
    (hdensity : (δ ^ (4 * η) / (75 : ℝ) ^ 3) * (S.card : ℝ) * (T.card : ℝ) ^ 2 ≤
      (H.card : ℝ)) : Nonempty (LocalizedModel δ η S T H) := by
  have hδ := hbudget.delta_pos
  let r := δ ^ (10 * η)
  let q := δ ^ (12 * η)
  have hr : 0 < r := Real.rpow_pos_of_pos hδ _
  have hq : 0 < q := Real.rpow_pos_of_pos hδ _
  have hq1 : q ≤ 1 := Real.rpow_le_one hδ.le hbudget.delta_le_one (by positivity)
  have hsmall : 4 * (225 * δ ^ (-4 * η)) * r * (S.card : ℝ) * (T.card : ℝ) ^ 2 ≤
      (H.card : ℝ) := by
    calc
      4 * (225 * δ ^ (-4 * η)) * r * (S.card : ℝ) * (T.card : ℝ) ^ 2 ≤
          (δ ^ (4 * η) / (75 : ℝ) ^ 3) * (S.card : ℝ) * (T.card : ℝ) ^ 2 := by
        gcongr
        exact hbudget.degeneracy_bound
      _ ≤ (H.card : ℝ) := hdensity
  obtain ⟨a, b, c, K, haS, hbT, hcT, hKH, hcard, hnear⟩ :=
    exists_localized_separated_triples hSsq hTsq hS hT hbudget.delta_le_separation
      hq hq1 H hH hHne hsmall
  have hKdensity : δ ^ (80 * η) * (S.card : ℝ) * (T.card : ℝ) ^ 2 ≤ (K.card : ℝ) := by
    calc
      δ ^ (80 * η) * (S.card : ℝ) * (T.card : ℝ) ^ 2 ≤
          ((δ ^ (4 * η) / (75 : ℝ) ^ 3) / (2 * (25 / q ^ 2) ^ 3)) *
            (S.card : ℝ) * (T.card : ℝ) ^ 2 := by
        gcongr
        exact hbudget.retained_density
      _ = ((δ ^ (4 * η) / (75 : ℝ) ^ 3) * (S.card : ℝ) * (T.card : ℝ) ^ 2) /
          (2 * (25 / q ^ 2) ^ 3) := by ring
      _ ≤ (H.card : ℝ) / (2 * (25 / q ^ 2) ^ 3) :=
        div_le_div_of_nonneg_right hdensity (by positivity)
      _ ≤ (K.card : ℝ) := hcard
  have hHpos : (0 : ℝ) < H.card := by exact_mod_cast Finset.card_pos.mpr hHne
  have hKpos : (0 : ℝ) < K.card := (by positivity : (0 : ℝ) <
    (H.card : ℝ) / (2 * (25 / q ^ 2) ^ 3)).trans_le hcard
  have hKne : K.Nonempty := Finset.card_pos.mp (by exact_mod_cast hKpos)
  obtain ⟨p, hp⟩ := hKne
  obtain ⟨hpA, hpB, hpC, hpR, hpBC⟩ := hnear p hp
  have hcenters := localized_centers_separated hpA hpB hpC hpR hpBC
  have hqa : 1000 * q ≤ r := hbudget.small_balls
  have ha : r / 2 ≤ ‖a‖ := by nlinarith [hcenters.1]
  have hbc : r / 2 ≤ dist b c := by nlinarith [hcenters.2]
  obtain ⟨α, β, hα, hβ, hαup, hβup, hαa, hβb, hβc, hαq, hβq⟩ :=
    exists_normalizing_zooms hr hq.le hqa ha hbc (hSsq.norm_le_two haS)
      (hTsq.dist_le_two hbT hcT)
  have hα0 : 0 ≤ α := zero_le_one.trans hα
  have hβ0 : 0 ≤ β := zero_le_one.trans hβ
  have hmax : (4 / r) ^ 2 ≤ δ ^ (-24 * η) := by
    calc (4 / r) ^ 2 = 16 / r ^ 2 := by ring
      _ ≤ δ ^ (-24 * η) := hbudget.zoom_bound
  have hαsq : α ^ 2 ≤ δ ^ (-24 * η) := (pow_le_pow_left₀ hα0 hαup 2).trans hmax
  have hβsq : β ^ 2 ≤ δ ^ (-24 * η) := (pow_le_pow_left₀ hβ0 hβup 2).trans hmax
  have hαβ : α * β ≤ δ ^ (-24 * η) := by
    calc α * β ≤ (4 / r) * (4 / r) := mul_le_mul hαup hβup hβ0 (by positivity)
      _ = (4 / r) ^ 2 := (pow_two _).symm
      _ ≤ δ ^ (-24 * η) := hmax
  exact ⟨{
    K := K, a := a, b := b, c := c, α := α, β := β,
    subset := hKH, nonempty := ⟨p, hp⟩, density := hKdensity,
    near := fun p hp => ⟨(hnear p hp).1, (hnear p hp).2.1, (hnear p hp).2.2.1⟩,
    one_le_alpha := hα, one_le_beta := hβ, alpha_sq_bound := hαsq,
    beta_sq_bound := hβsq, product_bound := hαβ, centerA_norm := hαa,
    centerC_norm := hβc, alpha_ball := hαq, beta_ball := hβq }⟩

end WangZahlLot.Obl.wz_separated_projection_dichotomy
