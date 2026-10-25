-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.ZoomFrostman.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Zoom

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

theorem ballCount_mono_radius (S : Finset Plane) (x : Plane) {r R : ℝ} (hrR : r ≤ R) :
    ballCount S x r ≤ ballCount S x R := by
  classical
  apply Finset.card_le_card
  intro y hy
  obtain ⟨hyS, hyr⟩ := Finset.mem_filter.mp hy
  exact Finset.mem_filter.mpr ⟨hyS, Metric.ball_subset_ball hrR hyr⟩

theorem ballCount_zoom (S : Finset Plane) (b : Plane) {k : ℝ} (hk : 0 < k)
    (x : Plane) (r : ℝ) :
    ballCount (S.image (zoom b k)) x r = ballCount S (b + k⁻¹ • x) (r / k) := by
  classical
  have hfilter : (S.image (zoom b k)).filter (fun y => y ∈ Metric.ball x r) =
      (S.filter (fun y => y ∈ Metric.ball (b + k⁻¹ • x) (r / k))).image (zoom b k) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hzb⟩
      exact ⟨z, ⟨hz, (zoom_mem_ball b hk x z r).mp hzb⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzb⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, (zoom_mem_ball b hk x z r).mpr hzb⟩
  dsimp [ballCount]
  rw [hfilter, Finset.card_image_of_injective _ (zoom_injective b hk)]

/-- An expanding similarity preserves the original scale Frostman bound:
preimages of radius-r balls lie in radius-r balls. -/
theorem FiniteFrostman.map_expanding_zoom {δ C k : ℝ} {S : Finset Plane}
    (h : FiniteFrostman δ C S) (hδ : 0 ≤ δ) (b : Plane) (hk : 1 ≤ k) :
    FiniteFrostman δ C (S.image (zoom b k)) := by
  classical
  intro x r hδr
  have hkpos : 0 < k := zero_lt_one.trans_le hk
  have hr : 0 ≤ r := hδ.trans hδr
  have hrk : r / k ≤ r := (div_le_iff₀ hkpos).mpr (by nlinarith)
  rw [ballCount_zoom S b hkpos, Finset.card_image_of_injective _ (zoom_injective b hkpos)]
  have hcount : (ballCount S (b + k⁻¹ • x) (r / k) : ℝ) ≤
      ballCount S (b + k⁻¹ • x) r := by
    exact_mod_cast ballCount_mono_radius S (b + k⁻¹ • x) hrk
  exact hcount.trans (h _ _ hδr)

theorem separated_map_expanding_zoom {δ k : ℝ} (S : Finset Plane) (b : Plane)
    (hk : 1 ≤ k) (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y) :
    ∀ x ∈ S.image (zoom b k), ∀ y ∈ S.image (zoom b k), x ≠ y → δ ≤ dist x y := by
  classical
  rintro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hy
  rw [zoom_dist b (zero_le_one.trans hk)]
  have hac : a ≠ c := fun h => hxy (congrArg (zoom b k) h)
  exact (hsep a ha c hc hac).trans (by nlinarith [dist_nonneg (x := a) (y := c)])

end WangZahlLot.Obl.wz_separated_projection_dichotomy
