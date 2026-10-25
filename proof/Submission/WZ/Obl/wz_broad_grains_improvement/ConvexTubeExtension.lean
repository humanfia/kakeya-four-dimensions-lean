-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.ConvexTubeExtension.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.Core
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormDiff

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set Metric MeasureTheory
open scoped ENNReal Pointwise
open wz_extremal_lipschitz_grains
  (diffBody enlarge convex_diffBody convex_enlarge smul_mem_smul_diffBody
    add_mem_smul_diffBody)

/-- The accepted open difference-body estimate also controls an arbitrary
convex set with interior. No measurability assumption on the set is needed. -/
theorem volume_diffBody_le_of_interior {W : Set V} (hW : Convex ℝ W)
    (hWi : (interior W).Nonempty) : μ (diffBody W) ≤ 512 * μ W := by
  obtain ⟨z, hz⟩ := hWi
  have hsub : diffBody W ⊆ (2 : ℝ) • diffBody (interior W) := by
    rintro p ⟨p₁, hp₁, p₂, hp₂, rfl⟩
    let q₁ := (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • p₁
    let q₂ := (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • p₂
    have hq₁ : q₁ ∈ interior W := hW.combo_interior_self_mem_interior hz hp₁
      (by norm_num) (by norm_num) (by norm_num)
    have hq₂ : q₂ ∈ interior W := hW.combo_interior_self_mem_interior hz hp₂
      (by norm_num) (by norm_num) (by norm_num)
    exact ⟨q₁ - q₂, ⟨q₁, hq₁, q₂, hq₂, rfl⟩, by dsimp [q₁, q₂]; module⟩
  calc
    μ (diffBody W) ≤ μ ((2 : ℝ) • diffBody (interior W)) := measure_mono hsub
    _ = 8 * μ (diffBody (interior W)) := by
      simp only [μ, Measure.addHaar_smul, finrank_euclideanSpace_fin]
      norm_num
    _ ≤ 8 * (64 * μ (interior W)) := mul_le_mul' le_rfl
      (wz_extremal_lipschitz_grains.volume_diffBody_le isOpen_interior hW.interior)
    _ ≤ 512 * μ W := by
      calc
        _ = 512 * μ (interior W) := by rw [← mul_assoc]; norm_num
        _ ≤ _ := mul_le_mul' le_rfl (measure_mono interior_subset)

theorem volume_convex_enlarge_le {W : Set V} (hW : Convex ℝ W)
    (hWi : (interior W).Nonempty) (z : V) {r : ℝ} (hr : 0 ≤ r) :
    μ (enlarge z r W) ≤ O (512 * r ^ 3) * μ W := by
  rw [enlarge, Set.image_add_left, μ, measure_preimage_add,
    Measure.addHaar_smul, finrank_euclideanSpace_fin,
    abs_of_nonneg (by positivity)]
  calc
    _ ≤ O (r ^ 3) * (512 * μ W) := mul_le_mul' le_rfl
      (volume_diffBody_le_of_interior hW hWi)
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_ofNat 512,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring

private theorem smul_diffBody_mono {W : Set V} (hW : Convex ℝ W)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a • diffBody W ⊆ b • diffBody W := by
  rintro p ⟨q, hq, rfl⟩
  exact smul_mem_smul_diffBody hW hq (by simpa [abs_of_nonneg ha] using hab)

private theorem error_mem_four_diffBody {W : Set V} {δ : ℝ} {z u : V}
    (hδ : 0 < δ) (hball : ball z (δ / 2) ⊆ W) (hu : ‖u‖ < 2 * δ) :
    u ∈ (4 : ℝ) • diffBody W := by
  have hz : z ∈ W := hball (mem_ball_self (by positivity))
  have hzu : z + (1 / 4 : ℝ) • u ∈ W := by
    apply hball
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs]
    norm_num
    linarith
  exact ⟨(1 / 4 : ℝ) • u, ⟨_, hzu, z, hz, by abel⟩, by
    change (4 : ℝ) • (1 / 4 : ℝ) • u = u
    rw [smul_smul]; norm_num⟩

/-- A unit tube with two well-separated contacts in a convex set lies in a
controlled difference-body enlargement. The set only needs a ball of radius
half the tube radius; the contacts need not lie on its boundary. -/
theorem tube_subset_convex_enlarge_of_contacts {W : Set V} {δ c : ℝ}
    {x v z z₀ p₀ p₁ : V} (hW : Convex ℝ W) (hδ : 0 < δ)
    (h4 : 4 * δ ≤ c) (hc1 : c ≤ 1) (hv : ‖v‖ = 1)
    (hball : ball z (δ / 2) ⊆ W) (hz₀ : z₀ ∈ W)
    (hp₀ : p₀ ∈ T δ x v ∩ W) (hp₁ : p₁ ∈ T δ x v ∩ W)
    (hsep : c ≤ dist p₀ p₁) : T δ x v ⊆ enlarge z₀ (15 / c) W := by
  have hc : 0 < c := by linarith
  obtain ⟨t₀, ht₀, hu₀⟩ := wz_extremal_lipschitz_grains.mem_tube_iff.mp hp₀.1
  obtain ⟨t₁, ht₁, hu₁⟩ := wz_extremal_lipschitz_grains.mem_tube_iff.mp hp₁.1
  let u₀ := p₀ - (x + t₀ • v)
  let u₁ := p₁ - (x + t₁ • v)
  have hdt : c / 2 ≤ |t₁ - t₀| := by
    have he : p₁ - p₀ = (t₁ - t₀) • v + (u₁ - u₀) := by
      dsimp [u₀, u₁]; module
    have hdist : dist p₀ p₁ ≤ |t₁ - t₀| + ‖u₁‖ + ‖u₀‖ := by
      rw [dist_comm, dist_eq_norm, he]
      calc
        _ ≤ ‖(t₁ - t₀) • v‖ + ‖u₁ - u₀‖ := norm_add_le _ _
        _ ≤ _ := by rw [norm_smul, hv, mul_one, Real.norm_eq_abs];
                    linarith [norm_sub_le u₁ u₀]
    change ‖u₀‖ < δ at hu₀
    change ‖u₁‖ < δ at hu₁
    linarith
  have hdtpos : 0 < |t₁ - t₀| := by linarith
  have hdtne : t₁ - t₀ ≠ 0 := abs_pos.mp hdtpos
  have hdiff : p₁ - p₀ ∈ diffBody W := ⟨p₁, hp₁.2, p₀, hp₀.2, rfl⟩
  intro p hp
  obtain ⟨t, ht, hu⟩ := wz_extremal_lipschitz_grains.mem_tube_iff.mp hp
  let u := p - (x + t • v)
  let s := (t - t₀) / (t₁ - t₀)
  have htnum : |t - t₀| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2, ht₀.1, ht₀.2]
  have hs : |s| ≤ 2 / c := by
    dsimp [s]
    rw [abs_div, div_le_div_iff₀ hdtpos hc]
    nlinarith
  have hfirst : p₀ - z₀ ∈ (1 : ℝ) • diffBody W := by
    simpa using (show p₀ - z₀ ∈ diffBody W from ⟨p₀, hp₀.2, z₀, hz₀, rfl⟩)
  have hsecond : s • (p₁ - p₀) ∈ (2 / c) • diffBody W :=
    smul_mem_smul_diffBody hW hdiff hs
  have herr₀ : u - u₀ ∈ (4 : ℝ) • diffBody W :=
    error_mem_four_diffBody hδ hball (by
      have hh := norm_sub_le u u₀
      change ‖u‖ < δ at hu
      change ‖u₀‖ < δ at hu₀
      linarith)
  have herr₁ : u₁ - u₀ ∈ (4 : ℝ) • diffBody W :=
    error_mem_four_diffBody hδ hball (by
      have hh := norm_sub_le u₁ u₀
      change ‖u₁‖ < δ at hu₁
      change ‖u₀‖ < δ at hu₀
      linarith)
  have hthird : (-s) • (u₁ - u₀) ∈ (8 / c) • diffBody W := by
    obtain ⟨q, hq, heq⟩ := herr₁
    rw [← heq, smul_smul]
    apply smul_mem_smul_diffBody hW hq
    rw [abs_mul, abs_neg]
    norm_num
    simp only [div_eq_mul_inv] at hs ⊢
    linarith
  have hsum := add_mem_smul_diffBody hW (by positivity) (by positivity)
    (add_mem_smul_diffBody hW (by positivity) (by positivity)
      (add_mem_smul_diffBody hW (by norm_num) (by positivity) hfirst hsecond) herr₀) hthird
  have he : p₀ - z₀ + s • (p₁ - p₀) + (u - u₀) + (-s) • (u₁ - u₀) =
      p - z₀ := by
    have hsdt : s * (t₁ - t₀) = t - t₀ := by
      dsimp [s]; exact div_mul_cancel₀ _ hdtne
    calc
      _ = p - z₀ + (s * (t₁ - t₀) - (t - t₀)) • v := by
        dsimp only [u, u₀, u₁]
        module
      _ = _ := by rw [hsdt, sub_self, zero_smul, add_zero]
  rw [he] at hsum
  refine ⟨p - z₀, smul_diffBody_mono hW (by positivity) ?_ hsum, by abel⟩
  have hcinv : 1 ≤ 1 / c := (le_div_iff₀ hc).mpr (by simpa using hc1)
  simp only [div_eq_mul_inv, one_mul] at hcinv ⊢
  linarith

end WangZahlLot.Obl.wz_broad_grains_improvement
