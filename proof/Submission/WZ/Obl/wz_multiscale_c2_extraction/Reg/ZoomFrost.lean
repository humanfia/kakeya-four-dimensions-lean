-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.ZoomFrost.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.ZoomCover
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Enclosure

/-!
# Convex counts of zoomed pieces

A convex set containing a zoomed piece lies, inside the unit ball, in a prism of volume at
most `512` times its volume (accepted o064).  Every old tube whose piece lies in the convex set
lies in a fixed box of volume at most `432 · 512` times the volume of the convex set.
-/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

abbrev Frame := WangZahlLot.Obl.wz_concentrated_convex_factorization.Frame

/-- A box adapted to an orthonormal frame. -/
def frameBox (b : Frame) (z : Space) (A₀ A₁ A₂ : ℝ) : Set Space :=
  {p | |⟪b 0, p - z⟫| ≤ A₀ ∧ |⟪b 1, p - z⟫| ≤ A₁ ∧ |⟪b 2, p - z⟫| ≤ A₂}

theorem frameBox_volume (b : Frame) (z : Space) {A₀ A₁ A₂ : ℝ} (h₀ : 0 ≤ A₀) (h₁ : 0 ≤ A₁) : volume (frameBox b z A₀ A₁ A₂) = ENNReal.ofReal (8 * A₀ * A₁ * A₂) := by
  let d : Fin 3 → ℝ := ![A₀, A₁, A₂]
  have he : frameBox b z A₀ A₁ A₂ = {p : Space | ∀ i, -d i ≤ b.repr (p - z) i ∧
      b.repr (p - z) i ≤ d i} := by
    ext p
    simp only [frameBox, mem_ofPred_eq, OrthonormalBasis.repr_apply_apply]
    constructor
    · rintro ⟨g₀, g₁, g₂⟩ i
      fin_cases i
      · exact abs_le.mp g₀
      · exact abs_le.mp g₁
      · exact abs_le.mp g₂
    · intro h
      exact ⟨abs_le.mpr (h 0), abs_le.mpr (h 1), abs_le.mpr (h 2)⟩
  rw [he, WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.coordinate_box_volume]
  simp only [Fin.prod_univ_three]
  change ENNReal.ofReal (A₀ - -A₀) * ENNReal.ofReal (A₁ - -A₁) *
    ENNReal.ofReal (A₂ - -A₂) = _
  simp only [sub_neg_eq_add]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem frameBox_convex (b : Frame) (z : Space) (A₀ A₁ A₂ : ℝ) :
    Convex ℝ (frameBox b z A₀ A₁ A₂) := by
  have hc' (i : Fin 3) (r : ℝ) : Convex ℝ {p : Space | |⟪b i, p - z⟫| ≤ r} := by
    have he : {p : Space | |⟪b i, p - z⟫| ≤ r} =
        {p | -r + ⟪b i, z⟫ ≤ ⟪b i, p⟫} ∩ {p | ⟪b i, p⟫ ≤ r + ⟪b i, z⟫} := by
      ext p
      simp only [mem_ofPred_eq, mem_inter_iff, inner_sub_right, abs_le]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    rw [he]
    exact (convex_halfSpace_ge (innerSL ℝ (b i)).toLinearMap.isLinear _).inter
      (convex_halfSpace_le (innerSL ℝ (b i)).toLinearMap.isLinear _)
  exact (hc' 0 A₀).inter ((hc' 1 A₁).inter (hc' 2 A₂))

/-- An affine function of one variable bounded at `0` and `1`. -/
theorem affine_bound_01 {α β μ W : ℝ} (h₀ : |α| ≤ W) (h₁ : |α + β| ≤ W) :
    |α + μ * β| ≤ (|1 - μ| + |μ|) * W := by
  have he : α + μ * β = (1 - μ) * α + μ * (α + β) := by ring
  rw [he]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have hW : 0 ≤ W := (abs_nonneg _).trans h₀
  nlinarith [abs_nonneg (1 - μ), abs_nonneg μ]

/-- Old tubes whose zoomed pieces lie in a convex set lie in a common box of comparable
volume. -/
theorem old_tubes_in_box {r δ : ℝ} (hr : 16 ≤ r) (hδ : 0 < δ) (hrδ : r * δ ≤ 1 / 8)
    {c : Space} {W : Set Space} (hW : Convex ℝ W) (hWfin : volume W ≠ ⊤)
    {x₀ v₀ : Space} (hv₀ : ‖v₀‖ = 1) (hn₀ : FNear r c x₀ v₀) (h₀ : fpiece r δ c x₀ v₀ ⊆ W) :
    ∃ B : Set Space, Convex ℝ B ∧
      volume B ≤ ENNReal.ofReal (432 * 512) * volume W ∧
      ∀ x v : Space, ‖v‖ = 1 → FNear r c x v → fpiece r δ c x v ⊆ W → Tube δ x v ⊆ B := by
  have hr0 : 0 < r := by linarith
  have hrδ0 : 0 < r * δ := mul_pos hr0 hδ
  have hball : ∀ x v : Space, ‖v‖ = 1 → FNear r c x v → fpiece r δ c x v ⊆ ball 0 1 := by
    intro x v hv hn
    apply piece_subset_ball hv _ (by linarith)
    rw [show zoom r c (cpt c x v) = r • (cpt c x v - c) from rfl, norm_smul,
      Real.norm_of_nonneg hr0.le]
    calc r * ‖cpt c x v - c‖ ≤ r * (1 / (8 * r)) := mul_le_mul_of_nonneg_left hn.1 hr0.le
      _ ≤ 1 / 4 := by rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith
  obtain ⟨b, a, c', hδa, hac, hc2, hsub, hvol⟩ :=
    WangZahlLot.Obl.wz_concentrated_convex_factorization.enclose_convex hrδ0 (by linarith)
      hW hWfin hv₀ (fun p hp => ⟨h₀ hp, hball x₀ v₀ hv₀ hn₀ hp⟩)
  set X₀ := pieceBase r c x₀ v₀
  have ha0 : 0 ≤ a := hrδ0.le.trans hδa
  refine ⟨frameBox b (c + r⁻¹ • X₀) 6 (3 * c') (3 * a), frameBox_convex _ _ _ _ _, ?_, ?_⟩
  · rw [frameBox_volume _ _ (by norm_num) (by linarith)]
    have hv' : ENNReal.ofReal (a * c') ≤ ENNReal.ofReal 512 * volume W := by
      rw [← ENNReal.ofReal_toReal hWfin, ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal hvol
    calc ENNReal.ofReal (8 * 6 * (3 * c') * (3 * a)) = ENNReal.ofReal 432 *
          ENNReal.ofReal (a * c') := by
          rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
      _ ≤ ENNReal.ofReal 432 * (ENNReal.ofReal 512 * volume W) := by gcongr
      _ = ENNReal.ofReal (432 * 512) * volume W := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
  · intro x v hv hn hW'
    have hpr : fpiece r δ c x v ⊆ WangZahlLot.Obl.wz_concentrated_convex_factorization.prism b X₀ a c' := fun p hp => hsub ⟨hW' hp, hball x v hv hn hp⟩
    set Xb := pieceBase r c x v
    have hend₀ : Xb ∈ WangZahlLot.Obl.wz_concentrated_convex_factorization.prism b X₀ a c' :=
      hpr (self_subset_thickening hrδ0 _ (left_mem_segment ℝ Xb (Xb + v)))
    have hend₁ : Xb + v ∈ WangZahlLot.Obl.wz_concentrated_convex_factorization.prism b X₀ a c' :=
      hpr (self_subset_thickening hrδ0 _ (right_mem_segment ℝ Xb (Xb + v)))
    intro p hp
    obtain ⟨t, ht, hpt⟩ := exists_param_of_mem_tube' hp
    set μ := r * (t - cpar c x v) + 1 / 2
    have hzoom : zoom r c p = Xb + μ • v + r • (p - (x + t • v)) := by
      simp only [Xb, μ, pieceBase, zoom, cpt]; module
    have hμ : |1 - μ| + |μ| ≤ 2 * r + 3 := by
      have h1 : |t - cpar c x v| ≤ 1 + 1 / (8 * r) := by
        rw [abs_le]; constructor <;> linarith [ht.1, ht.2, hn.2.1, hn.2.2]
      have h2 : |μ - 1 / 2| ≤ r + 1 := by
        rw [show μ - 1 / 2 = r * (t - cpar c x v) by simp only [μ]; ring, abs_mul,
          abs_of_pos hr0]
        calc r * |t - cpar c x v| ≤ r * (1 + 1 / (8 * r)) := mul_le_mul_of_nonneg_left h1 hr0.le
          _ = r + 1 / 8 := by field_simp
          _ ≤ r + 1 := by linarith
      calc |1 - μ| + |μ| ≤ (|μ - 1 / 2| + 1 / 2) + (|μ - 1 / 2| + 1 / 2) := by
            gcongr
            · calc |1 - μ| = |-(μ - 1 / 2) + 1 / 2| := by ring_nf
                _ ≤ |-(μ - 1 / 2)| + |(1 / 2 : ℝ)| := abs_add_le _ _
                _ = |μ - 1 / 2| + 1 / 2 := by rw [abs_neg]; norm_num
            · calc |μ| = |(μ - 1 / 2) + 1 / 2| := by ring_nf
                _ ≤ |μ - 1 / 2| + |(1 / 2 : ℝ)| := abs_add_le _ _
                _ = |μ - 1 / 2| + 1 / 2 := by norm_num
        _ ≤ 2 * r + 3 := by linarith
    have he_small : ‖r • (p - (x + t • v))‖ ≤ r * δ := by
      rw [norm_smul, Real.norm_of_nonneg hr0.le]
      exact mul_le_mul_of_nonneg_left hpt.le hr0.le
    have hkey : ∀ (k : Fin 3) (A : ℝ), |⟪b k, Xb - X₀⟫| ≤ A → |⟪b k, Xb + v - X₀⟫| ≤ A →
        r * δ ≤ A → |⟪b k, p - (c + r⁻¹ • X₀)⟫| ≤ 3 * A := by
      intro k A hA₀ hA₁ hδA
      have hA : 0 ≤ A := (abs_nonneg _).trans hA₀
      have hrel : ⟪b k, p - (c + r⁻¹ • X₀)⟫ = r⁻¹ * ⟪b k, zoom r c p - X₀⟫ := by
        rw [← inner_smul_right]
        congr 1
        simp only [zoom, smul_sub, smul_smul, inv_mul_cancel₀ hr0.ne', one_smul]
        abel
      rw [hrel, hzoom]
      have hsplit : ⟪b k, Xb + μ • v + r • (p - (x + t • v)) - X₀⟫ =
          (⟪b k, Xb - X₀⟫ + μ * ⟪b k, v⟫) + ⟪b k, r • (p - (x + t • v))⟫ := by
        rw [show Xb + μ • v + r • (p - (x + t • v)) - X₀ =
          (Xb - X₀) + μ • v + r • (p - (x + t • v)) by abel, inner_add_right, inner_add_right,
          inner_smul_right]
      rw [hsplit]
      have hb1 : |⟪b k, Xb - X₀⟫ + μ * ⟪b k, v⟫| ≤ (2 * r + 3) * A := by
        have hA₁' : |⟪b k, Xb - X₀⟫ + ⟪b k, v⟫| ≤ A := by
          rwa [← inner_add_right, show Xb - X₀ + v = Xb + v - X₀ by abel]
        exact (affine_bound_01 hA₀ hA₁').trans (mul_le_mul_of_nonneg_right hμ hA)
      have hb2 : |⟪b k, r • (p - (x + t • v))⟫| ≤ A := by
        refine (abs_real_inner_le_norm _ _).trans ?_
        rw [b.norm_eq_one, one_mul]; linarith
      rw [abs_mul, abs_inv, abs_of_pos hr0, inv_mul_le_iff₀ hr0]
      calc |⟪b k, Xb - X₀⟫ + μ * ⟪b k, v⟫ + ⟪b k, r • (p - (x + t • v))⟫|
          ≤ (2 * r + 3) * A + A := (abs_add_le _ _).trans (add_le_add hb1 hb2)
        _ ≤ r * (3 * A) := by nlinarith
    obtain ⟨e0, e1, e2⟩ := hend₀
    obtain ⟨f0, f1, f2⟩ := hend₁
    refine ⟨?_, ?_, ?_⟩
    · have := hkey 0 2 e0 f0 (by linarith)
      linarith
    · exact hkey 1 c' e1 f1 (by linarith)
    · exact hkey 2 a e2 f2 hδa

end

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
