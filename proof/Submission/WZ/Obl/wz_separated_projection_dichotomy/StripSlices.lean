-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.StripSlices.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.RadiusTransfer
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CoverCounting
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Anisotropic
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Strips
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Packing

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

/-- Pigeonhole a narrow strip inside a containing strip. Half-radius closed
intervals give strict membership in the requested open strip. -/
theorem exists_dense_strip_slice {S : Finset Plane} (hne : S.Nonempty)
    {δ W c : ℝ} {e : Plane} (hδ : 0 < δ) (hδW : δ ≤ W)
    (hstrip : ∀ x ∈ S, |inner ℝ x e - c| ≤ W) :
    ∃ (c' : ℝ) (T : Finset Plane), T ⊆ S ∧
      (∀ x ∈ T, |inner ℝ x e - c'| < δ) ∧
      δ / (6 * W) * (S.card : ℝ) ≤ (T.card : ℝ) := by
  classical
  have hW : 0 < W := hδ.trans_le hδW
  obtain ⟨m, hm, hcover⟩ := real_closedBall_radius_cover (by positivity : 0 < δ / 2) (by linarith : δ / 2 ≤ W)
  obtain ⟨cc, hcc⟩ := hcover c
  have hcov : Covers (δ / 2) ((fun x => inner ℝ x e) '' (↑S : Set Plane)) cc := by
    rintro t ⟨x, hx, rfl⟩
    apply hcc
    simpa only [Metric.mem_closedBall, Real.dist_eq] using hstrip x hx
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨j₀, hj₀⟩ := Set.mem_iUnion.mp (hcov ⟨x₀, hx₀, rfl⟩)
  let T (j : Fin m) := S.filter (fun x => dist (inner ℝ x e) (cc j) ≤ δ / 2)
  obtain ⟨j, hj, hmax⟩ := Finset.univ.exists_max_image (fun j : Fin m => (T j).card) ⟨j₀, Finset.mem_univ _⟩
  have hcard : (S.card : ℝ) ≤ (m : ℝ) * ((T j).card : ℝ) :=
    card_le_cover_mul_fiber_bound S (fun x => inner ℝ x e) hcov
      (fun k => by exact_mod_cast hmax k (Finset.mem_univ _))
  refine ⟨cc j, T j, Finset.filter_subset _ _, ?_, ?_⟩
  · intro x hx
    have hh := (Finset.mem_filter.mp hx).2
    rw [Real.dist_eq] at hh
    linarith
  · have hm' : (m : ℝ) ≤ 6 * W / δ := by convert hm using 1 <;> ring
    have hc : (S.card : ℝ) ≤ (6 * W / δ) * ((T j).card : ℝ) :=
      hcard.trans (mul_le_mul_of_nonneg_right hm' (Nat.cast_nonneg _))
    apply (mul_le_mul_iff_left₀ (by positivity : 0 < 6 * W)).mp
    calc (δ / (6 * W) * (S.card : ℝ)) * (6 * W) = δ * (S.card : ℝ) := by field_simp
      _ ≤ (T j).card * (6 * W) := by
        have hh := mul_le_mul_of_nonneg_left hc hδ.le
        field_simp at hh
        nlinarith

theorem perpendicular_hyperplane_eq_line {e : Plane} (he : ‖e‖ = 1) (c : ℝ) :
    {x : Plane | inner ℝ x (perp e) = c} = Set.range (fun t : ℝ => c • perp e + t • e) := by
  ext x
  constructor
  · intro hx
    refine ⟨inner ℝ x e, ?_⟩
    have h := unit_inner_decomposition he x
    rw [hx] at h
    simpa only [add_comm] using h
  · rintro ⟨t, rfl⟩
    have hpp : inner ℝ (perp e) (perp e) = 1 := by
      rw [real_inner_self_eq_norm_sq, perp_norm, he]; norm_num
    simp only [Set.mem_setOf_eq, inner_add_left, real_inner_smul_left, hpp, perp_inner,
      mul_one, mul_zero, add_zero]

theorem line_conclusion_of_strip_cardinals {F G : Finset Plane} {δ ε W c : ℝ} {e : Plane}
    (hFne : F.Nonempty) (hGne : G.Nonempty) (hδ : 0 < δ) (hδW : δ ≤ W) (he : ‖e‖ = 1)
    (hFsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → δ ≤ dist x y)
    (hGsep : ∀ x ∈ G, ∀ y ∈ G, x ≠ y → δ ≤ dist x y)
    (hFstrip : ∀ a ∈ F, |inner ℝ a e| ≤ W)
    (hGstrip : ∀ b ∈ G, |inner ℝ b (perp e) - c| ≤ W)
    (hFcard : δ ^ (ε - 1) ≤ δ / (150 * W) * (F.card : ℝ))
    (hGcard : δ ^ (ε - 1) ≤ δ / (150 * W) * (G.card : ℝ)) :
    LineConclusion δ ε (↑F : Set Plane) (↑G : Set Plane) := by
  classical
  obtain ⟨c₁, F', hF', hF'strip, hF'card⟩ := exists_dense_strip_slice hFne hδ hδW
    (c := 0) (by simpa only [sub_zero] using hFstrip)
  obtain ⟨c₂, G', hG', hG'strip, hG'card⟩ := exists_dense_strip_slice hGne hδ hδW hGstrip
  have hFc := coverLower_of_separated hδ F' (fun x hx y hy hxy => hFsep x (hF' hx) y (hF' hy) hxy)
  have hGc := coverLower_of_separated hδ G' (fun x hx y hy hxy => hGsep x (hG' hx) y (hG' hy) hxy)
  refine ⟨e, c₂ • perp e, c₁, he, ?_, ?_⟩
  · apply (hFc.weaken (show δ ^ (ε - 1) ≤ (F'.card : ℝ) / 25 by
      have hh : δ / (150 * W) * (F.card : ℝ) = (δ / (6 * W) * (F.card : ℝ)) / 25 := by ring
      rw [hh] at hFcard
      linarith)).mono_set
    intro a ha
    refine ⟨?_, hF' ha⟩
    rw [thickening_hyperplane_eq_strip he]
    exact hF'strip a ha
  · apply (hGc.weaken (show δ ^ (ε - 1) ≤ (G'.card : ℝ) / 25 by
      have hh : δ / (150 * W) * (G.card : ℝ) = (δ / (6 * W) * (G.card : ℝ)) / 25 := by ring
      rw [hh] at hGcard
      linarith)).mono_set
    intro b hb
    refine ⟨?_, hG' hb⟩
    rw [← perpendicular_hyperplane_eq_line he, thickening_hyperplane_eq_strip ((perp_norm e).trans he)]
    exact hG'strip b hb

end WangZahlLot.Obl.wz_separated_projection_dichotomy
