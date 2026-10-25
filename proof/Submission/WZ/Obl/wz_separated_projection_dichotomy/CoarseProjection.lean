-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.CoarseProjection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CoarseTripleModel
import Submission.WZ.Obl.wz_separated_projection_dichotomy.RadiusTransfer
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Quantization

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

/-- Quantified stability of cover lower bounds under bounded perturbation. -/
theorem CoverLower.transfer_close_mul {r N L : ℝ} {S T : Set ℝ}
    (h : CoverLower r S N) (hr : 0 < r) (hL : 0 ≤ L)
    (hclose : ∀ x ∈ S, ∃ y ∈ T, dist x y ≤ L * r) :
    CoverLower r T (N / (3 * (L + 1))) := by
  intro m cc hc
  have hbig : Covers ((L + 1) * r) S cc := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hclose x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hc hy)
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    change dist x (cc i) ≤ (L + 1) * r
    have hiy : dist y (cc i) ≤ r := hi
    have ht := dist_triangle x y (cc i)
    nlinarith
  obtain ⟨n, dd, hdd, hn⟩ := hbig.refine_radius hr (by nlinarith)
  have hN := h n dd hdd
  apply (div_le_iff₀ (by positivity : 0 < 3 * (L + 1))).mpr
  calc N ≤ (m : ℝ) * (3 * (((L + 1) * r) / r)) := hN.trans hn
    _ = _ := by field_simp

/-- The dot-product map is Lipschitz on a bounded product of plane sets. -/
theorem dotValue_sub_le_of_norm {p q : Triple} {R : ℝ}
    (hR : 0 ≤ R) (hp₁ : ‖p.2.1‖ ≤ R) (hp₂ : ‖p.2.2‖ ≤ R) (hq : ‖q.1‖ ≤ R) :
    |dotValue p - dotValue q| ≤ 4 * R * dist p q := by
  have ha : ‖p.1 - q.1‖ ≤ dist p q := by rw [← dist_eq_norm]; exact le_max_left _ _
  have hb : ‖p.2.1 - q.2.1‖ ≤ dist p q := by
    rw [← dist_eq_norm]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hc : ‖p.2.2 - q.2.2‖ ≤ dist p q := by
    rw [← dist_eq_norm]
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hd : ‖p.2.1 - p.2.2‖ ≤ 2 * R := (norm_sub_le _ _).trans (by linarith)
  have he : ‖(p.2.1 - q.2.1) - (p.2.2 - q.2.2)‖ ≤ 2 * dist p q :=
    (norm_sub_le _ _).trans (by linarith)
  have hid : dotValue p - dotValue q =
      inner ℝ (p.1 - q.1) (p.2.1 - p.2.2) +
        inner ℝ q.1 ((p.2.1 - q.2.1) - (p.2.2 - q.2.2)) := by
    simp only [dotValue, inner_sub_left, inner_sub_right]
    ring
  rw [hid]
  calc _ ≤ |inner ℝ (p.1 - q.1) (p.2.1 - p.2.2)| +
        |inner ℝ q.1 ((p.2.1 - q.2.1) - (p.2.2 - q.2.2))| := abs_add_le _ _
    _ ≤ ‖p.1 - q.1‖ * ‖p.2.1 - p.2.2‖ +
        ‖q.1‖ * ‖(p.2.1 - q.2.1) - (p.2.2 - q.2.2)‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ dist p q * (2 * R) + R * (2 * dist p q) := by gcongr
    _ = _ := by ring

/-- Projection lower bounds for the coarse model pass to the original
hypergraph at the same radius with an explicit absolute loss. -/
theorem CoarseTripleData.transfer_dot_cover {δ C D ζ d R N : ℝ}
    {F G U : Finset Plane} {H : Finset Triple}
    (model : CoarseTripleData δ C D ζ d F G U H)
    (hδ : 0 < δ) (hR : 0 ≤ R)
    (hFn : ∀ x ∈ F, ‖x‖ ≤ R) (hGn : ∀ x ∈ G, ‖x‖ ≤ R) (hUn : ∀ x ∈ U, ‖x‖ ≤ R)
    (hH : H ⊆ F ×ˢ (G ×ˢ U))
    (hcov : CoverLower δ (DotSet (↑model.edges : Set Triple)) N) :
    CoverLower δ (DotSet (↑H : Set Triple)) (N / (3 * (4 * R + 1))) := by
  apply hcov.transfer_close_mul hδ (by positivity : 0 ≤ 4 * R)
  rintro t ⟨q, hq, rfl⟩
  obtain ⟨p, hp, hpq⟩ := model.approximates q hq
  have hpF := Finset.mem_product.mp (hH hp)
  have hpG := Finset.mem_product.mp hpF.2
  have hqF := Finset.mem_product.mp (model.contained hq)
  refine ⟨dotValue p, ⟨p, hp, rfl⟩, ?_⟩
  have hh := dotValue_sub_le_of_norm hR (hGn p.2.1 hpG.1) (hUn p.2.2 hpG.2)
    (hFn q.1 (model.first_subset hqF.1))
  rw [Real.dist_eq, abs_sub_comm]
  exact hh.trans (mul_le_mul_of_nonneg_left hpq (by positivity))

end WangZahlLot.Obl.wz_separated_projection_dichotomy
