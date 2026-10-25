-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.RobustTransversality.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Basic
import Submission.WZ.Obl.wz_balanced_cluster_cover
import Submission.WZ.Obl.wz_direction_density_transfer

/-!
# Robust transversality from separated covers (sticky Lemma 3.4)

A fine tube inside a coarse tube of radius `ρ` has direction within `4ρ` of it; a fine tube
through a point of it with direction within `3ρ` lies in the coarse tube's tenfold dilate
(`subset_dilatedTube_of_cone`).  With the separation property of `Separated`, all shading-tubes
through a point in a cone of width `ρ` lie in one fibre, so `cone_count_le` bounds them by the
fibre multiplicity.
-/

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal

theorem tube_param {δ : ℝ} {x v q : Space} (h : q ∈ tube δ x v) :
    ∃ t ∈ Icc (0 : ℝ) 1, ‖q - (x + t • v)‖ < δ :=
  WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube h

theorem start_mem_tube {δ : ℝ} (hδ : 0 < δ) (x v : Space) : x ∈ tube δ x v :=
  self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v))

theorem end_mem_tube {δ : ℝ} (hδ : 0 < δ) (x v : Space) : x + v ∈ tube δ x v :=
  self_subset_thickening hδ _ (right_mem_segment ℝ x (x + v))

/-- A unit fine tube inside a unit coarse tube of radius `ρ` has direction within `4 ρ` of the
coarse direction, up to sign. -/
theorem direction_close_of_subset {δ ρ : ℝ} (hδ : 0 < δ) {x v z w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hT : tube δ x v ⊆ tube ρ z w) :
    min ‖v - w‖ ‖v + w‖ ≤ 4 * ρ := by
  obtain ⟨a, _, ha⟩ := tube_param (hT (start_mem_tube hδ x v))
  obtain ⟨b, _, hb⟩ := tube_param (hT (end_mem_tube hδ x v))
  have hn : ‖v - (b - a) • w‖ < 2 * ρ := by
    have he : v - (b - a) • w = (x + v - (z + b • w)) - (x - (z + a • w)) := by module
    rw [he]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  by_contra hcon
  push Not at hcon
  have h1 : 4 * ρ < ‖v - w‖ := lt_of_lt_of_le hcon (min_le_left _ _)
  have h2 : 4 * ρ < ‖v + w‖ := lt_of_lt_of_le hcon (min_le_right _ _)
  have hd := WangZahlLot.Obl.wz_direction_density_transfer.scale_sep
    (a := 1) (b := b - a) hv hw h1.le h2.le
  simp only [abs_one, mul_one, one_smul] at hd
  linarith

/-- A fine tube through a point of a fine tube of a coarse tube, with nearly the same direction,
lies in the tenfold dilate of the coarse tube. -/
theorem subset_dilatedTube_of_cone {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    {x v z w y u p : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    (hT : tube δ x v ⊆ tube ρ z w) (hp : p ∈ tube δ x v) (hp' : p ∈ tube δ y u)
    (hcone : min ‖u - v‖ ‖u + v‖ ≤ 3 * ρ) : tube δ y u ⊆ dilatedTube ρ z w := by
  have hvw := direction_close_of_subset hδ hv hw hT
  obtain ⟨c, hc, hpc⟩ := tube_param (hT hp)
  obtain ⟨tp, htp, hptp⟩ := tube_param hp'
  -- signs
  obtain ⟨σ, hσ, hσu⟩ : ∃ σ : ℝ, |σ| = 1 ∧ ‖u - σ • v‖ ≤ 3 * ρ := by
    rcases le_total ‖u - v‖ ‖u + v‖ with h | h
    · exact ⟨1, by norm_num, by rw [one_smul]; exact (min_eq_left h) ▸ hcone⟩
    · exact ⟨-1, by norm_num, by rw [neg_one_smul, sub_neg_eq_add]; exact (min_eq_right h) ▸ hcone⟩
  obtain ⟨τ, hτ, hτv⟩ : ∃ τ : ℝ, |τ| = 1 ∧ ‖v - τ • w‖ ≤ 4 * ρ := by
    rcases le_total ‖v - w‖ ‖v + w‖ with h | h
    · exact ⟨1, by norm_num, by rw [one_smul]; exact (min_eq_left h) ▸ hvw⟩
    · exact ⟨-1, by norm_num, by rw [neg_one_smul, sub_neg_eq_add]; exact (min_eq_right h) ▸ hvw⟩
  intro q hq
  obtain ⟨t, ht, hqt⟩ := tube_param hq
  -- the axial parameter
  set ℓ := c + (t - tp) * (σ * τ) with hℓ
  have hℓI : ℓ ∈ Icc (-(9 / 2 : ℝ)) (11 / 2) := by
    have hst : |(t - tp) * (σ * τ)| ≤ 1 := by
      rw [abs_mul, abs_mul, hσ, hτ, mul_one, mul_one, abs_le]
      constructor <;> linarith [ht.1, ht.2, htp.1, htp.2]
    rw [abs_le] at hst
    constructor <;> linarith [hc.1, hc.2, hst.1, hst.2]
  rw [dilatedTube, mem_thickening_iff]
  refine ⟨z + ℓ • w, ?_, ?_⟩
  · rw [segment_eq_image']
    refine ⟨(ℓ + 9 / 2) / 10, ⟨by linarith [hℓI.1], by linarith [hℓI.2]⟩, ?_⟩
    simp only
    module
  · rw [dist_eq_norm]
    have he : q - (z + ℓ • w) = (q - (y + t • u)) - (p - (y + tp • u)) + (p - (z + c • w)) +
        (t - tp) • ((u - σ • v) + σ • (v - τ • w)) := by
      rw [hℓ]; module
    rw [he]
    have hsmall : ‖(t - tp) • ((u - σ • v) + σ • (v - τ • w))‖ ≤ 7 * ρ := by
      rw [norm_smul, Real.norm_eq_abs]
      have h1 : |t - tp| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2, htp.1, htp.2]
      have h2 : ‖(u - σ • v) + σ • (v - τ • w)‖ ≤ 7 * ρ := by
        calc ‖(u - σ • v) + σ • (v - τ • w)‖ ≤ ‖u - σ • v‖ + ‖σ • (v - τ • w)‖ := norm_add_le _ _
          _ = ‖u - σ • v‖ + ‖v - τ • w‖ := by rw [norm_smul, Real.norm_eq_abs, hσ, one_mul]
          _ ≤ 3 * ρ + 4 * ρ := add_le_add hσu hτv
          _ = 7 * ρ := by ring
      calc |t - tp| * ‖(u - σ • v) + σ • (v - τ • w)‖ ≤ 1 * (7 * ρ) :=
            mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        _ = 7 * ρ := one_mul _
    have h1 := norm_add_le ((q - (y + t • u)) - (p - (y + tp • u)) + (p - (z + c • w)))
      ((t - tp) • ((u - σ • v) + σ • (v - τ • w)))
    have h2 := norm_add_le ((q - (y + t • u)) - (p - (y + tp • u))) (p - (z + c • w))
    have h3 := norm_sub_le (q - (y + t • u)) (p - (y + tp • u))
    linarith


theorem tube_subset_dilatedTube (ρ : ℝ) (hρ : 0 ≤ ρ) (z w : Space) :
    tube ρ z w ⊆ dilatedTube ρ z w := by
  intro q hq
  obtain ⟨t, ht, hqt⟩ := tube_param hq
  rw [dilatedTube, mem_thickening_iff]
  refine ⟨z + t • w, ?_, by rw [dist_eq_norm]; linarith⟩
  rw [segment_eq_image']
  refine ⟨(t + 9 / 2) / 10, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
  simp only
  module

/-- **Robust transversality from separated covers.**  At a point `p`, the shading-tubes whose
directions lie within `ρ` (up to sign) of a unit vector `u` all belong to one coarse tube of a
separated cover at scale `ρ`; so they are at most as many as the fibre multiplicity bound. -/
theorem cone_count_le {n k : ℕ} {δ ρ B : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    {x v : Fin n → Space} {Y : Fin n → Set Space} {z w : Fin k → Space} {a : Fin n → Fin k}
    (hv : ∀ i, ‖v i‖ = 1) (hw : ∀ j, ‖w j‖ = 1) (hYT : ∀ i, Y i ⊆ tube δ (x i) (v i))
    (ha : ∀ i, (Y i).Nonempty → tube δ (x i) (v i) ⊆ tube ρ (z (a i)) (w (a i)))
    (hsep : ∀ i j j', tube δ (x i) (v i) ⊆ dilatedTube ρ (z j) (w j) →
      tube δ (x i) (v i) ⊆ dilatedTube ρ (z j') (w j') → j = j')
    (hfibre : ∀ j p, ({i | a i = j ∧ p ∈ Y i}.ncard : ℝ) ≤ B) (hB : 0 ≤ B)
    (p u : Space) (hu : ‖u‖ = 1) :
    ({l | p ∈ Y l ∧ min ‖v l - u‖ ‖v l + u‖ ≤ ρ}.ncard : ℝ) ≤ B := by
  classical
  by_cases hne : {l | p ∈ Y l ∧ min ‖v l - u‖ ‖v l + u‖ ≤ ρ}.Nonempty
  · obtain ⟨i₀, hpi₀, hi₀⟩ := hne
    have hsub : {l | p ∈ Y l ∧ min ‖v l - u‖ ‖v l + u‖ ≤ ρ} ⊆ {l | a l = a i₀ ∧ p ∈ Y l} := by
      rintro l ⟨hpl, hl⟩
      refine ⟨?_, hpl⟩
      -- the cone condition relative to `v i₀`
      have hcone : min ‖v l - v i₀‖ ‖v l + v i₀‖ ≤ 3 * ρ := by
        rcases le_total ‖v l - u‖ ‖v l + u‖ with h1 | h1 <;>
          rcases le_total ‖v i₀ - u‖ ‖v i₀ + u‖ with h2 | h2
        · rw [min_eq_left h1] at hl; rw [min_eq_left h2] at hi₀
          have : ‖v l - v i₀‖ ≤ ‖v l - u‖ + ‖v i₀ - u‖ := by
            rw [show v l - v i₀ = (v l - u) - (v i₀ - u) by abel]; exact norm_sub_le _ _
          exact (min_le_left _ _).trans (by linarith)
        · rw [min_eq_left h1] at hl; rw [min_eq_right h2] at hi₀
          have : ‖v l + v i₀‖ ≤ ‖v l - u‖ + ‖v i₀ + u‖ := by
            rw [show v l + v i₀ = (v l - u) + (v i₀ + u) by abel]; exact norm_add_le _ _
          exact (min_le_right _ _).trans (by linarith)
        · rw [min_eq_right h1] at hl; rw [min_eq_left h2] at hi₀
          have : ‖v l + v i₀‖ ≤ ‖v l + u‖ + ‖v i₀ - u‖ := by
            rw [show v l + v i₀ = (v l + u) + (v i₀ - u) by abel]; exact norm_add_le _ _
          exact (min_le_right _ _).trans (by linarith)
        · rw [min_eq_right h1] at hl; rw [min_eq_right h2] at hi₀
          have : ‖v l - v i₀‖ ≤ ‖v l + u‖ + ‖v i₀ + u‖ := by
            rw [show v l - v i₀ = (v l + u) - (v i₀ + u) by abel]; exact norm_sub_le _ _
          exact (min_le_left _ _).trans (by linarith)
      have hD := subset_dilatedTube_of_cone hδ hδρ (hv i₀) (hw _) (hv l) (ha i₀ ⟨p, hpi₀⟩)
        (hYT i₀ hpi₀) (hYT l hpl) hcone
      have hD' := (ha l ⟨p, hpl⟩).trans (tube_subset_dilatedTube ρ (hδ.le.trans hδρ) _ _)
      exact hsep l (a l) (a i₀) hD' hD
    calc ({l | p ∈ Y l ∧ min ‖v l - u‖ ‖v l + u‖ ≤ ρ}.ncard : ℝ)
        ≤ ({l | a l = a i₀ ∧ p ∈ Y l}.ncard : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ B := hfibre _ p
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.ncard_empty, Nat.cast_zero]
    exact hB

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
