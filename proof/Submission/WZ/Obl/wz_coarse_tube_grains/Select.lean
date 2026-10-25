-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.Select.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.X48.ColorRefinement
import Submission.WZ.Obl.wz_coarse_tube_grains.X48.CarrierNet
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.DyadicShading

/-!
# Selecting one thin carrier inside a coarse tube

A fibre of unit `δ`-tubes inside `T (ρ/2) y w` is split, by a fixed finite net of tube
parameters, into a bounded number of classes, each inside a carrier tube of radius `ρ/256`
around one of its own tubes. One class is kept with the colour refinement of x0448 (o151,
`ColorRefinement.lean`), which keeps a fixed fraction of the multiplicity at every retained
point, and then one dyadic multiplicity level (x0310's `dyadic_shading_refinement_common`).
-/

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_tube_grains

open Set Metric MeasureTheory
open scoped Classical

/-- The tubes of the frozen statement. -/
abbrev Tb (d : ℝ) (p u : LeanEval.Analysis.WangZahlKakeya.Space) :
    Set LeanEval.Analysis.WangZahlKakeya.Space :=
  Metric.thickening d (segment ℝ p (p + u))

local notation "V" => LeanEval.Analysis.WangZahlKakeya.Space

/-- A unit tube inside the `ρ/2`-tube around `[y, y + w]` has, up to reversing its axis,
start within `2ρ` of `y` and direction within `2ρ` of `w`. -/
theorem normalize_tube {δ ρ : ℝ} (hδ : 0 < δ) {x v y w : V} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (h : Tb δ x v ⊆ Tb (ρ / 2) y w) :
    ∃ x' v' : V, segment ℝ x' (x' + v') = segment ℝ x (x + v) ∧ ‖v'‖ = 1 ∧
      ‖v' - w‖ < 2 * ρ ∧ ‖x' - y‖ < 2 * ρ := by
  have hx : x ∈ Tb (ρ / 2) y w :=
    h (self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v)))
  have hxv : x + v ∈ Tb (ρ / 2) y w :=
    h (self_subset_thickening hδ _ (right_mem_segment ℝ x (x + v)))
  obtain ⟨q, hq, hxq⟩ := mem_thickening_iff.mp hx
  obtain ⟨q', hq', hxq'⟩ := mem_thickening_iff.mp hxv
  rw [segment_eq_image'] at hq hq'
  obtain ⟨s, hs, rfl⟩ := hq
  obtain ⟨s', hs', rfl⟩ := hq'
  simp only [add_sub_cancel_left] at hxq hxq'
  rw [dist_eq_norm] at hxq hxq'
  set d := s' - s with hd_def
  have hdv : ‖v - d • w‖ < ρ := by
    have heq : v - d • w = (x + v - (y + s' • w)) - (x - (y + s • w)) := by
      rw [hd_def]; module
    rw [heq]
    have := norm_sub_le (x + v - (y + s' • w)) (x - (y + s • w))
    linarith
  have hdw : ‖d • w‖ = |d| := by rw [norm_smul, Real.norm_eq_abs, hw, mul_one]
  have hgap : 1 - |d| < ρ := by
    have := norm_sub_norm_le v (d • w)
    rw [hv, hdw] at this
    linarith
  have hd1 : d ≤ 1 := by linarith [hs.1, hs'.2]
  have hd1' : -1 ≤ d := by linarith [hs.2, hs'.1]
  have hsw : ∀ t : ℝ, 0 ≤ t → ‖t • w‖ = t := fun t ht => by
    rw [norm_smul, Real.norm_of_nonneg ht, hw, mul_one]
  rcases le_or_gt 0 d with hd0 | hd0
  · have habs : |d| = d := abs_of_nonneg hd0
    refine ⟨x, v, rfl, hv, ?_, ?_⟩
    · have heq : v - w = (v - d • w) - (1 - d) • w := by module
      rw [heq]
      have h1 := norm_sub_le (v - d • w) ((1 - d) • w)
      rw [hsw (1 - d) (by linarith)] at h1
      linarith
    · have heq : x - y = (x - (y + s • w)) + s • w := by module
      rw [heq]
      have h1 := norm_add_le (x - (y + s • w)) (s • w)
      rw [hsw s hs.1] at h1
      have : s < ρ := by linarith [hs'.2]
      linarith
  · have habs : |d| = -d := abs_of_neg hd0
    refine ⟨x + v, -v, ?_, by rw [norm_neg, hv], ?_, ?_⟩
    · rw [show x + v + -v = x by abel, segment_symm]
    · have heq : -v - w = -((v - d • w) + (1 + d) • w) := by module
      rw [heq, norm_neg]
      have h1 := norm_add_le (v - d • w) ((1 + d) • w)
      rw [hsw (1 + d) (by linarith)] at h1
      linarith
    · have heq : x + v - y = (x + v - (y + s' • w)) + s' • w := by module
      rw [heq]
      have h1 := norm_add_le (x + v - (y + s' • w)) (s' • w)
      rw [hsw s' hs'.1] at h1
      have : s' < ρ := by linarith [hs.2]
      linarith

/-- A fixed finite net of the parameter pairs `(u, t)` with `‖u‖ ≤ 2`, `‖t‖ ≤ 2`. -/
theorem exists_param_net :
    ∃ (K : ℕ), 0 < K ∧ ∃ (a b : Fin K → V), ∀ (u t : V), ‖u‖ ≤ 2 → ‖t‖ ≤ 2 →
      ∃ k, dist u (a k) < 1 / 2048 ∧ dist t (b k) < 1 / 2048 := by
  let C : Set (V × V) := closedBall (0 : V) 2 ×ˢ closedBall (0 : V) 2
  have hC : IsCompact C := (isCompact_closedBall (0 : V) 2).prod (isCompact_closedBall (0 : V) 2)
  obtain ⟨D, hDC, hDfin, hcover⟩ := hC.finite_cover_balls (by norm_num : (0 : ℝ) < 1 / 2048)
  have h0 : ((0 : V), (0 : V)) ∈ C := by simp [C]
  obtain ⟨c₀, hc₀, _⟩ := mem_iUnion₂.mp (hcover h0)
  letI : Fintype D := hDfin.fintype
  let e : Fin (Fintype.card D) ≃ D := (Fintype.equivFin D).symm
  refine ⟨Fintype.card D, Fintype.card_pos_iff.mpr ⟨⟨c₀, hc₀⟩⟩,
    (fun k => (e k).val.1), (fun k => (e k).val.2), ?_⟩
  intro u t hu ht
  have hpair : (u, t) ∈ C :=
    ⟨mem_closedBall_zero_iff.mpr hu, mem_closedBall_zero_iff.mpr ht⟩
  obtain ⟨c, hc, hpc⟩ := mem_iUnion₂.mp (hcover hpair)
  refine ⟨e.symm ⟨c, hc⟩, ?_⟩
  simp only [Equiv.apply_symm_apply]
  have hdist : dist (u, t) c < (1 / 2048 : ℝ) := mem_ball.mp hpc
  rw [Prod.dist_eq, max_lt_iff] at hdist
  exact hdist

/-- Selection of one thin carrier, one colour class and one multiplicity level. -/
theorem carrier_selection :
    ∃ K₁ : ℕ, 0 < K₁ ∧ ∀ (δ ρ : ℝ), 0 < δ → 512 * δ ≤ ρ →
      ∀ (m : ℕ) (x v : Fin m → V) (Z : Fin m → Set V) (y w : V), ‖w‖ = 1 →
      (∀ i, ‖v i‖ = 1 ∧ Tb δ (x i) (v i) ⊆ Tb (ρ / 2) y w ∧ MeasurableSet (Z i) ∧
        Z i ⊆ Tb δ (x i) (v i)) →
      ∃ (k : ℕ) (Y : Fin m → Set V) (y' w' : V), ‖w'‖ = 1 ∧ ‖w' - w‖ < 2 * ρ ∧
        segment ℝ y' (y' + w') ⊆ Tb (ρ / 2) y w ∧
        (∀ i, MeasurableSet (Y i) ∧ Y i ⊆ Z i) ∧
        (∀ i, (Y i).Nonempty → Tb δ (x i) (v i) ⊆ Tb (ρ / 256) y' w') ∧
        (∑ i, volume (Z i)) ≤ ((K₁ ^ 2 * (Nat.log 2 m + 1) : ℕ) : ENNReal) *
          ∑ i, volume (Y i) ∧
        (∀ p ∈ ⋃ i, Y i, 2 ^ k ≤ (Finset.univ.filter fun i => p ∈ Y i).card ∧
          (Finset.univ.filter fun i => p ∈ Y i).card < 2 ^ (k + 1)) ∧
        (∀ p, (∃ i, p ∈ Y i) → (({i | p ∈ Z i} : Set (Fin m)).ncard : ℝ) ≤
          K₁ * (({i | p ∈ Y i} : Set (Fin m)).ncard : ℝ)) := by
  obtain ⟨K₁, hK₁, a, b, hnet⟩ := exists_param_net
  refine ⟨K₁, hK₁, ?_⟩
  intro δ ρ hδ hδρ m x v Z y w hw hZ
  have hρ : 0 < ρ := by linarith
  -- normalized parameters
  have hnorm := fun i => normalize_tube hδ (hZ i).1 hw (hZ i).2.1
  choose xt vt hseg hvt hvw hxy using hnorm
  -- colours
  have hcol : ∀ i, ∃ k, dist (ρ⁻¹ • (xt i - y)) (a k) < 1 / 2048 ∧
      dist (ρ⁻¹ • (vt i - w)) (b k) < 1 / 2048 := by
    intro i
    apply hnet
    · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρ.le)]
      rw [inv_mul_le_iff₀ hρ]; linarith [hxy i]
    · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρ.le)]
      rw [inv_mul_le_iff₀ hρ]; linarith [hvw i]
  choose color hcolor using hcol
  -- tubes of one colour lie in the thin carrier around any one of them
  have hsame : ∀ i j, color i = color j →
      Tb δ (x i) (v i) ⊆ Tb (ρ / 256) (xt j) (vt j) := by
    intro i j hij
    have hclose : ∀ (u u' c : V), dist (ρ⁻¹ • u) c < 1 / 2048 →
        dist (ρ⁻¹ • u') c < 1 / 2048 → dist u u' ≤ ρ / 1024 := by
      intro u u' c h1 h2
      have h3 := (dist_triangle_right (ρ⁻¹ • u) (ρ⁻¹ • u') c).trans_lt (add_lt_add h1 h2)
      rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρ.le),
        inv_mul_lt_iff₀ hρ] at h3
      rw [dist_eq_norm]
      linarith
    have hx' : dist (xt i) (xt j) ≤ ρ / 1024 := by
      have := hclose (xt i - y) (xt j - y) (a (color j)) (by rw [← hij]; exact (hcolor i).1)
        (hcolor j).1
      rwa [dist_eq_norm, sub_sub_sub_cancel_right, ← dist_eq_norm] at this
    have hv' : dist (vt i) (vt j) ≤ ρ / 1024 := by
      have := hclose (vt i - w) (vt j - w) (b (color j)) (by rw [← hij]; exact (hcolor i).2)
        (hcolor j).2
      rwa [dist_eq_norm, sub_sub_sub_cancel_right, ← dist_eq_norm] at this
    have h1 : Tb δ (x i) (v i) = Tb δ (xt i) (vt i) := by
      simp only [Tb, hseg i]
    rw [h1]
    exact X48.tube_containment_of_parameters (by linarith)
  -- one colour class with a fixed pointwise fraction of the multiplicity
  obtain ⟨c₀, Za, hZa, hmassa, hfraca⟩ :=
    X48.color_refinement hK₁ color Z (fun i => (hZ i).2.2.1)
  -- one dyadic multiplicity level
  obtain ⟨k, Y, -, hY, hmassY, hlevel⟩ :=
    RIS.dyadic_shading_refinement_common volume Za (fun i => (hZa i).1)
  rw [Fintype.card_fin] at hmassY
  have hYsub : ∀ i, Y i ⊆ Z i := fun i => (hY i).2.trans (hZa i).2.1
  have hYcol : ∀ i, (Y i).Nonempty → color i = c₀ := by
    intro i ⟨p, hp⟩
    by_contra hne
    have := (hZa i).2.2 hne
    have hp' := (hY i).2 hp
    rw [this] at hp'
    simp at hp'
  -- the representative tube
  have hrep : ∃ y' w' : V, ‖w'‖ = 1 ∧ ‖w' - w‖ < 2 * ρ ∧
      segment ℝ y' (y' + w') ⊆ Tb (ρ / 2) y w ∧
      ∀ i, (Y i).Nonempty → Tb δ (x i) (v i) ⊆ Tb (ρ / 256) y' w' := by
    by_cases hex : ∃ i₀, (Y i₀).Nonempty
    · obtain ⟨i₀, hi₀⟩ := hex
      refine ⟨xt i₀, vt i₀, hvt i₀, hvw i₀, ?_, ?_⟩
      · rw [hseg i₀]
        exact (self_subset_thickening hδ _).trans (hZ i₀).2.1
      · intro i hi
        exact hsame i i₀ ((hYcol i hi).trans (hYcol i₀ hi₀).symm)
    · refine ⟨y, w, hw, by rw [sub_self, norm_zero]; linarith,
        self_subset_thickening (by linarith : (0 : ℝ) < ρ / 2) _, ?_⟩
      intro i hi
      exact absurd ⟨i, hi⟩ hex
  obtain ⟨y', w', hw', hww, hsegsub, hcar⟩ := hrep
  refine ⟨k, Y, y', w', hw', hww, hsegsub, fun i => ⟨(hY i).1, hYsub i⟩, hcar, ?_, ?_, ?_⟩
  · calc (∑ i, volume (Z i)) ≤ (K₁ : ENNReal) ^ 2 * ∑ i, volume (Za i) := hmassa
      _ ≤ (K₁ : ENNReal) ^ 2 * (((Nat.log 2 m + 1 : ℕ) : ENNReal) * ∑ i, volume (Y i)) := by
          gcongr
      _ = ((K₁ ^ 2 * (Nat.log 2 m + 1) : ℕ) : ENNReal) * ∑ i, volume (Y i) := by
          push_cast; ring
  · intro p hp
    exact ⟨(hlevel p hp).1, (hlevel p hp).2.1⟩
  · intro p hp
    have hpU : p ∈ ⋃ i, Y i := Set.mem_iUnion.mpr hp
    have hset : ({i | p ∈ Y i} : Set (Fin m)) = {i | p ∈ Za i} := by
      ext i
      exact (hlevel p hpU).2.2 i
    obtain ⟨i, hi⟩ := hp
    have := hfraca p ⟨i, (hY i).2 hi⟩
    rw [hset]
    exact this

end WangZahlLot.Obl.wz_coarse_tube_grains
