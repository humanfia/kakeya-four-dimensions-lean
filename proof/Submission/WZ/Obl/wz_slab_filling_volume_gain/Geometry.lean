-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_filling_volume_gain.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyEstimate
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxGeometry

/-!
# Geometry of a filled box cut to the unit ball

A `10δ × b × 2` box containing a tube of the unit ball, intersected with the closed
unit ball, is a convex body for o065's body estimate: it has volume comparable to
`δ * b`, contains a `δ`-ball and a unit segment, and has a wide section of size
comparable to `b`. Everything is witnessed by a sub-box near the tube midpoint.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_slab_filling_volume_gain

open MeasureTheory Set Metric
open scoped ENNReal

abbrev Space := LeanEval.Analysis.WangZahlKakeya.Space
abbrev Tube := WangZahlLot.Obl.wz_tower_balanced_refinement.Tube
abbrev Box := WangZahlLot.Obl.wz_two_scale_flat_box_estimate.Box

/-- The squared norm of a vector of `ℝ³` in coordinates. -/
lemma norm_sq_three (d : Space) : ‖d‖ ^ 2 = d 0 ^ 2 + d 1 ^ 2 + d 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]

/-- The midpoint of a unit segment whose tube lies in the unit ball is well inside it. -/
lemma mid_norm_lt {δ : ℝ} (hδ : 0 < δ) {x v : Space} (hv : ‖v‖ = 1)
    (hT : Tube δ x v ⊆ ball (0 : Space) 1) : ‖x + (1 / 2 : ℝ) • v‖ < 87 / 100 := by
  have hx : ‖x‖ < 1 := by
    have : x ∈ Tube δ x v := self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v))
    simpa using hT this
  have hxv : ‖x + v‖ < 1 := by
    have : x + v ∈ Tube δ x v :=
      self_subset_thickening hδ _ (right_mem_segment ℝ x (x + v))
    simpa using hT this
  have h1 : ‖x + v‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x v + ‖v‖ ^ 2 := norm_add_sq_real x v
  have h2 : ‖x + (1 / 2 : ℝ) • v‖ ^ 2 =
      ‖x‖ ^ 2 + 2 * inner ℝ x ((1 / 2 : ℝ) • v) + ‖(1 / 2 : ℝ) • v‖ ^ 2 :=
    norm_add_sq_real _ _
  rw [inner_smul_right, norm_smul, hv] at h2
  rw [hv] at h1
  have hsq : ‖x + (1 / 2 : ℝ) • v‖ ^ 2 < 3 / 4 := by
    rw [h2]
    norm_num
    nlinarith [norm_nonneg x, norm_nonneg (x + v)]
  nlinarith [norm_nonneg (x + (1 / 2 : ℝ) • v)]

/-- Clamping a coordinate into a shorter interval moves it by at most the margin. -/
lemma clamp_spec {t h r : ℝ} (hr : 0 ≤ r) (hrh : r ≤ h) (ht : |t| ≤ h) :
    |max (-(h - r)) (min t (h - r))| ≤ h - r ∧
      |max (-(h - r)) (min t (h - r)) - t| ≤ r := by
  rw [abs_le] at ht
  constructor
  · rw [abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_right _ _)
  · rw [abs_le]
    rcases le_total t (h - r) with h1 | h1
    · rw [min_eq_left h1]
      rcases le_total (-(h - r)) t with h2 | h2
      · rw [max_eq_right h2]; constructor <;> linarith
      · rw [max_eq_left h2]; constructor <;> linarith
    · rw [min_eq_right h1, max_eq_right (by linarith)]
      constructor <;> linarith

/-- The coordinate vector of the sub-box centre in the box frame. -/
noncomputable def centreVec (s t : ℝ) : Space :=
  s • EuclideanSpace.single 1 (1 : ℝ) + t • EuclideanSpace.single 2 (1 : ℝ)

@[simp] lemma centreVec_zero (s t : ℝ) : centreVec s t 0 = 0 := by
  simp [centreVec]

@[simp] lemma centreVec_one (s t : ℝ) : centreVec s t 1 = s := by
  simp [centreVec]

@[simp] lemma centreVec_two (s t : ℝ) : centreVec s t 2 = t := by
  simp [centreVec]

lemma box_mem_iff {a b c : ℝ} {z p : Space} {g : Space ≃ₗᵢ[ℝ] Space} :
    p ∈ Box a b c z g ↔
      |g (p - z) 0| ≤ a / 2 ∧ |g (p - z) 1| ≤ b / 2 ∧ |g (p - z) 2| ≤ c / 2 :=
  Iff.rfl

lemma frame_shift (z p : Space) (g : Space ≃ₗᵢ[ℝ] Space) (w : Space) :
    g (p - (z + g.symm w)) = g (p - z) - w := by
  rw [show p - (z + g.symm w) = (p - z) - g.symm w by abel, map_sub,
    LinearIsometryEquiv.apply_symm_apply]

/-- The sub-box of half-widths `(5δ, r₁, r₂)` centred at box coordinates `(0, s, t)`. -/
noncomputable def subBox (δ r₁ r₂ s t : ℝ) (z : Space) (g : Space ≃ₗᵢ[ℝ] Space) : Set Space :=
  Box (10 * δ) (2 * r₁) (2 * r₂) (z + g.symm (centreVec s t)) g

lemma subBox_subset {δ b r₁ r₂ s t : ℝ} {z : Space} {g : Space ≃ₗᵢ[ℝ] Space}
    (hs : |s| + r₁ ≤ b / 2) (ht : |t| + r₂ ≤ 1) :
    subBox δ r₁ r₂ s t z g ⊆ Box (10 * δ) b 2 z g := by
  intro p hp
  rw [subBox, box_mem_iff, frame_shift] at hp
  obtain ⟨h0, h1, h2⟩ := hp
  simp only [PiLp.sub_apply, centreVec_zero, centreVec_one, centreVec_two, sub_zero] at h0 h1 h2
  refine ⟨h0, ?_, ?_⟩
  · have := abs_sub_abs_le_abs_sub (g (p - z) 1) s
    linarith [abs_nonneg s]
  · have := abs_sub_abs_le_abs_sub (g (p - z) 2) t
    linarith

lemma subBox_subset_ball {δ b r₁ r₂ s t : ℝ} {z m : Space} {g : Space ≃ₗᵢ[ℝ] Space}
    (hδ : 0 ≤ δ) (hδs : δ ≤ 1 / 1000) (hr₁ : r₁ ≤ 1 / 25) (hr₂ : r₂ ≤ 1 / 25)
    (hm : ‖m‖ < 87 / 100) (hmP : m ∈ Box (10 * δ) b 2 z g)
    (hs : |s - g (m - z) 1| ≤ r₁) (ht : |t - g (m - z) 2| ≤ r₂) :
    subBox δ r₁ r₂ s t z g ⊆ closedBall (0 : Space) 1 := by
  intro p hp
  rw [subBox, box_mem_iff, frame_shift] at hp
  obtain ⟨h0, h1, h2⟩ := hp
  simp only [PiLp.sub_apply, centreVec_zero, centreVec_one, centreVec_two, sub_zero] at h0 h1 h2
  rw [box_mem_iff] at hmP
  obtain ⟨m0, m1, m2⟩ := hmP
  set d : Space := g (p - z) - g (m - z) with hd
  have hdist : ‖p - m‖ = ‖d‖ := by
    rw [hd, ← map_sub, LinearIsometryEquiv.norm_map]
    congr 1
    abel
  have hd0 : |d 0| ≤ 10 * δ := by
    have : d 0 = g (p - z) 0 - g (m - z) 0 := by simp [hd]
    rw [this]
    have := abs_sub (g (p - z) 0) (g (m - z) 0)
    linarith
  have hd1 : |d 1| ≤ 2 * r₁ := by
    have : d 1 = (g (p - z) 1 - s) + (s - g (m - z) 1) := by simp [hd]
    rw [this]
    have := abs_add_le (g (p - z) 1 - s) (s - g (m - z) 1)
    linarith
  have hd2 : |d 2| ≤ 2 * r₂ := by
    have : d 2 = (g (p - z) 2 - t) + (t - g (m - z) 2) := by simp [hd]
    rw [this]
    have := abs_add_le (g (p - z) 2 - t) (t - g (m - z) 2)
    linarith
  have hsq : ‖d‖ ^ 2 < (12 / 100) ^ 2 := by
    rw [norm_sq_three]
    have e0 : d 0 ^ 2 ≤ (10 * δ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hd0 2
    have e1 : d 1 ^ 2 ≤ (2 * r₁) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hd1 2
    have e2 : d 2 ^ 2 ≤ (2 * r₂) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hd2 2
    have r1n : 0 ≤ 2 * r₁ := (abs_nonneg _).trans hd1
    have r2n : 0 ≤ 2 * r₂ := (abs_nonneg _).trans hd2
    have f1 : (2 * r₁) ^ 2 ≤ (2 / 25) ^ 2 := pow_le_pow_left₀ r1n (by linarith) 2
    have f2 : (2 * r₂) ^ 2 ≤ (2 / 25) ^ 2 := pow_le_pow_left₀ r2n (by linarith) 2
    have f0 : (10 * δ) ^ 2 ≤ (1 / 100) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    nlinarith
  have hdn : ‖d‖ < 12 / 100 := by nlinarith [norm_nonneg d]
  rw [mem_closedBall, dist_zero_right]
  have := norm_add_le m (p - m)
  rw [add_sub_cancel] at this
  linarith

lemma subBox_volume {δ r₁ r₂ s t : ℝ} (hδ : 0 ≤ δ) (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂)
    (z : Space) (g : Space ≃ₗᵢ[ℝ] Space) :
    volume (subBox δ r₁ r₂ s t z g) = ENNReal.ofReal (10 * δ * (2 * r₁) * (2 * r₂)) :=
  WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_volume (by positivity) (by positivity)
    (by positivity) _ _

lemma subBox_diamond {δ r₁ r₂ s t : ℝ} (hδ : 0 ≤ δ) (hr : r₁ ≤ r₂)
    (z : Space) (g : Space ≃ₗᵢ[ℝ] Space) :
    ∀ σ τ : ℝ, |σ| + |τ| ≤ r₁ →
      (z + g.symm (centreVec s t)) + σ • g.symm (EuclideanSpace.single 1 (1 : ℝ)) +
        τ • g.symm (EuclideanSpace.single 2 (1 : ℝ)) ∈ subBox δ r₁ r₂ s t z g := by
  intro σ τ hστ
  rw [subBox, box_mem_iff]
  have he : g ((z + g.symm (centreVec s t)) + σ • g.symm (EuclideanSpace.single 1 (1 : ℝ)) +
      τ • g.symm (EuclideanSpace.single 2 (1 : ℝ)) - (z + g.symm (centreVec s t))) =
      centreVec σ τ := by
    rw [show (z + g.symm (centreVec s t)) + σ • g.symm (EuclideanSpace.single 1 (1 : ℝ)) +
        τ • g.symm (EuclideanSpace.single 2 (1 : ℝ)) - (z + g.symm (centreVec s t)) =
        σ • g.symm (EuclideanSpace.single 1 (1 : ℝ)) +
          τ • g.symm (EuclideanSpace.single 2 (1 : ℝ)) by abel]
    rw [map_add, map_smul, map_smul, LinearIsometryEquiv.apply_symm_apply,
      LinearIsometryEquiv.apply_symm_apply]
    rfl
  rw [he, centreVec_zero, centreVec_one, centreVec_two]
  refine ⟨by rw [abs_zero]; positivity, by linarith [abs_nonneg τ], by linarith [abs_nonneg σ]⟩

/-- All the per-body facts needed for o065's `BodyGeometry`. -/
theorem filled_body_facts {δ b : ℝ} (hδ : 0 < δ) (hδs : δ ≤ 1 / 1000) (hb : 10 * δ ≤ b)
    (hb1 : b ≤ 1) {x v z : Space} {g : Space ≃ₗᵢ[ℝ] Space} (hv : ‖v‖ = 1)
    (hTI : Tube δ x v ⊆ ball (0 : Space) 1) (hTP : Tube δ x v ⊆ Box (10 * δ) b 2 z g) :
    IsCompact (Box (10 * δ) b 2 z g ∩ closedBall (0 : Space) 1) ∧
    Convex ℝ (Box (10 * δ) b 2 z g ∩ closedBall (0 : Space) 1) ∧
    ball (x + (1 / 2 : ℝ) • v) δ ⊆ Box (10 * δ) b 2 z g ∩ closedBall (0 : Space) 1 ∧
    (∃ p ∈ Box (10 * δ) b 2 z g ∩ closedBall (0 : Space) 1,
      ∃ q ∈ Box (10 * δ) b 2 z g ∩ closedBall (0 : Space) 1, (1 / 16 : ℝ) ≤ dist p q) ∧
    WangZahlLot.Obl.wz_flat_factored_improvement.WideSection
      (Box (10 * δ) b 2 z g ∩ closedBall (0 : Space) 1) (min (b / 2) (1 / 25) / 2) ∧
    ENNReal.ofReal (δ * b / 16) ≤ volume (Box (10 * δ) b 2 z g ∩ closedBall (0 : Space) 1) ∧
    volume (Box (10 * δ) b 2 z g ∩ closedBall (0 : Space) 1) ≤
      ENNReal.ofReal (384 * (δ * b / 16)) ∧
    Tube δ x v ⊆ Box (10 * δ) b 2 z g ∩ closedBall (0 : Space) 1 := by
  have hb0 : 0 ≤ b := by linarith
  have hTU : Tube δ x v ⊆ Box (10 * δ) b 2 z g ∩ closedBall (0 : Space) 1 :=
    subset_inter hTP (hTI.trans ball_subset_closedBall)
  set m : Space := x + (1 / 2 : ℝ) • v with hmdef
  have hmseg : m ∈ segment ℝ x (x + v) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [hmdef]
    module
  have hmT : m ∈ Tube δ x v := self_subset_thickening hδ _ hmseg
  have hmP : m ∈ Box (10 * δ) b 2 z g := hTP hmT
  have hmn : ‖m‖ < 87 / 100 := mid_norm_lt hδ hv hTI
  -- the sub-box
  set r₁ : ℝ := min (b / 2) (1 / 25) with hr₁
  have hr₁0 : 0 ≤ r₁ := le_min (by positivity) (by norm_num)
  have hr₁b : r₁ ≤ b / 2 := min_le_left _ _
  have hr₁s : r₁ ≤ 1 / 25 := min_le_right _ _
  have hmP' := hmP
  rw [box_mem_iff] at hmP'
  obtain ⟨hm0, hm1, hm2⟩ := hmP'
  obtain ⟨hs1, hs2⟩ := clamp_spec hr₁0 hr₁b hm1
  obtain ⟨ht1, ht2⟩ := clamp_spec (by norm_num : (0 : ℝ) ≤ 1 / 25)
    (by norm_num : (1 / 25 : ℝ) ≤ 2 / 2) hm2
  set s := max (-(b / 2 - r₁)) (min (g (m - z) 1) (b / 2 - r₁))
  set t := max (-(2 / 2 - (1 / 25 : ℝ))) (min (g (m - z) 2) (2 / 2 - 1 / 25))
  have hSP : subBox δ r₁ (1 / 25) s t z g ⊆ Box (10 * δ) b 2 z g :=
    subBox_subset (by linarith) (by linarith)
  have hSB : subBox δ r₁ (1 / 25) s t z g ⊆ closedBall (0 : Space) 1 :=
    subBox_subset_ball hδ.le hδs hr₁s le_rfl hmn hmP hs2 ht2
  have hSU : subBox δ r₁ (1 / 25) s t z g ⊆ Box (10 * δ) b 2 z g ∩ closedBall (0 : Space) 1 :=
    subset_inter hSP hSB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hTU⟩
  · exact (WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_compact hb (by linarith)
      (by norm_num) z g).inter_right isClosed_closedBall
  · exact (WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_convex _ _ _ z g).inter
      (convex_closedBall _ _)
  · exact (ball_subset_thickening hmseg δ).trans hTU
  · refine ⟨x, hTU (self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v))),
      x + v, hTU (self_subset_thickening hδ _ (right_mem_segment ℝ x (x + v))), ?_⟩
    rw [dist_eq_norm, show x - (x + v) = -v by abel, norm_neg, hv]
    norm_num
  · apply WangZahlLot.Obl.wz_flat_factored_improvement.WideSection.mono _ hSU
    apply WangZahlLot.Obl.wz_flat_factored_improvement.wideSection_of_diamond hr₁0
      (z + g.symm (centreVec s t)) (g.symm (EuclideanSpace.single 1 (1 : ℝ)))
      (g.symm (EuclideanSpace.single 2 (1 : ℝ)))
    · rw [LinearIsometryEquiv.norm_map]; simp
    · rw [LinearIsometryEquiv.norm_map]; simp
    · rw [LinearIsometryEquiv.inner_map_map]
      simp [EuclideanSpace.inner_single_left]
    · exact subBox_diamond hδ.le hr₁s z g
  · apply le_trans _ (measure_mono hSU)
    rw [subBox_volume hδ.le hr₁0 (by norm_num) z g]
    apply ENNReal.ofReal_le_ofReal
    have hr₁b' : b / 25 ≤ r₁ := le_min (by linarith) (by linarith)
    nlinarith
  · apply (measure_mono inter_subset_left).trans
    rw [WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_volume (by positivity) hb0
      (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith

end WangZahlLot.Obl.wz_slab_filling_volume_gain
