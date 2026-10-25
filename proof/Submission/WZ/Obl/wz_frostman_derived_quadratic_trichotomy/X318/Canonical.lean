-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Canonical.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.PrismGeometry
import Submission.WZ.Obl.wz_normalized_projection_iteration.Convex
import Submission.WZ.Obl.wz_convex_container_tube_packing

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file Canonical.lean), namespace renamed.
/-!
# Canonical (chord-aligned) unit tubes

A unit segment inside `closedBall 0 R` lies on a chord of that ball of length at most `2R`.
It is covered by the two unit segments at the ends of the chord.  Replacing every tube of a
family by one of these canonical tubes makes the axial positions a function of the line.
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set Metric MeasureTheory
open scoped ENNReal

/-- Discriminant of the chord of `closedBall 0 R` along `t ↦ x + t • v`. -/
noncomputable def chordDisc (R : ℝ) (x v : Space) : ℝ :=
  inner ℝ x v ^ 2 - ‖x‖ ^ 2 + R ^ 2

/-- Entry parameter of the line `t ↦ x + t • v` into `closedBall 0 R`. -/
noncomputable def chordLow (R : ℝ) (x v : Space) : ℝ :=
  -inner ℝ x v - Real.sqrt (chordDisc R x v)

/-- Exit parameter of the line `t ↦ x + t • v` from `closedBall 0 R`. -/
noncomputable def chordHigh (R : ℝ) (x v : Space) : ℝ :=
  -inner ℝ x v + Real.sqrt (chordDisc R x v)

lemma norm_add_smul_sq {x v : Space} (hv : ‖v‖ = 1) (t : ℝ) :
    ‖x + t • v‖ ^ 2 = ‖x‖ ^ 2 + 2 * t * inner ℝ x v + t ^ 2 := by
  rw [norm_add_sq_real, inner_smul_right, norm_smul, hv, Real.norm_eq_abs, mul_one, sq_abs]
  ring

lemma chordDisc_nonneg {R : ℝ} {x : Space} (v : Space) (hx : ‖x‖ ≤ R) :
    0 ≤ chordDisc R x v := by
  unfold chordDisc
  have h0 : 0 ≤ ‖x‖ := norm_nonneg x
  nlinarith [sq_nonneg (inner ℝ x v)]

lemma chordDisc_le {R : ℝ} {x v : Space} (hv : ‖v‖ = 1) :
    chordDisc R x v ≤ R ^ 2 := by
  unfold chordDisc
  have h := abs_real_inner_le_norm x v
  rw [hv, mul_one] at h
  have h2 : inner ℝ x v ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  linarith

lemma mem_closedBall_iff_chord {R : ℝ} {x v : Space} (hv : ‖v‖ = 1) (hR : 0 ≤ R)
    (hD : 0 ≤ chordDisc R x v) (t : ℝ) :
    x + t • v ∈ closedBall (0 : Space) R ↔ chordLow R x v ≤ t ∧ t ≤ chordHigh R x v := by
  rw [mem_closedBall_zero_iff, ← sq_le_sq₀ (norm_nonneg _) hR, norm_add_smul_sq hv]
  have hiff : ‖x‖ ^ 2 + 2 * t * inner ℝ x v + t ^ 2 ≤ R ^ 2 ↔
      (t + inner ℝ x v) ^ 2 ≤ chordDisc R x v := by
    unfold chordDisc
    constructor <;> intro h <;> nlinarith
  rw [hiff, Real.sq_le hD]
  unfold chordLow chordHigh
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- The data of a unit segment inside `closedBall 0 R`. -/
lemma chord_bounds {R : ℝ} {x v : Space} (hv : ‖v‖ = 1)
    (hseg : segment ℝ x (x + v) ⊆ closedBall (0 : Space) R) :
    0 ≤ R ∧ 0 ≤ chordDisc R x v ∧ chordLow R x v ≤ 0 ∧ 1 ≤ chordHigh R x v ∧
      chordHigh R x v - chordLow R x v ≤ 2 * R := by
  have hx : x ∈ closedBall (0 : Space) R := hseg (left_mem_segment ℝ _ _)
  have hx1 : x + v ∈ closedBall (0 : Space) R := hseg (right_mem_segment ℝ _ _)
  have hxR : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
  have hR : 0 ≤ R := (norm_nonneg x).trans hxR
  have hD := chordDisc_nonneg v hxR
  have h0 := (mem_closedBall_iff_chord hv hR hD 0).mp (by simpa using hx)
  have h1 := (mem_closedBall_iff_chord hv hR hD 1).mp (by simpa using hx1)
  refine ⟨hR, hD, h0.1, h1.2, ?_⟩
  have hs : Real.sqrt (chordDisc R x v) ≤ R :=
    (Real.sqrt_le_sqrt (chordDisc_le hv)).trans_eq (Real.sqrt_sq hR)
  unfold chordLow chordHigh
  linarith

/-- Start of the left canonical unit segment (it starts on the sphere). -/
noncomputable def leftStart (R : ℝ) (x v : Space) : Space := x + chordLow R x v • v

/-- Start of the right canonical unit segment (it ends on the sphere). -/
noncomputable def rightStart (R : ℝ) (x v : Space) : Space := x + (chordHigh R x v - 1) • v

lemma segment_unit_eq (p v : Space) :
    segment ℝ p (p + v) = (fun θ : ℝ => p + θ • v) '' Icc 0 1 := by
  rw [segment_eq_image']
  simp only [add_sub_cancel_left]

lemma segment_cover {R : ℝ} {x v : Space} (hv : ‖v‖ = 1) (hR1 : R ≤ 1)
    (hseg : segment ℝ x (x + v) ⊆ closedBall (0 : Space) R) :
    segment ℝ x (x + v) ⊆
      segment ℝ (leftStart R x v) (leftStart R x v + v) ∪
        segment ℝ (rightStart R x v) (rightStart R x v + v) := by
  obtain ⟨-, -, hlo, hhi, hlen⟩ := chord_bounds hv hseg
  rw [segment_unit_eq x v]
  rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩
  by_cases hcase : t ≤ chordLow R x v + 1
  · left
    rw [segment_unit_eq]
    refine ⟨t - chordLow R x v, ⟨by linarith, by linarith⟩, ?_⟩
    simp only [leftStart]
    module
  · right
    rw [segment_unit_eq]
    refine ⟨t - (chordHigh R x v - 1), ⟨by linarith, by linarith⟩, ?_⟩
    simp only [rightStart]
    module

lemma left_segment_subset {R : ℝ} {x v : Space} (hv : ‖v‖ = 1)
    (hseg : segment ℝ x (x + v) ⊆ closedBall (0 : Space) R) :
    segment ℝ (leftStart R x v) (leftStart R x v + v) ⊆ closedBall (0 : Space) R := by
  obtain ⟨hR, hD, hlo, hhi, -⟩ := chord_bounds hv hseg
  rw [segment_unit_eq]
  rintro _ ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩
  have he : leftStart R x v + θ • v = x + (chordLow R x v + θ) • v := by
    simp only [leftStart]; module
  show leftStart R x v + θ • v ∈ _
  rw [he, mem_closedBall_iff_chord hv hR hD]
  constructor <;> linarith

lemma right_segment_subset {R : ℝ} {x v : Space} (hv : ‖v‖ = 1)
    (hseg : segment ℝ x (x + v) ⊆ closedBall (0 : Space) R) :
    segment ℝ (rightStart R x v) (rightStart R x v + v) ⊆ closedBall (0 : Space) R := by
  obtain ⟨hR, hD, hlo, hhi, -⟩ := chord_bounds hv hseg
  rw [segment_unit_eq]
  rintro _ ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩
  have he : rightStart R x v + θ • v = x + (chordHigh R x v - 1 + θ) • v := by
    simp only [rightStart]; module
  show rightStart R x v + θ • v ∈ _
  rw [he, mem_closedBall_iff_chord hv hR hD]
  constructor <;> linarith

lemma norm_leftStart {R : ℝ} {x v : Space} (hv : ‖v‖ = 1)
    (hseg : segment ℝ x (x + v) ⊆ closedBall (0 : Space) R) :
    ‖leftStart R x v‖ = R := by
  obtain ⟨hR, hD, -, -, -⟩ := chord_bounds hv hseg
  have hsq : ‖leftStart R x v‖ ^ 2 = R ^ 2 := by
    unfold leftStart
    rw [norm_add_smul_sq hv]
    have hs := Real.sq_sqrt hD
    unfold chordLow
    unfold chordDisc at hs ⊢
    nlinarith
  have := (sq_eq_sq₀ (norm_nonneg _) hR).mp hsq
  exact this

lemma norm_rightEnd {R : ℝ} {x v : Space} (hv : ‖v‖ = 1)
    (hseg : segment ℝ x (x + v) ⊆ closedBall (0 : Space) R) :
    ‖rightStart R x v + v‖ = R := by
  obtain ⟨hR, hD, -, -, -⟩ := chord_bounds hv hseg
  have hsq : ‖rightStart R x v + v‖ ^ 2 = R ^ 2 := by
    have he : rightStart R x v + v = x + chordHigh R x v • v := by
      simp only [rightStart]; module
    rw [he, norm_add_smul_sq hv]
    have hs := Real.sq_sqrt hD
    unfold chordHigh
    unfold chordDisc at hs ⊢
    nlinarith
  exact (sq_eq_sq₀ (norm_nonneg _) hR).mp hsq


lemma segment_subset_closedBall_of_tube {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {x v : Space}
    (h : Tube δ x v ⊆ ball (0 : Space) 1) :
    segment ℝ x (x + v) ⊆ closedBall (0 : Space) (1 - δ) := by
  intro z hz
  rw [mem_closedBall_zero_iff]
  by_contra hlt'
  have hlt := not_le.mp hlt'
  have hz1 : ‖z‖ < 1 := by
    have := h (show z ∈ Tube δ x v from self_subset_thickening hδ _ hz)
    simpa using this
  have hzpos : 0 < ‖z‖ := by linarith
  set c : ℝ := (1 - ‖z‖ + δ) / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hcδ : c < δ := by rw [hc]; linarith
  set y : Space := z + (c / ‖z‖) • z with hydef
  have hy : y ∈ ball z δ := by
    rw [mem_ball, dist_eq_norm]
    have : y - z = (c / ‖z‖) • z := by rw [hydef]; abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hc0 hzpos),
      div_mul_cancel₀ _ hzpos.ne']
    exact hcδ
  have hyb := h (show y ∈ Tube δ x v from ball_subset_thickening hz δ hy)
  rw [mem_ball_zero_iff] at hyb
  have hny : ‖y‖ = ‖z‖ + c := by
    have : y = (1 + c / ‖z‖) • z := by rw [hydef]; module
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), add_mul, one_mul,
      div_mul_cancel₀ _ hzpos.ne']
  rw [hny, hc] at hyb
  linarith

lemma tube_subset_ball_of_segment {δ : ℝ} {p v : Space}
    (h : segment ℝ p (p + v) ⊆ closedBall (0 : Space) (1 - δ)) :
    Tube δ p v ⊆ ball (0 : Space) 1 := by
  intro y hy
  obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.mp hy
  have hz' := mem_closedBall_zero_iff.mp (h hz)
  rw [mem_ball_zero_iff]
  have h1 := norm_sub_norm_le y z
  rw [dist_eq_norm] at hyz
  linarith

lemma tube_cover {δ R : ℝ} {x v : Space} (hv : ‖v‖ = 1) (hR1 : R ≤ 1)
    (hseg : segment ℝ x (x + v) ⊆ closedBall (0 : Space) R) :
    Tube δ x v ⊆ Tube δ (leftStart R x v) v ∪ Tube δ (rightStart R x v) v := by
  unfold Tube
  rw [← thickening_union]
  exact thickening_subset_of_subset δ (segment_cover hv hR1 hseg)

lemma tube_shift {δ s : ℝ} {p v y : Space}
    (hy : y ∈ Tube δ (p + s • v) v) : y - s • v ∈ Tube δ p v := by
  obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.mp hy
  rw [segment_unit_eq] at hz
  obtain ⟨θ, hθ, rfl⟩ := hz
  refine mem_thickening_iff.mpr ⟨p + θ • v, ?_, ?_⟩
  · rw [segment_unit_eq]; exact ⟨θ, hθ, rfl⟩
  · have : y - s • v - (p + θ • v) = y - (p + s • v + θ • v) := by abel
    rw [dist_eq_norm, this, ← dist_eq_norm]; exact hyz

lemma canonical_tube_reverse (δ : ℝ) (p v : Space) : Tube δ p v = Tube δ (p + v) (-v) := by
  unfold Tube
  rw [show p + v + -v = p by abel, segment_symm]

lemma left_mem_tube {δ : ℝ} (hδ : 0 < δ) (p v : Space) : p ∈ Tube δ p v :=
  self_subset_thickening hδ _ (left_mem_segment ℝ _ _)

lemma right_mem_tube {δ : ℝ} (hδ : 0 < δ) (p v : Space) : p + v ∈ Tube δ p v :=
  self_subset_thickening hδ _ (right_mem_segment ℝ _ _)

lemma eq_leftStart_add (R : ℝ) (x v : Space) :
    x = leftStart R x v + (-chordLow R x v) • v := by
  simp only [leftStart]; module

lemma eq_rightStart_add (R : ℝ) (x v : Space) :
    x = rightStart R x v + (1 - chordHigh R x v) • v := by
  simp only [rightStart]; module

lemma chord_shift_bounds {R : ℝ} {x v : Space} (hv : ‖v‖ = 1) (hR1 : R ≤ 1)
    (hseg : segment ℝ x (x + v) ⊆ closedBall (0 : Space) R) :
    |-chordLow R x v| ≤ 1 ∧ |1 - chordHigh R x v| ≤ 1 := by
  obtain ⟨-, -, hlo, hhi, hlen⟩ := chord_bounds hv hseg
  constructor <;> rw [abs_le] <;> constructor <;> linarith

/-- Counting transfer for families related by bounded shifts along their own direction. -/
theorem convex_count_transfer {n k : ℕ} (T : Fin n → Set Space) (T' : Fin k → Set Space)
    (g : Fin k → Fin n) (hg : Function.Injective g)
    (hint : ∀ j, (interior (T' j)).Nonempty) (hball : ∀ j, T' j ⊆ ball (0 : Space) 1)
    (hshift : ∀ j, ∃ q ∈ T' j, ∃ z ∈ T' j, ∃ s : ℝ, |s| ≤ 1 ∧
      ∀ y ∈ T (g j), y - s • (q - z) ∈ T' j)
    {M : ℝ} (hM : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (ncard {i | T i ⊆ W} : ℝ) ≤ ENNReal.ofReal M * volume W) :
    ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (ncard {j | T' j ⊆ W} : ℝ) ≤ ENNReal.ofReal (48 ^ 3 * M) * volume W := by
  intro W hW
  set W₁ := W ∩ ball (0 : Space) 1 with hW₁
  have hW₁c : Convex ℝ W₁ := hW.inter (convex_ball 0 1)
  have hW₁b : Bornology.IsBounded W₁ := isBounded_ball.subset inter_subset_right
  have hsub : ∀ j, T' j ⊆ W → T' j ⊆ W₁ := fun j h => subset_inter h (hball j)
  by_cases hne : (interior W₁).Nonempty
  · obtain ⟨U, hUc, hUvol, hUmem⟩ :=
      WangZahlLot.Obl.wz_normalized_projection_iteration.exists_convex_difference_container
        hW₁c hW₁b hne (le_refl (1 : ℝ))
    have hmap : ∀ j, T' j ⊆ W → T (g j) ⊆ U := by
      intro j hj y hy
      obtain ⟨q, hq, z, hz, s, hs, hmem⟩ := hshift j
      have hy₀ := hsub j hj (hmem y hy)
      have hq₁ := hsub j hj hq
      have hz₁ := hsub j hj hz
      have hA : y - s • (q - z) ∈ U := by
        simpa using hUmem (y - s • (q - z)) hy₀ z hz₁ z hz₁
      rcases le_total 0 s with hs0 | hs0
      · have hB : (y - s • (q - z)) + (q - z) ∈ U := by
          simpa using hUmem (y - s • (q - z)) hy₀ q hq₁ z hz₁
        have hs1 : s ≤ 1 := (le_abs_self s).trans hs
        have hc := hUc hA hB (by linarith : (0:ℝ) ≤ 1 - s) hs0 (by ring)
        convert hc using 1
        module
      · have hB : (y - s • (q - z)) + (z - q) ∈ U := by
          simpa using hUmem (y - s • (q - z)) hy₀ z hz₁ q hq₁
        have hs1 : -s ≤ 1 := (neg_le_abs s).trans hs
        have hc := hUc hA hB (by linarith : (0:ℝ) ≤ 1 + s) (by linarith : (0:ℝ) ≤ -s)
          (by ring)
        convert hc using 1
        module
    have hcard : (ncard {j | T' j ⊆ W} : ℝ) ≤ ncard {i | T i ⊆ U} := by
      exact_mod_cast ncard_le_ncard_of_injOn g (fun j hj => hmap j hj) hg.injOn
    calc ENNReal.ofReal (ncard {j | T' j ⊆ W} : ℝ)
        ≤ ENNReal.ofReal (ncard {i | T i ⊆ U} : ℝ) := ENNReal.ofReal_le_ofReal hcard
      _ ≤ ENNReal.ofReal M * volume U := hM U hUc
      _ = ENNReal.ofReal M * (ENNReal.ofReal ((48 * 1) ^ 3) * volume W₁) := by rw [hUvol]
      _ = ENNReal.ofReal (48 ^ 3 * M) * volume W₁ := by
        rw [← mul_assoc, mul_comm (ENNReal.ofReal M), ← ENNReal.ofReal_mul (by norm_num)]
        norm_num
      _ ≤ ENNReal.ofReal (48 ^ 3 * M) * volume W := by
        gcongr
        exact inter_subset_left
  · have hempty : {j | T' j ⊆ W} = ∅ := by
      ext j
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro hj
      obtain ⟨y, hy⟩ := hint j
      exact hne ⟨y, interior_mono (hsub j hj) hy⟩
    rw [hempty, ncard_empty]
    simp


lemma midpoint_norm_sq_le {p w : Space} (hw : ‖w‖ = 1)
    (hseg : segment ℝ p (p + w) ⊆ closedBall (0 : Space) 1) :
    ‖p + (1 / 2 : ℝ) • w‖ ^ 2 ≤ 3 / 4 := by
  have hp : ‖p‖ ≤ 1 := mem_closedBall_zero_iff.mp (hseg (left_mem_segment ℝ _ _))
  have hpw : ‖p + w‖ ≤ 1 := mem_closedBall_zero_iff.mp (hseg (right_mem_segment ℝ _ _))
  have e1 : ‖p + (1 / 2 : ℝ) • w‖ ^ 2 = ‖p‖ ^ 2 + inner ℝ p w + 1 / 4 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, hw]; norm_num; ring
  have e2 : ‖p + w‖ ^ 2 = ‖p‖ ^ 2 + 2 * inner ℝ p w + 1 := by
    rw [norm_add_sq_real, hw]; ring
  have h1 : ‖p‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg p]
  have h2 : ‖p + w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (p + w)]
  nlinarith

lemma norm_le_of_repr_le (b : OrthonormalBasis (Fin 3) ℝ Space) (z : Space) {c : ℝ}
    (hz : ∀ i, |b.repr z i| ≤ c) : ‖z‖ ^ 2 ≤ 3 * c ^ 2 := by
  have hn : ‖z‖ ^ 2 = ∑ i, (b.repr z i) ^ 2 := by
    rw [← b.repr.norm_map, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hn, Fin.sum_univ_three]
  have h0 := sq_le_sq' (abs_le.mp (hz 0)).1 (abs_le.mp (hz 0)).2
  have h1 := sq_le_sq' (abs_le.mp (hz 1)).1 (abs_le.mp (hz 1)).2
  have h2 := sq_le_sq' (abs_le.mp (hz 2)).1 (abs_le.mp (hz 2)).2
  linarith

/-- A slab of the unit ball containing a unit tube has volume at least `min r (1/20) / 100`. -/
lemma slab_volume_lower {δ : ℝ} (hδ : 0 < δ) {p w u : Space} (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    (hseg : segment ℝ p (p + w) ⊆ closedBall (0 : Space) 1) {t r : ℝ} (hr : 0 < r)
    (hsub : Tube δ p w ⊆ {y | |inner ℝ u y - t| ≤ r}) :
    ENNReal.ofReal (min r (1 / 20) / 100) ≤
      volume (ball (0 : Space) 1 ∩ {y | |inner ℝ u y - t| ≤ r}) := by
  set m : Space := p + (1 / 2 : ℝ) • w with hm
  have hmseg : m ∈ segment ℝ p (p + w) := by
    rw [segment_unit_eq]; exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
  have hmslab : |inner ℝ u m - t| ≤ r := hsub (self_subset_thickening hδ _ hmseg)
  have hmnorm : ‖m‖ ^ 2 ≤ 3 / 4 := midpoint_norm_sq_le hw hseg
  obtain ⟨b, hb⟩ := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.exists_basis_first hu
  set h : ℝ := min r (1 / 20) with hh
  have hh0 : 0 < h := lt_min hr (by norm_num)
  have hhr : h ≤ r := min_le_left _ _
  have hh20 : h ≤ 1 / 20 := min_le_right _ _
  set s0 : ℝ := inner ℝ u m - t with hs0
  obtain ⟨l0, hl0, hlr, hlbox⟩ : ∃ l0 : ℝ, -h ≤ l0 ∧ l0 + h ≤ h ∧
      ∀ c, l0 ≤ c → c ≤ l0 + h → |s0 + c| ≤ r := by
    rcases le_total s0 0 with hneg | hpos
    · refine ⟨0, by linarith, by linarith, fun c hc1 hc2 => abs_le.mpr ⟨?_, ?_⟩⟩
      · linarith [(abs_le.mp hmslab).1]
      · linarith
    · refine ⟨-h, le_refl _, by linarith, fun c hc1 hc2 => abs_le.mpr ⟨?_, ?_⟩⟩
      · linarith
      · linarith [(abs_le.mp hmslab).2]
  let lo : Fin 3 → ℝ := ![l0, -(1 / 20), -(1 / 20)]
  let hi : Fin 3 → ℝ := ![l0 + h, 1 / 20, 1 / 20]
  have hbox : {y : Space | ∀ i, lo i ≤ b.repr (y - m) i ∧ b.repr (y - m) i ≤ hi i} ⊆
      ball (0 : Space) 1 ∩ {y | |inner ℝ u y - t| ≤ r} := by
    intro y hy
    have hc : ∀ i, |b.repr (y - m) i| ≤ 1 / 20 := by
      intro i
      fin_cases i
      · have := hy 0; simp only [lo, hi] at this
        exact abs_le.mpr ⟨by simp at this ⊢; linarith [this.1], by simp at this ⊢; linarith [this.2]⟩
      · have := hy 1; simpa [lo, hi, abs_le] using this
      · have := hy 2; simpa [lo, hi, abs_le] using this
    have hym := norm_le_of_repr_le b (y - m) hc
    constructor
    · rw [mem_ball_zero_iff]
      have hmn : ‖m‖ ≤ 87 / 100 := by nlinarith [norm_nonneg m]
      have hymn : ‖y - m‖ ≤ 9 / 100 := by nlinarith [norm_nonneg (y - m)]
      have := norm_sub_norm_le y m
      linarith
    · have h0 := hy 0
      simp only [lo, hi, Matrix.cons_val_zero] at h0
      have hrep : b.repr (y - m) 0 = inner ℝ u y - inner ℝ u m := by
        rw [OrthonormalBasis.repr_apply_apply, hb, inner_sub_right]
      rw [hrep] at h0
      have := hlbox (inner ℝ u y - inner ℝ u m) h0.1 h0.2
      simp only [mem_ofPred_eq]
      convert this using 2
      rw [hs0]; ring
  calc ENNReal.ofReal (min r (1 / 20) / 100)
      = volume {y : Space | ∀ i, lo i ≤ b.repr (y - m) i ∧ b.repr (y - m) i ≤ hi i} := by
        rw [WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.coordinate_box_volume]
        simp only [Fin.prod_univ_three, lo, hi, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        have e1 : l0 + h - l0 = h := by ring
        rw [e1, ← ENNReal.ofReal_mul hh0.le,
          ← ENNReal.ofReal_mul (mul_nonneg hh0.le (by norm_num))]
        congr 1
        ring
    _ ≤ _ := measure_mono hbox


lemma slab_count_transfer {δ : ℝ} (hδ : 0 < δ) {n k : ℕ} (T : Fin n → Set Space)
    (p w : Fin k → Space) (g : Fin k → Fin n) (hg : Function.Injective g)
    (hw : ∀ j, ‖w j‖ = 1) (hseg : ∀ j, segment ℝ (p j) (p j + w j) ⊆ closedBall (0 : Space) 1)
    (hTball : ∀ i, T i ⊆ ball (0 : Space) 1)
    (hshift : ∀ j, ∃ s : ℝ, |s| ≤ 1 ∧ ∀ y ∈ T (g j), y - s • w j ∈ Tube δ (p j) (w j))
    {L : ℝ} (hL : 0 ≤ L) (hcount : ∀ (u : Space) (t r : ℝ), ‖u‖ = 1 → 0 < r →
      ENNReal.ofReal (ncard {i | T i ⊆ ball (0 : Space) 1 ∩ {y | |inner ℝ u y - t| ≤ r}} : ℝ) ≤
        ENNReal.ofReal L * volume (ball (0 : Space) 1 ∩ {y | |inner ℝ u y - t| ≤ r})) :
    ∀ (u : Space) (t r : ℝ), ‖u‖ = 1 → 0 < r →
      ENNReal.ofReal (ncard {j | Tube δ (p j) (w j) ⊆
          ball (0 : Space) 1 ∩ {y | |inner ℝ u y - t| ≤ r}} : ℝ) ≤
        ENNReal.ofReal (16000 * L) *
          volume (ball (0 : Space) 1 ∩ {y | |inner ℝ u y - t| ≤ r}) := by
  intro u t r hu hr
  set S := {j | Tube δ (p j) (w j) ⊆ ball (0 : Space) 1 ∩ {y | |inner ℝ u y - t| ≤ r}}
    with hS
  rcases S.eq_empty_or_nonempty with hemp | ⟨j₀, hj₀⟩
  · rw [hemp, ncard_empty]; simp
  have hlow := slab_volume_lower hδ (hw j₀) hu (hseg j₀) hr (fun y hy => (hj₀ hy).2)
  have hmap : ∀ j ∈ S, T (g j) ⊆ ball (0 : Space) 1 ∩ {y | |inner ℝ u y - t| ≤ 3 * r} := by
    intro j hj y hy
    obtain ⟨s, hs, hmem⟩ := hshift j
    refine ⟨hTball (g j) hy, ?_⟩
    have h₀ := (hj (hmem y hy)).2
    have hp := (hj (left_mem_tube hδ (p j) (w j))).2
    have hpw := (hj (right_mem_tube hδ (p j) (w j))).2
    simp only [mem_ofPred_eq] at h₀ hp hpw ⊢
    have huw : |inner ℝ u (w j)| ≤ 2 * r := by
      have he : inner ℝ u (w j) = (inner ℝ u (p j + w j) - t) - (inner ℝ u (p j) - t) := by
        rw [inner_add_right]; ring
      rw [he]
      calc _ ≤ |inner ℝ u (p j + w j) - t| + |inner ℝ u (p j) - t| := abs_sub _ _
        _ ≤ r + r := add_le_add hpw hp
        _ = 2 * r := by ring
    have he : inner ℝ u y - t = (inner ℝ u (y - s • w j) - t) + s * inner ℝ u (w j) := by
      rw [inner_sub_right, inner_smul_right]; ring
    rw [he]
    calc _ ≤ |inner ℝ u (y - s • w j) - t| + |s * inner ℝ u (w j)| := abs_add_le _ _
      _ ≤ r + 1 * (2 * r) := by
        rw [abs_mul]
        exact add_le_add h₀ (mul_le_mul hs huw (abs_nonneg _) zero_le_one)
      _ = 3 * r := by ring
  have hcard : (ncard S : ℝ) ≤
      ncard {i | T i ⊆ ball (0 : Space) 1 ∩ {y | |inner ℝ u y - t| ≤ 3 * r}} := by
    exact_mod_cast ncard_le_ncard_of_injOn g (fun j hj => hmap j hj) hg.injOn
  have hvol3 : volume (ball (0 : Space) 1 ∩ {y | |inner ℝ u y - t| ≤ 3 * r}) ≤
      ENNReal.ofReal (160 * min r (1 / 20)) := by
    rcases le_total r (1 / 20) with hr20 | hr20
    · have h8 := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.slab_volume_le hu t (3 * r)
        (by linarith)
      refine h8.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [min_eq_left hr20]; linarith
    · have hball : ball (0 : Space) 1 ∩ {y | |inner ℝ u y - t| ≤ 3 * r} ⊆
          ball (0 : Space) 1 ∩ {y | |inner ℝ u y - 0| ≤ 1} := by
        rintro y ⟨hy, -⟩
        refine ⟨hy, ?_⟩
        simp only [mem_ofPred_eq, sub_zero]
        exact (abs_real_inner_le_norm u y).trans
          (by rw [hu, one_mul]; exact (mem_ball_zero_iff.mp hy).le)
      have h8 := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.slab_volume_le hu 0 1
        zero_le_one
      refine (measure_mono hball).trans (h8.trans (ENNReal.ofReal_le_ofReal ?_))
      rw [min_eq_right hr20]; norm_num
  have hmin : 0 ≤ min r (1 / 20) := le_min hr.le (by norm_num)
  calc ENNReal.ofReal (ncard S : ℝ)
      ≤ ENNReal.ofReal
          (ncard {i | T i ⊆ ball (0 : Space) 1 ∩ {y | |inner ℝ u y - t| ≤ 3 * r}} : ℝ) :=
        ENNReal.ofReal_le_ofReal hcard
    _ ≤ ENNReal.ofReal L * volume (ball (0 : Space) 1 ∩ {y | |inner ℝ u y - t| ≤ 3 * r}) :=
        hcount u t (3 * r) hu (by linarith)
    _ ≤ ENNReal.ofReal L * ENNReal.ofReal (160 * min r (1 / 20)) := by gcongr
    _ = ENNReal.ofReal (16000 * L) * ENNReal.ofReal (min r (1 / 20) / 100) := by
        rw [← ENNReal.ofReal_mul hL, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
    _ ≤ ENNReal.ofReal (16000 * L) *
          volume (ball (0 : Space) 1 ∩ {y | |inner ℝ u y - t| ≤ r}) := by
        gcongr

lemma repr_abs_le_norm (b : OrthonormalBasis (Fin 3) ℝ Space) (z : Space) (i : Fin 3) :
    |b.repr z i| ≤ ‖z‖ := by
  rw [OrthonormalBasis.repr_apply_apply]
  exact (abs_real_inner_le_norm _ _).trans (by rw [b.norm_eq_one, one_mul])

lemma norm_sq_eq_sum_repr (b : OrthonormalBasis (Fin 3) ℝ Space) (z : Space) :
    ‖z‖ ^ 2 = (b.repr z 0) ^ 2 + (b.repr z 1) ^ 2 + (b.repr z 2) ^ 2 := by
  rw [← b.repr.norm_map, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Real.norm_eq_abs, sq_abs, Fin.sum_univ_three]

/-- A unit tube contains a box of volume `49/25 δ²`. -/
lemma tube_volume_lower_box {δ : ℝ} (hδ : 0 < δ) (p : Space) {w : Space} (hw : ‖w‖ = 1) :
    ENNReal.ofReal (49 / 25 * δ ^ 2) ≤ volume (Tube δ p w) := by
  obtain ⟨b, hb⟩ := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.exists_basis_first hw
  let lo : Fin 3 → ℝ := ![0, -(7 / 10 * δ), -(7 / 10 * δ)]
  let hi : Fin 3 → ℝ := ![1, 7 / 10 * δ, 7 / 10 * δ]
  have hbox : {y : Space | ∀ i, lo i ≤ b.repr (y - p) i ∧ b.repr (y - p) i ≤ hi i} ⊆
      Tube δ p w := by
    intro y hy
    have h0 := hy 0
    have h1 := hy 1
    have h2 := hy 2
    simp only [lo, hi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
    refine mem_thickening_iff.mpr ⟨p + b.repr (y - p) 0 • w, ?_, ?_⟩
    · rw [segment_unit_eq]; exact ⟨_, ⟨h0.1, h0.2⟩, rfl⟩
    · rw [dist_eq_norm]
      have hrep : ∀ i, b.repr (y - (p + b.repr (y - p) 0 • w)) i =
          b.repr (y - p) i - b.repr (y - p) 0 * (if i = 0 then 1 else 0) := by
        intro i
        have : y - (p + b.repr (y - p) 0 • w) = (y - p) - b.repr (y - p) 0 • b 0 := by
          rw [hb]; abel
        rw [this, map_sub, map_smul, OrthonormalBasis.repr_self]
        simp
      have hsq := norm_sq_eq_sum_repr b (y - (p + b.repr (y - p) 0 • w))
      rw [hrep 0, hrep 1, hrep 2] at hsq
      simp only [ite_true, mul_one, sub_self, show (1 : Fin 3) ≠ 0 by decide,
        show (2 : Fin 3) ≠ 0 by decide, ite_false, mul_zero, sub_zero] at hsq
      have hs1 : (b.repr (y - p) 1) ^ 2 ≤ (7 / 10 * δ) ^ 2 :=
        sq_le_sq' (by linarith [h1.1]) h1.2
      have hs2 : (b.repr (y - p) 2) ^ 2 ≤ (7 / 10 * δ) ^ 2 :=
        sq_le_sq' (by linarith [h2.1]) h2.2
      have hlt : ‖y - (p + b.repr (y - p) 0 • w)‖ ^ 2 < δ ^ 2 := by nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 hδ.le hlt
  calc ENNReal.ofReal (49 / 25 * δ ^ 2)
      = volume {y : Space | ∀ i, lo i ≤ b.repr (y - p) i ∧ b.repr (y - p) i ≤ hi i} := by
        rw [WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.coordinate_box_volume]
        simp only [Fin.prod_univ_three, lo, hi, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        rw [← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) (by linarith))]
        congr 1; ring
    _ ≤ _ := measure_mono hbox


/-- Close starts and directions give containment of unit tubes. -/
lemma tube_subset_of_params_close {δ ρ : ℝ} {x v z w : Space}
    (h : ‖x - z‖ + ‖v - w‖ ≤ ρ - δ) : Tube δ x v ⊆ Tube ρ z w := by
  intro y hy
  obtain ⟨p, hp, hyp⟩ := mem_thickening_iff.mp hy
  rw [segment_unit_eq] at hp
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hp
  refine mem_thickening_iff.mpr ⟨z + t • w, ?_, ?_⟩
  · rw [segment_unit_eq]; exact ⟨t, ⟨ht0, ht1⟩, rfl⟩
  · have e : x + t • v - (z + t • w) = (x - z) + t • (v - w) := by module
    have hb : ‖x + t • v - (z + t • w)‖ ≤ ρ - δ := by
      rw [e]
      calc ‖(x - z) + t • (v - w)‖ ≤ ‖x - z‖ + ‖t • (v - w)‖ := norm_add_le _ _
        _ = ‖x - z‖ + t * ‖v - w‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
        _ ≤ ‖x - z‖ + 1 * ‖v - w‖ := by gcongr
        _ ≤ ρ - δ := by linarith
    calc dist y (z + t • w) ≤ dist y (x + t • v) + dist (x + t • v) (z + t • w) :=
          dist_triangle _ _ _
      _ < δ + (ρ - δ) := by rw [dist_eq_norm (x + t • v)]; linarith
      _ = ρ := by ring

/-- Containment of a unit `δ`-tube in a unit `ρ`-tube whose direction is in the same half space
forces close directions and close start points. -/
lemma params_close_of_tube_subset {δ ρ : ℝ} (hδ : 0 < δ) {x v z w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hvw : 0 ≤ inner ℝ v w) (hρ : ρ ≤ 1 / 4)
    (hsub : Tube δ x v ⊆ Tube ρ z w) :
    ‖v - w‖ < 4 * ρ ∧ ‖x - z‖ < 4 * ρ := by
  have hseg : segment ℝ x (x + v) ⊆ Tube ρ z w :=
    (self_subset_thickening hδ _).trans hsub
  obtain ⟨p, hp, hxp⟩ := mem_thickening_iff.mp (hseg (left_mem_segment ℝ x (x + v)))
  obtain ⟨q, hq, hxq⟩ := mem_thickening_iff.mp (hseg (right_mem_segment ℝ x (x + v)))
  rw [segment_unit_eq] at hp hq
  obtain ⟨a, ⟨ha0, ha1⟩, rfl⟩ := hp
  obtain ⟨b, ⟨hb0, hb1⟩, rfl⟩ := hq
  rw [dist_eq_norm] at hxp hxq
  have hvd : ‖v - (b - a) • w‖ < 2 * ρ := by
    have he : v - (b - a) • w = (x + v - (z + b • w)) - (x - (z + a • w)) := by module
    rw [he]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  have hba : 1 - 2 * ρ < b - a := by
    -- otherwise `v` would be close to a nonpositive multiple of `w`
    by_contra hle
    have hle' : b - a ≤ 1 - 2 * ρ := not_lt.mp hle
    rcases le_or_gt (b - a) 0 with hneg | hpos
    · -- `‖v - s w‖ ≥ 1` for `s ≤ 0` since `⟨v, w⟩ ≥ 0`
      have hge : 1 ≤ ‖v - (b - a) • w‖ := by
        have hsq : ‖v - (b - a) • w‖ ^ 2 = 1 - 2 * (b - a) * inner ℝ v w + (b - a) ^ 2 := by
          rw [norm_sub_sq_real, inner_smul_right, norm_smul, hv, hw, Real.norm_eq_abs, mul_one,
            sq_abs]
          ring
        have h1 : 1 ≤ ‖v - (b - a) • w‖ ^ 2 := by nlinarith
        nlinarith [norm_nonneg (v - (b - a) • w)]
      linarith
    · have hge : ‖v‖ - ‖(b - a) • w‖ ≤ ‖v - (b - a) • w‖ := norm_sub_norm_le _ _
      rw [hv, norm_smul, hw, Real.norm_eq_abs, abs_of_pos hpos, mul_one] at hge
      linarith
  have hba1 : b - a ≤ 1 := by linarith
  have hvw' : ‖v - w‖ < 4 * ρ := by
    have he : v - w = (v - (b - a) • w) - (1 - (b - a)) • w := by module
    rw [he]
    calc ‖(v - (b - a) • w) - (1 - (b - a)) • w‖
        ≤ ‖v - (b - a) • w‖ + ‖(1 - (b - a)) • w‖ := norm_sub_le _ _
      _ = ‖v - (b - a) • w‖ + (1 - (b - a)) := by
          rw [norm_smul, hw, Real.norm_eq_abs, abs_of_nonneg (by linarith), mul_one]
      _ < 2 * ρ + 2 * ρ := by linarith
      _ = 4 * ρ := by ring
  refine ⟨hvw', ?_⟩
  -- the start: average the two endpoint estimates
  have he : x - z = (1 / 2 : ℝ) • ((x - (z + a • w)) + (x + v - (z + b • w))) -
      (1 / 2 : ℝ) • (v - w) + ((a + b - 1) / 2) • w := by module
  have hab : |a + b - 1| ≤ 1 - (b - a) := by
    rw [abs_le]; constructor <;> linarith
  have n1 : ‖(1 / 2 : ℝ) • ((x - (z + a • w)) + (x + v - (z + b • w)))‖ =
      (1 / 2) * ‖(x - (z + a • w)) + (x + v - (z + b • w))‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
  have n2 : ‖(1 / 2 : ℝ) • (v - w)‖ = (1 / 2) * ‖v - w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
  have n3 : ‖((a + b - 1) / 2) • w‖ = |a + b - 1| / 2 := by
    rw [norm_smul, hw, mul_one, Real.norm_eq_abs, abs_div, abs_two]
  have hsum := norm_add_le (x - (z + a • w)) (x + v - (z + b • w))
  have htri : ‖(1 / 2 : ℝ) • ((x - (z + a • w)) + (x + v - (z + b • w))) - (1 / 2 : ℝ) • (v - w) +
        ((a + b - 1) / 2) • w‖ ≤
      ‖(1 / 2 : ℝ) • ((x - (z + a • w)) + (x + v - (z + b • w)))‖ +
          ‖(1 / 2 : ℝ) • (v - w)‖ + ‖((a + b - 1) / 2) • w‖ :=
    (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
  rw [n1, n2, n3] at htri
  have habs : |a + b - 1| < 2 * ρ := by linarith
  rw [he]
  calc _ ≤ _ := htri
    _ < (1 / 2) * (ρ + ρ) + (1 / 2) * (4 * ρ) + (2 * ρ) / 2 := by
        have h1 : ‖(x - (z + a • w)) + (x + v - (z + b • w))‖ < ρ + ρ := by
          exact hsum.trans_lt (add_lt_add hxp hxq)
        linarith
    _ = 4 * ρ := by ring

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
