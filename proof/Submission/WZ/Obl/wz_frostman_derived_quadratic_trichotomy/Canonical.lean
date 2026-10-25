-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.Canonical.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
/-!
# Canonical chord positions of unit tubes

Step 1 of the repair of o038 (see `Repair.lean`): move each tube to a canonical unit
subsegment of its chord, so that tubes on nearby lines are axially aligned.

For a unit vector `v` and a δ-tube `thickening δ [x, x + v]` inside `B(0,1)`, let
`p = x - ⟪x, v⟫ v` be the foot of the perpendicular from `0` to the line `x + ℝ v` and
`h = √((1-δ)² - ‖p‖²)`. The unit segments of the line with both ends in the closed ball
`B(0, 1-δ)` are the `[p + s v, p + (s+1) v]` with `-h ≤ s ≤ h - 1`. The two extreme ones start
at `leftStart = p - h v` and `rightStart = p + (h-1) v`.

`canonical_tubes`: both canonical tubes lie in `B(0,1)`, and the tube lies in their union.
`canonical_split`: each shading keeps at least half of its measure in one of the two.
-/

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy

/-- The ambient space. -/
abbrev Sp := LeanEval.Analysis.WangZahlKakeya.Space

/-- If a δ-ball around `y` lies in the unit ball, then `‖y‖ + δ ≤ 1`. -/
lemma norm_add_le_of_ball_subset {y : Sp} {δ : ℝ} (hδ : 0 < δ)
    (h : Metric.ball y δ ⊆ Metric.ball (0 : Sp) 1) : ‖y‖ + δ ≤ 1 := by
  by_contra hcon
  rw [not_le] at hcon
  set c : ℝ := max 0 (1 - ‖y‖) with hc
  have hc0 : 0 ≤ c := le_max_left _ _
  have hcδ : c < δ := max_lt hδ (by linarith)
  have hc1 : 1 ≤ ‖y‖ + c := by
    rcases le_total 0 (1 - ‖y‖) with h1 | h1
    · rw [hc, max_eq_right h1]; linarith
    · rw [hc, max_eq_left h1]; linarith
  by_cases hy : y = 0
  · subst hy
    have hu : ‖(EuclideanSpace.single 0 1 : Sp)‖ = 1 := by simp
    have hmem : c • (EuclideanSpace.single 0 1 : Sp) ∈ Metric.ball (0 : Sp) δ := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0, hu, mul_one]
      exact hcδ
    have h2 := h hmem
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0, hu, mul_one] at h2
    rw [norm_zero, zero_add] at hc1
    linarith
  · have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hz1 : ‖(1 + c / ‖y‖) • y‖ = ‖y‖ + c := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), add_mul, one_mul,
        div_mul_cancel₀ c hny.ne']
    have hzy : dist ((1 + c / ‖y‖) • y) y = c := by
      rw [dist_eq_norm, add_smul, one_smul, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), div_mul_cancel₀ c hny.ne']
    have hmem : (1 + c / ‖y‖) • y ∈ Metric.ball y δ := by
      rw [Metric.mem_ball, hzy]; exact hcδ
    have h2 := h hmem
    rw [mem_ball_zero_iff, hz1] at h2
    linarith

/-- Points of a set whose δ-thickening lies in `B(0,1)` have norm at most `1 - δ`. -/
lemma norm_le_of_thickening_subset {s : Set Sp} {y : Sp} {δ : ℝ} (hδ : 0 < δ)
    (h : Metric.thickening δ s ⊆ Metric.ball (0 : Sp) 1) (hy : y ∈ s) : ‖y‖ ≤ 1 - δ := by
  have := norm_add_le_of_ball_subset hδ ((Metric.ball_subset_thickening hy δ).trans h)
  linarith

/-- A set of points of norm at most `1 - δ` has its δ-thickening in `B(0,1)`. -/
lemma thickening_subset_ball_of_norm_le {s : Set Sp} {δ : ℝ} (h : ∀ y ∈ s, ‖y‖ ≤ 1 - δ) :
    Metric.thickening δ s ⊆ Metric.ball (0 : Sp) 1 := by
  intro z hz
  obtain ⟨y, hy, hzy⟩ := Metric.mem_thickening_iff.1 hz
  rw [mem_ball_zero_iff]
  rw [dist_eq_norm] at hzy
  calc ‖z‖ = ‖y + (z - y)‖ := by rw [add_sub_cancel]
    _ ≤ ‖y‖ + ‖z - y‖ := norm_add_le _ _
    _ < (1 - δ) + δ := by linarith [h y hy]
    _ = 1 := by ring

/-- The foot of the perpendicular from `0` to the line `x + ℝ v`. -/
noncomputable def foot (x v : Sp) : Sp := x - (inner ℝ x v) • v

lemma inner_foot {x v : Sp} (hv : ‖v‖ = 1) : inner ℝ (foot x v) v = 0 := by
  unfold foot
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hv]
  ring

lemma foot_add_inner (x v : Sp) : foot x v + (inner ℝ x v) • v = x := by
  unfold foot; abel

lemma norm_foot_add_smul_sq {x v : Sp} (hv : ‖v‖ = 1) (t : ℝ) :
    ‖foot x v + t • v‖ ^ 2 = ‖foot x v‖ ^ 2 + t ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_right, inner_foot hv, norm_smul, Real.norm_eq_abs, hv]
  rw [mul_one, sq_abs]; ring

/-- Half the length of the chord of the line `x + ℝ v` in the closed ball `B(0, 1-δ)`. -/
noncomputable def halfChord (δ : ℝ) (x v : Sp) : ℝ :=
  Real.sqrt ((1 - δ) ^ 2 - ‖foot x v‖ ^ 2)

/-- Start of the left canonical unit segment. -/
noncomputable def leftStart (δ : ℝ) (x v : Sp) : Sp := foot x v - halfChord δ x v • v

/-- Start of the right canonical unit segment. -/
noncomputable def rightStart (δ : ℝ) (x v : Sp) : Sp := foot x v + (halfChord δ x v - 1) • v

/-- Points of the segment `[x, x + v]`. -/
lemma mem_segment_add_iff {x v z : Sp} :
    z ∈ segment ℝ x (x + v) ↔ ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ z = x + θ • v := by
  rw [segment_eq_image']
  simp only [add_sub_cancel_left, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨θ, ⟨h0, h1⟩, rfl⟩; exact ⟨θ, h0, h1, rfl⟩
  · rintro ⟨θ, h0, h1, rfl⟩; exact ⟨θ, ⟨h0, h1⟩, rfl⟩

/-- The chord facts: `-h ≤ ⟪x,v⟫`, `⟪x,v⟫ + 1 ≤ h`, `h ≤ 1 - δ` and
`h² = (1-δ)² - ‖p‖²`. -/
lemma chord_bounds {δ : ℝ} {x v : Sp} (hδ : 0 < δ) (hv : ‖v‖ = 1)
    (hT : Metric.thickening δ (segment ℝ x (x + v)) ⊆ Metric.ball (0 : Sp) 1) :
    -halfChord δ x v ≤ inner ℝ x v ∧ inner ℝ x v + 1 ≤ halfChord δ x v ∧
      halfChord δ x v ≤ 1 - δ ∧ 0 ≤ 1 - δ ∧
      halfChord δ x v ^ 2 = (1 - δ) ^ 2 - ‖foot x v‖ ^ 2 := by
  set p := foot x v with hp
  set s := inner ℝ x v with hs
  have hx := norm_le_of_thickening_subset hδ hT (left_mem_segment ℝ x (x + v))
  have hxv := norm_le_of_thickening_subset hδ hT (right_mem_segment ℝ x (x + v))
  have h1δ : 0 ≤ 1 - δ := le_trans (norm_nonneg _) hx
  have ex : x = p + s • v := (foot_add_inner x v).symm
  have exv : x + v = p + (s + 1) • v := by
    rw [ex, add_smul, one_smul, add_assoc]
  have nx : ‖x‖ ^ 2 = ‖p‖ ^ 2 + s ^ 2 := by rw [ex]; exact norm_foot_add_smul_sq hv s
  have nxv : ‖x + v‖ ^ 2 = ‖p‖ ^ 2 + (s + 1) ^ 2 := by
    rw [exv]; exact norm_foot_add_smul_sq hv (s + 1)
  have sx : ‖x‖ ^ 2 ≤ (1 - δ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have sxv : ‖x + v‖ ^ 2 ≤ (1 - δ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxv 2
  have hnn : 0 ≤ (1 - δ) ^ 2 - ‖p‖ ^ 2 := by nlinarith [sq_nonneg s]
  have hh2 : halfChord δ x v ^ 2 = (1 - δ) ^ 2 - ‖p‖ ^ 2 := Real.sq_sqrt hnn
  have habs1 : |s| ≤ halfChord δ x v := Real.abs_le_sqrt (by nlinarith)
  have habs2 : |s + 1| ≤ halfChord δ x v := Real.abs_le_sqrt (by nlinarith)
  have hh0 : 0 ≤ halfChord δ x v := Real.sqrt_nonneg _
  refine ⟨?_, ?_, ?_, h1δ, hh2⟩
  · linarith [neg_abs_le s]
  · linarith [le_abs_self (s + 1)]
  · nlinarith [sq_nonneg (‖p‖)]

/-- Points `p + t v` with `|t| ≤ h` have norm at most `1 - δ`. -/
lemma norm_foot_add_le {δ : ℝ} {x v : Sp} (hv : ‖v‖ = 1) (h1δ : 0 ≤ 1 - δ)
    (hh2 : halfChord δ x v ^ 2 = (1 - δ) ^ 2 - ‖foot x v‖ ^ 2) {t : ℝ}
    (ht1 : -halfChord δ x v ≤ t) (ht2 : t ≤ halfChord δ x v) :
    ‖foot x v + t • v‖ ≤ 1 - δ := by
  have hh0 : 0 ≤ halfChord δ x v := Real.sqrt_nonneg _
  have hn := norm_foot_add_smul_sq (x := x) hv t
  have ht : t ^ 2 ≤ halfChord δ x v ^ 2 := by nlinarith
  have hsq : ‖foot x v + t • v‖ ^ 2 ≤ (1 - δ) ^ 2 := by rw [hn]; linarith
  nlinarith [norm_nonneg (foot x v + t • v)]

lemma start_param (x v : Sp) (t : ℝ) : x + t • v = foot x v + (inner ℝ x v + t) • v := by
  conv_lhs => rw [← foot_add_inner x v]
  module

lemma leftStart_param (δ : ℝ) (x v : Sp) (t : ℝ) :
    leftStart δ x v + t • v = foot x v + (t - halfChord δ x v) • v := by
  unfold leftStart; module

lemma rightStart_param (δ : ℝ) (x v : Sp) (t : ℝ) :
    rightStart δ x v + t • v = foot x v + (halfChord δ x v - 1 + t) • v := by
  unfold rightStart; module

/-- Both canonical δ-tubes lie in `B(0,1)`, and the tube lies in their union. -/
theorem canonical_tubes {δ : ℝ} {x v : Sp} (hδ : 0 < δ) (hv : ‖v‖ = 1)
    (hT : Metric.thickening δ (segment ℝ x (x + v)) ⊆ Metric.ball (0 : Sp) 1) :
    Metric.thickening δ (segment ℝ (leftStart δ x v) (leftStart δ x v + v))
        ⊆ Metric.ball (0 : Sp) 1 ∧
      Metric.thickening δ (segment ℝ (rightStart δ x v) (rightStart δ x v + v))
        ⊆ Metric.ball (0 : Sp) 1 ∧
      Metric.thickening δ (segment ℝ x (x + v)) ⊆
        Metric.thickening δ (segment ℝ (leftStart δ x v) (leftStart δ x v + v)) ∪
          Metric.thickening δ (segment ℝ (rightStart δ x v) (rightStart δ x v + v)) := by
  obtain ⟨hs1, hs2, hh1, h1δ, hh2⟩ := chord_bounds hδ hv hT
  have hhalf : 1 / 2 ≤ halfChord δ x v := by linarith
  refine ⟨?_, ?_, ?_⟩
  · apply thickening_subset_ball_of_norm_le
    intro y hy
    obtain ⟨θ, h0, h1, rfl⟩ := mem_segment_add_iff.1 hy
    rw [leftStart_param]
    exact norm_foot_add_le hv h1δ hh2 (by linarith) (by linarith)
  · apply thickening_subset_ball_of_norm_le
    intro y hy
    obtain ⟨θ, h0, h1, rfl⟩ := mem_segment_add_iff.1 hy
    rw [rightStart_param]
    exact norm_foot_add_le hv h1δ hh2 (by linarith) (by linarith)
  · rw [← Metric.thickening_union]
    apply Metric.thickening_subset_of_subset
    intro z hz
    obtain ⟨θ, h0, h1, rfl⟩ := mem_segment_add_iff.1 hz
    rcases le_total (inner ℝ x v + θ) (1 - halfChord δ x v) with hle | hle
    · left
      refine mem_segment_add_iff.2
        ⟨inner ℝ x v + θ + halfChord δ x v, by linarith, by linarith, ?_⟩
      rw [start_param x v θ, leftStart_param]
      congr 2; ring
    · right
      refine mem_segment_add_iff.2
        ⟨inner ℝ x v + θ - halfChord δ x v + 1, by linarith, by linarith, ?_⟩
      rw [start_param x v θ, rightStart_param]
      congr 2; ring

/-- A shading of the tube keeps at least half of its measure in one canonical tube. -/
theorem canonical_split {δ : ℝ} {x v : Sp} (hδ : 0 < δ) (hv : ‖v‖ = 1)
    (hT : Metric.thickening δ (segment ℝ x (x + v)) ⊆ Metric.ball (0 : Sp) 1)
    {Y : Set Sp} (hY : Y ⊆ Metric.thickening δ (segment ℝ x (x + v))) :
    MeasureTheory.volume Y ≤
      2 * MeasureTheory.volume
        (Y ∩ Metric.thickening δ (segment ℝ (leftStart δ x v) (leftStart δ x v + v))) ∨
    MeasureTheory.volume Y ≤
      2 * MeasureTheory.volume
        (Y ∩ Metric.thickening δ (segment ℝ (rightStart δ x v) (rightStart δ x v + v))) := by
  obtain ⟨-, -, hcov⟩ := canonical_tubes hδ hv hT
  set L := Metric.thickening δ (segment ℝ (leftStart δ x v) (leftStart δ x v + v))
  set R := Metric.thickening δ (segment ℝ (rightStart δ x v) (rightStart δ x v + v))
  have hYLR : Y ⊆ (Y ∩ L) ∪ (Y ∩ R) := by
    intro y hy
    rcases hcov (hY hy) with h | h
    · exact Or.inl ⟨hy, h⟩
    · exact Or.inr ⟨hy, h⟩
  have hsum : MeasureTheory.volume Y ≤
      MeasureTheory.volume (Y ∩ L) + MeasureTheory.volume (Y ∩ R) :=
    (MeasureTheory.measure_mono hYLR).trans (MeasureTheory.measure_union_le _ _)
  rcases le_total (MeasureTheory.volume (Y ∩ R)) (MeasureTheory.volume (Y ∩ L)) with h | h
  · left
    calc MeasureTheory.volume Y ≤ MeasureTheory.volume (Y ∩ L) + MeasureTheory.volume (Y ∩ R) :=
          hsum
      _ ≤ MeasureTheory.volume (Y ∩ L) + MeasureTheory.volume (Y ∩ L) := by gcongr
      _ = 2 * MeasureTheory.volume (Y ∩ L) := by rw [two_mul]
  · right
    calc MeasureTheory.volume Y ≤ MeasureTheory.volume (Y ∩ L) + MeasureTheory.volume (Y ∩ R) :=
          hsum
      _ ≤ MeasureTheory.volume (Y ∩ R) + MeasureTheory.volume (Y ∩ R) := by gcongr
      _ = 2 * MeasureTheory.volume (Y ∩ R) := by rw [two_mul]

/-! ### Alignment: canonical starts are Lipschitz in the line -/

/-- The foot of the perpendicular of a valid tube has norm at most `1`. -/
lemma norm_foot_le_one {δ : ℝ} {x v : Sp} (hδ : 0 < δ) (hv : ‖v‖ = 1)
    (hT : Metric.thickening δ (segment ℝ x (x + v)) ⊆ Metric.ball (0 : Sp) 1) :
    ‖foot x v‖ ≤ 1 := by
  obtain ⟨-, -, hh1, h1δ, hh2⟩ := chord_bounds hδ hv hT
  have hh0 : 0 ≤ halfChord δ x v := Real.sqrt_nonneg _
  have : ‖foot x v‖ ^ 2 ≤ 1 := by nlinarith
  nlinarith [norm_nonneg (foot x v)]

/-- The half chord of a valid tube is at least `1/2`. -/
lemma half_le_halfChord {δ : ℝ} {x v : Sp} (hδ : 0 < δ) (hv : ‖v‖ = 1)
    (hT : Metric.thickening δ (segment ℝ x (x + v)) ⊆ Metric.ball (0 : Sp) 1) :
    1 / 2 ≤ halfChord δ x v := by
  obtain ⟨hs1, hs2, -, -, -⟩ := chord_bounds hδ hv hT
  linarith

/-- The half chord is `2`-Lipschitz in the foot, for valid tubes. -/
lemma abs_halfChord_sub_le {δ : ℝ} {x v x' v' : Sp} (hδ : 0 < δ) (hv : ‖v‖ = 1)
    (hv' : ‖v'‖ = 1)
    (hT : Metric.thickening δ (segment ℝ x (x + v)) ⊆ Metric.ball (0 : Sp) 1)
    (hT' : Metric.thickening δ (segment ℝ x' (x' + v')) ⊆ Metric.ball (0 : Sp) 1) :
    |halfChord δ x v - halfChord δ x' v'| ≤ 2 * ‖foot x v - foot x' v'‖ := by
  obtain ⟨-, -, -, -, hh2⟩ := chord_bounds hδ hv hT
  obtain ⟨-, -, -, -, hh2'⟩ := chord_bounds hδ hv' hT'
  have h1 := half_le_halfChord hδ hv hT
  have h1' := half_le_halfChord hδ hv' hT'
  have hp := norm_foot_le_one hδ hv hT
  have hp' := norm_foot_le_one hδ hv' hT'
  set h := halfChord δ x v
  set h' := halfChord δ x v'
  set a := ‖foot x v‖
  set b := ‖foot x' v'‖
  have hab : |a - b| ≤ ‖foot x v - foot x' v'‖ := abs_norm_sub_norm_le _ _
  -- `(h - h')(h + h') = b² - a² = (b - a)(b + a)`
  have hprod : (halfChord δ x v - halfChord δ x' v') * (halfChord δ x v + halfChord δ x' v')
      = (b - a) * (b + a) := by
    have e1 : halfChord δ x v ^ 2 - halfChord δ x' v' ^ 2 = b ^ 2 - a ^ 2 := by
      rw [hh2, hh2']; ring
    nlinarith [e1]
  have hsum : 1 ≤ halfChord δ x v + halfChord δ x' v' := by linarith
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have key : |halfChord δ x v - halfChord δ x' v'| * (halfChord δ x v + halfChord δ x' v')
      = |b - a| * (b + a) := by
    rw [← abs_of_nonneg (show 0 ≤ halfChord δ x v + halfChord δ x' v' by linarith),
      ← abs_mul, hprod, abs_mul, abs_of_nonneg (show 0 ≤ b + a by linarith)]
  have hba : |b - a| ≤ ‖foot x v - foot x' v'‖ := by rw [abs_sub_comm]; exact hab
  have hX : 0 ≤ |halfChord δ x v - halfChord δ x' v'| := abs_nonneg _
  calc |halfChord δ x v - halfChord δ x' v'|
      ≤ |halfChord δ x v - halfChord δ x' v'| * (halfChord δ x v + halfChord δ x' v') := by
        nlinarith
    _ = |b - a| * (b + a) := key
    _ ≤ ‖foot x v - foot x' v'‖ * 2 := by
        apply mul_le_mul hba (by linarith) (by linarith) (norm_nonneg _)
    _ = 2 * ‖foot x v - foot x' v'‖ := by ring

/-- The left canonical start is Lipschitz in the line (foot and direction). -/
lemma norm_leftStart_sub_le {δ : ℝ} {x v x' v' : Sp} (hδ : 0 < δ) (hv : ‖v‖ = 1)
    (hv' : ‖v'‖ = 1)
    (hT : Metric.thickening δ (segment ℝ x (x + v)) ⊆ Metric.ball (0 : Sp) 1)
    (hT' : Metric.thickening δ (segment ℝ x' (x' + v')) ⊆ Metric.ball (0 : Sp) 1) :
    ‖leftStart δ x v - leftStart δ x' v'‖ ≤ 3 * ‖foot x v - foot x' v'‖ + ‖v - v'‖ := by
  have hL := abs_halfChord_sub_le hδ hv hv' hT hT'
  obtain ⟨-, -, hh1', h1δ', -⟩ := chord_bounds hδ hv' hT'
  have hh0' : 0 ≤ halfChord δ x' v' := Real.sqrt_nonneg _
  have e : leftStart δ x v - leftStart δ x' v' = (foot x v - foot x' v')
      - ((halfChord δ x v - halfChord δ x' v') • v + halfChord δ x' v' • (v - v')) := by
    unfold leftStart; module
  rw [e]
  calc ‖(foot x v - foot x' v') - ((halfChord δ x v - halfChord δ x' v') • v
          + halfChord δ x' v' • (v - v'))‖
      ≤ ‖foot x v - foot x' v'‖ + (‖(halfChord δ x v - halfChord δ x' v') • v‖
          + ‖halfChord δ x' v' • (v - v')‖) :=
        (norm_sub_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ = ‖foot x v - foot x' v'‖ + (|halfChord δ x v - halfChord δ x' v'|
          + halfChord δ x' v' * ‖v - v'‖) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hv, mul_one,
          abs_of_nonneg hh0']
    _ ≤ ‖foot x v - foot x' v'‖ + (2 * ‖foot x v - foot x' v'‖ + 1 * ‖v - v'‖) := by
        gcongr
        linarith
    _ = 3 * ‖foot x v - foot x' v'‖ + ‖v - v'‖ := by ring

/-- The right canonical start is Lipschitz in the line (foot and direction). -/
lemma norm_rightStart_sub_le {δ : ℝ} {x v x' v' : Sp} (hδ : 0 < δ) (hv : ‖v‖ = 1)
    (hv' : ‖v'‖ = 1)
    (hT : Metric.thickening δ (segment ℝ x (x + v)) ⊆ Metric.ball (0 : Sp) 1)
    (hT' : Metric.thickening δ (segment ℝ x' (x' + v')) ⊆ Metric.ball (0 : Sp) 1) :
    ‖rightStart δ x v - rightStart δ x' v'‖ ≤ 3 * ‖foot x v - foot x' v'‖ + ‖v - v'‖ := by
  have hL := abs_halfChord_sub_le hδ hv hv' hT hT'
  obtain ⟨-, -, hh1', h1δ', -⟩ := chord_bounds hδ hv' hT'
  have hh' := half_le_halfChord hδ hv' hT'
  have habs : |halfChord δ x' v' - 1| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have e : rightStart δ x v - rightStart δ x' v' = (foot x v - foot x' v')
      + ((halfChord δ x v - halfChord δ x' v') • v + (halfChord δ x' v' - 1) • (v - v')) := by
    unfold rightStart; module
  rw [e]
  calc ‖(foot x v - foot x' v') + ((halfChord δ x v - halfChord δ x' v') • v
          + (halfChord δ x' v' - 1) • (v - v'))‖
      ≤ ‖foot x v - foot x' v'‖ + (‖(halfChord δ x v - halfChord δ x' v') • v‖
          + ‖(halfChord δ x' v' - 1) • (v - v')‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ = ‖foot x v - foot x' v'‖ + (|halfChord δ x v - halfChord δ x' v'|
          + |halfChord δ x' v' - 1| * ‖v - v'‖) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hv, mul_one]
    _ ≤ ‖foot x v - foot x' v'‖ + (2 * ‖foot x v - foot x' v'‖ + 1 * ‖v - v'‖) := by
        gcongr
    _ = 3 * ‖foot x v - foot x' v'‖ + ‖v - v'‖ := by ring

/-- Nearby unit segments have nested thickenings: if both pairs of endpoints are `r`-close,
the δ-thickening of one lies in the `(δ + r)`-thickening of the other. -/
lemma thickening_segment_subset_of_close {a b v w : Sp} {δ r : ℝ}
    (h0 : ‖a - b‖ ≤ r) (h1 : ‖(a + v) - (b + w)‖ ≤ r) :
    Metric.thickening δ (segment ℝ a (a + v)) ⊆ Metric.thickening (δ + r) (segment ℝ b (b + w)) := by
  intro z hz
  obtain ⟨y, hy, hzy⟩ := Metric.mem_thickening_iff.1 hz
  obtain ⟨θ, h0θ, h1θ, rfl⟩ := mem_segment_add_iff.1 hy
  refine Metric.mem_thickening_iff.2 ⟨b + θ • w, mem_segment_add_iff.2 ⟨θ, h0θ, h1θ, rfl⟩, ?_⟩
  have e : (a + θ • v) - (b + θ • w) = (1 - θ) • (a - b) + θ • ((a + v) - (b + w)) := by
    module
  have hclose : ‖(a + θ • v) - (b + θ • w)‖ ≤ r := by
    rw [e]
    calc ‖(1 - θ) • (a - b) + θ • ((a + v) - (b + w))‖
        ≤ ‖(1 - θ) • (a - b)‖ + ‖θ • ((a + v) - (b + w))‖ := norm_add_le _ _
      _ = (1 - θ) * ‖a - b‖ + θ * ‖(a + v) - (b + w)‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by linarith), abs_of_nonneg h0θ]
      _ ≤ (1 - θ) * r + θ * r := by gcongr
      _ = r := by ring
  calc dist z (b + θ • w) ≤ dist z (a + θ • v) + dist (a + θ • v) (b + θ • w) :=
        dist_triangle _ _ _
    _ < δ + r := by
        rw [dist_eq_norm (a + θ • v)]
        linarith

/-! ### Left-canonical tubes start on the sphere of radius `1 - δ` -/

/-- The left canonical start lies on the sphere of radius `1 - δ`. -/
lemma norm_leftStart {δ : ℝ} {x v : Sp} (hδ : 0 < δ) (hv : ‖v‖ = 1)
    (hT : Metric.thickening δ (segment ℝ x (x + v)) ⊆ Metric.ball (0 : Sp) 1) :
    ‖leftStart δ x v‖ = 1 - δ := by
  obtain ⟨-, -, -, h1δ, hh2⟩ := chord_bounds hδ hv hT
  have e : leftStart δ x v = foot x v + (-halfChord δ x v) • v := by
    unfold leftStart; module
  have hsq : ‖leftStart δ x v‖ ^ 2 = (1 - δ) ^ 2 := by
    rw [e, norm_foot_add_smul_sq hv, neg_sq, hh2]; ring
  have h0 := norm_nonneg (leftStart δ x v)
  nlinarith [sq_nonneg (‖leftStart δ x v‖ - (1 - δ)), sq_nonneg (‖leftStart δ x v‖ + (1 - δ))]

/-- A valid tube whose start lies on the sphere of radius `1 - δ` is left-canonical. -/
lemma eq_leftStart_of_norm {δ : ℝ} {x v : Sp} (hδ : 0 < δ) (hv : ‖v‖ = 1)
    (hT : Metric.thickening δ (segment ℝ x (x + v)) ⊆ Metric.ball (0 : Sp) 1)
    (hx : ‖x‖ = 1 - δ) : x = leftStart δ x v := by
  obtain ⟨hs1, hs2, -, h1δ, hh2⟩ := chord_bounds hδ hv hT
  have hh := half_le_halfChord hδ hv hT
  have ex : ‖x‖ ^ 2 = ‖foot x v‖ ^ 2 + (inner ℝ x v) ^ 2 := by
    conv_lhs => rw [← foot_add_inner x v]
    exact norm_foot_add_smul_sq hv _
  -- `⟪x, v⟫² = h²` and `⟪x, v⟫ < h`, so `⟪x, v⟫ = -h`
  have hsq : (inner ℝ x v) ^ 2 = halfChord δ x v ^ 2 := by
    rw [hh2, ← hx, ex]; ring
  have hneg : inner ℝ x v = -halfChord δ x v := by
    have hlt : inner ℝ x v < halfChord δ x v := by linarith
    have : (inner ℝ x v - halfChord δ x v) * (inner ℝ x v + halfChord δ x v) = 0 := by
      ring_nf; linarith [hsq]
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) (ne_of_lt hlt)
    · linarith
  conv_lhs => rw [← foot_add_inner x v]
  rw [hneg]; unfold leftStart; module

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy
