-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.NormConflict.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormContain
import Submission.WZ.Obl.wz_convex_container_tube_packing

/-!
# Conflicts between zoomed pieces

Two zoomed unit pieces *nearly coincide* (`TwoNear`) when both endpoints of the second lie
close to the axis line of the first. This happens when they overlap by more than half, or when
they contain a common unit tube. Nearly coincident pieces come from original unit tubes lying in
a common line container `LC` of radius `O(lam ρ)`, so a family of half-distinct original tubes
has at most `10 ^ 50 lam ^ 4` members conflicting with a given one (tube packing, o032).
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory
open scoped ENNReal

/-- Line container: points within `r` of the segment `a + [-M, M] u`. -/
def LC (a u : Space) (M r : ℝ) : Set Space := {p | ∃ σ ∈ Icc (-M) M, ‖p - (a + σ • u)‖ < r}

theorem LC_mono {a u : Space} {M M' r r' : ℝ} (hM : M ≤ M') (hr : r ≤ r') :
    LC a u M r ⊆ LC a u M' r' := by
  rintro p ⟨σ, hσ, hp⟩
  exact ⟨σ, ⟨by linarith [hσ.1], by linarith [hσ.2]⟩, hp.trans_le hr⟩

theorem volume_LC_le {a u : Space} (hu : ‖u‖ = 1) {M r : ℝ} (hM : 1 ≤ M) (hr : 0 < r) :
    volume (LC a u M r) ≤ ENNReal.ofReal (256 * M * (2 + r) * r ^ 2) := by
  set b := a - M • u
  have hsub : LC a u M r ⊆ AffineMap.homothety b (2 * M) '' tube (r / (2 * M)) b u := by
    rintro p ⟨σ, hσ, hp⟩
    refine ⟨b + (1 / (2 * M)) • (p - b), ?_, ?_⟩
    · refine mem_tube_iff.mpr ⟨(σ + M) / (2 * M), ⟨?_, ?_⟩, ?_⟩
      · apply div_nonneg (by linarith [hσ.1]) (by linarith)
      · rw [div_le_one (by linarith)]; linarith [hσ.2]
      · have he : b + (1 / (2 * M)) • (p - b) - (b + ((σ + M) / (2 * M)) • u) =
            (1 / (2 * M)) • (p - (a + σ • u)) := by
          simp only [b]
          rw [show (σ + M) / (2 * M) = (1 / (2 * M)) * (σ + M) by ring, ← smul_smul]
          module
        rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
        calc 1 / (2 * M) * ‖p - (a + σ • u)‖ < 1 / (2 * M) * r :=
              mul_lt_mul_of_pos_left hp (by positivity)
          _ = r / (2 * M) := by ring
    · rw [AffineMap.homothety_apply]
      simp only [vsub_eq_sub, vadd_eq_add, add_sub_cancel_left, smul_smul]
      rw [show 2 * M * (1 / (2 * M)) = 1 by field_simp, one_smul]
      abel
  have hseg : (fun t : ℝ => b + t • u) '' Icc 0 1 = segment ℝ b (b + u) := by
    rw [segment_eq_image']; simp
  have hvol : volume (tube (r / (2 * M)) b u) ≤
      ENNReal.ofReal (128 * (2 * 1 + r / (2 * M)) * (r / (2 * M)) ^ 2) := by
    have h := WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper b u hu
      (T := Icc 0 1) subset_rfl (r := r / (2 * M)) (A := 1) (by positivity) zero_le_one (by
        intro s hs t ht
        rw [Real.dist_eq, abs_le]
        constructor <;> linarith [hs.1, hs.2, ht.1, ht.2])
    rwa [hseg] at h
  calc volume (LC a u M r) ≤ volume (AffineMap.homothety b (2 * M) '' tube (r / (2 * M)) b u) :=
        measure_mono hsub
    _ = ENNReal.ofReal |(2 * M) ^ 3| * volume (tube (r / (2 * M)) b u) := by
        rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin]
    _ ≤ ENNReal.ofReal |(2 * M) ^ 3| *
          ENNReal.ofReal (128 * (2 * 1 + r / (2 * M)) * (r / (2 * M)) ^ 2) := by gcongr
    _ = ENNReal.ofReal ((2 * M) ^ 3 * (128 * (2 * 1 + r / (2 * M)) * (r / (2 * M)) ^ 2)) := by
        rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (by positivity)]
    _ ≤ ENNReal.ofReal (256 * M * (2 + r) * r ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        have hM0 : 0 < M := by linarith
        have h1 : (2 * M) ^ 3 * (128 * (2 * 1 + r / (2 * M)) * (r / (2 * M)) ^ 2) =
            256 * M * (2 + r / (2 * M)) * r ^ 2 := by
          field_simp
          ring
        rw [h1]
        have h2 : r / (2 * M) ≤ r := by
          rw [div_le_iff₀ (by positivity)]; nlinarith
        gcongr

/-- Linear extrapolation between two pairs of close points on two lines. -/
theorem extrap {a' u' a u : Space} {t₀ t₁ s₀ s₁ d : ℝ} (ht : t₀ ≠ t₁)
    (h₀ : ‖(a' + t₀ • u') - (a + s₀ • u)‖ ≤ d) (h₁ : ‖(a' + t₁ • u') - (a + s₁ • u)‖ ≤ d)
    (t : ℝ) :
    ‖(a' + t • u') - (a + (s₀ + (t - t₀) / (t₁ - t₀) * (s₁ - s₀)) • u)‖ ≤
      (1 + 2 * |(t - t₀) / (t₁ - t₀)|) * d := by
  set μ := (t - t₀) / (t₁ - t₀) with hμ
  have hne : t₁ - t₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have he : (a' + t • u') - (a + (s₀ + μ * (s₁ - s₀)) • u) =
      (1 - μ) • ((a' + t₀ • u') - (a + s₀ • u)) + μ • ((a' + t₁ • u') - (a + s₁ • u)) := by
    have ht' : t = t₀ + μ * (t₁ - t₀) := by rw [hμ]; field_simp; ring
    rw [ht']
    module
  rw [he]
  have hd : 0 ≤ d := (norm_nonneg _).trans h₀
  calc ‖(1 - μ) • ((a' + t₀ • u') - (a + s₀ • u)) + μ • ((a' + t₁ • u') - (a + s₁ • u))‖ ≤
        |1 - μ| * d + |μ| * d := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Real.norm_eq_abs]; gcongr
        · rw [norm_smul, Real.norm_eq_abs]; gcongr
    _ ≤ (1 + 2 * |μ|) * d := by
        have : |1 - μ| ≤ 1 + |μ| := by
          calc |1 - μ| ≤ |1| + |μ| := abs_sub _ _
            _ = 1 + |μ| := by rw [abs_one]
        nlinarith

/-- Both endpoints of the second segment are close to the line of the first. -/
def TwoNear (D : ℝ) (s u s' u' : Space) : Prop :=
  ∃ σ₀ ∈ Icc (-2 : ℝ) 3, ∃ σ₁ ∈ Icc (-2 : ℝ) 3,
    ‖s' - (s + σ₀ • u)‖ < D ∧ ‖(s' + u') - (s + σ₁ • u)‖ < D

/-- Overlapping unit pieces nearly coincide. -/
theorem twoNear_of_overlap {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1 / 10000) {s u s' u' : Space}
    (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1)
    (hov : (1 / 2 : ℝ≥0∞) * volume (tube R s u) < volume (tube R s u ∩ tube R s' u')) :
    TwoNear (10000 * R) s u s' u' := by
  have h := overlap_axis_close hR hR1 hu hu' hov
  obtain ⟨σ₀, hσ₀, h₀⟩ := h 0 ⟨le_rfl, zero_le_one⟩
  obtain ⟨σ₁, hσ₁, h₁⟩ := h 1 ⟨zero_le_one, le_rfl⟩
  exact ⟨σ₀, hσ₀, σ₁, hσ₁, by simpa using h₀, by simpa using h₁⟩

/-- Unit pieces containing a common unit tube nearly coincide. -/
theorem twoNear_of_common {r R : ℝ} (hr : 0 < r) {q u₀ s u s' u' : Space} (hu₀ : ‖u₀‖ = 1)
    (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1)
    (h₁ : tube r q u₀ ⊆ tube R s u) (h₂ : tube r q u₀ ⊆ tube R s' u') :
    TwoNear (10000 * R) s u s' u' := by
  have hR : 0 < R := by
    obtain ⟨t, -, ht⟩ := mem_tube_iff.mp (h₁ (axis_mem_tube hr q u₀ ⟨le_rfl, zero_le_one⟩))
    exact lt_of_le_of_lt (norm_nonneg _) ht
  have hsmall : 6 * R < 10000 * R := by linarith
  rcases endpoints_close hr hu₀ hu h₁ with ⟨a0, a1⟩ | ⟨a0, a1⟩ <;>
    rcases endpoints_close hr hu₀ hu' h₂ with ⟨b0, b1⟩ | ⟨b0, b1⟩
  · refine ⟨0, ⟨by norm_num, by norm_num⟩, 1, ⟨by norm_num, by norm_num⟩, ?_, ?_⟩
    · calc ‖s' - (s + (0 : ℝ) • u)‖ = ‖(q - s) - (q - s')‖ := by congr 1; simp
        _ ≤ ‖q - s‖ + ‖q - s'‖ := norm_sub_le _ _
        _ < 10000 * R := by linarith
    · calc ‖(s' + u') - (s + (1 : ℝ) • u)‖ = ‖(q + u₀ - (s + u)) - (q + u₀ - (s' + u'))‖ := by
            congr 1; simp only [one_smul]; abel
        _ ≤ ‖q + u₀ - (s + u)‖ + ‖q + u₀ - (s' + u')‖ := norm_sub_le _ _
        _ < 10000 * R := by linarith
  · refine ⟨1, ⟨by norm_num, by norm_num⟩, 0, ⟨by norm_num, by norm_num⟩, ?_, ?_⟩
    · calc ‖s' - (s + (1 : ℝ) • u)‖ = ‖(q + u₀ - (s + u)) - (q + u₀ - s')‖ := by
            congr 1; simp only [one_smul]; abel
        _ ≤ ‖q + u₀ - (s + u)‖ + ‖q + u₀ - s'‖ := norm_sub_le _ _
        _ < 10000 * R := by linarith
    · calc ‖(s' + u') - (s + (0 : ℝ) • u)‖ = ‖(q - s) - (q - (s' + u'))‖ := by
            congr 1; simp
        _ ≤ ‖q - s‖ + ‖q - (s' + u')‖ := norm_sub_le _ _
        _ < 10000 * R := by linarith
  · refine ⟨1, ⟨by norm_num, by norm_num⟩, 0, ⟨by norm_num, by norm_num⟩, ?_, ?_⟩
    · calc ‖s' - (s + (1 : ℝ) • u)‖ = ‖(q - (s + u)) - (q - s')‖ := by
            congr 1; simp only [one_smul]; abel
        _ ≤ ‖q - (s + u)‖ + ‖q - s'‖ := norm_sub_le _ _
        _ < 10000 * R := by linarith
    · calc ‖(s' + u') - (s + (0 : ℝ) • u)‖ = ‖(q + u₀ - s) - (q + u₀ - (s' + u'))‖ := by
            congr 1; simp
        _ ≤ ‖q + u₀ - s‖ + ‖q + u₀ - (s' + u')‖ := norm_sub_le _ _
        _ < 10000 * R := by linarith
  · refine ⟨0, ⟨by norm_num, by norm_num⟩, 1, ⟨by norm_num, by norm_num⟩, ?_, ?_⟩
    · calc ‖s' - (s + (0 : ℝ) • u)‖ = ‖(q + u₀ - s) - (q + u₀ - s')‖ := by congr 1; simp
        _ ≤ ‖q + u₀ - s‖ + ‖q + u₀ - s'‖ := norm_sub_le _ _
        _ < 10000 * R := by linarith
    · calc ‖(s' + u') - (s + (1 : ℝ) • u)‖ = ‖(q - (s + u)) - (q - (s' + u'))‖ := by
            congr 1; simp only [one_smul]; abel
        _ ≤ ‖q - (s + u)‖ + ‖q - (s' + u')‖ := norm_sub_le _ _
        _ < 10000 * R := by linarith

theorem pieceStart_add_smul (c : Space) {lam : ℝ} (hlam : 0 < lam) (z w : Space) (τ : ℝ) :
    pieceStart c lam z w + τ • w = lam • (foot c z w + ((τ - 1 / 2) / lam) • w - c) := by
  simp only [pieceStart, smul_add, smul_sub, smul_smul]
  rw [show lam * ((τ - 1 / 2) / lam) = τ - 1 / 2 by field_simp]
  module

/-- Nearly coincident zoomed pieces: the second original unit tube lies in a line container
around the first original line. -/
theorem tube_subset_LC_of_twoNear {c : Space} {lam ρ D : ℝ} (hlam : 1 ≤ lam) (hρ : 0 < ρ)
    {z w z' w' : Space} (hw' : ‖w'‖ = 1) (hcz' : ‖c - z'‖ ≤ 3)
    (h : TwoNear D (pieceStart c lam z w) w (pieceStart c lam z' w') w') :
    tube ρ z' w' ⊆ LC (foot c z w) w 25 ((2 + 8 * lam) * (D / lam) + ρ) := by
  have hlam0 : 0 < lam := by linarith
  obtain ⟨σ₀, hσ₀, σ₁, hσ₁, h₀, h₁⟩ := h
  -- unzoom the two estimates
  have hun : ∀ (τ σ : ℝ), ‖(pieceStart c lam z' w' + τ • w') - (pieceStart c lam z w + σ • w)‖ =
      lam * ‖(foot c z' w' + ((τ - 1 / 2) / lam) • w') -
        (foot c z w + ((σ - 1 / 2) / lam) • w)‖ := by
    intro τ σ
    rw [pieceStart_add_smul c hlam0, pieceStart_add_smul c hlam0, ← smul_sub,
      show foot c z' w' + ((τ - 1 / 2) / lam) • w' - c -
        (foot c z w + ((σ - 1 / 2) / lam) • w - c) =
        (foot c z' w' + ((τ - 1 / 2) / lam) • w') - (foot c z w + ((σ - 1 / 2) / lam) • w) by
        abel, norm_smul, Real.norm_eq_abs, abs_of_pos hlam0]
  have e₀ : ‖(foot c z' w' + ((0 - 1 / 2) / lam) • w') - (foot c z w + ((σ₀ - 1 / 2) / lam) • w)‖
      ≤ D / lam := by
    rw [le_div_iff₀ hlam0, mul_comm, ← hun]
    simpa using h₀.le
  have e₁ : ‖(foot c z' w' + ((1 - 1 / 2) / lam) • w') - (foot c z w + ((σ₁ - 1 / 2) / lam) • w)‖
      ≤ D / lam := by
    rw [le_div_iff₀ hlam0, mul_comm, ← hun]
    simpa using h₁.le
  have hne : (0 - 1 / 2) / lam ≠ (1 - 1 / 2) / lam := by
    intro h; field_simp at h; linarith
  intro p hp
  obtain ⟨t'', ht'', hpt⟩ := mem_tube_iff.mp hp
  set τ' := inner ℝ (c - z') w' with hτ'
  have hτ'b : |τ'| ≤ 3 := by
    calc |τ'| ≤ ‖c - z'‖ * ‖w'‖ := abs_real_inner_le_norm _ _
      _ ≤ 3 * 1 := by rw [hw']; gcongr
      _ = 3 := by ring
  set t := t'' - τ' with ht
  have hz' : z' + t'' • w' = foot c z' w' + t • w' := by
    simp only [foot, ht, ← hτ']; module
  have hext := extrap hne e₀ e₁ t
  set μ := (t - (0 - 1 / 2) / lam) / ((1 - 1 / 2) / lam - (0 - 1 / 2) / lam) with hμ
  have hμe : μ = lam * t + 1 / 2 := by
    rw [hμ]; field_simp; ring
  have htb : |t| ≤ 4 := by
    rw [ht, abs_le]; constructor <;> linarith [ht''.1, ht''.2, (abs_le.mp hτ'b).1, (abs_le.mp hτ'b).2]
  have hμb : |μ| ≤ 4 * lam + 1 / 2 := by
    rw [hμe]
    calc |lam * t + 1 / 2| ≤ |lam * t| + |1 / 2| := abs_add_le _ _
      _ = lam * |t| + 1 / 2 := by
          rw [abs_mul, abs_of_pos hlam0, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
      _ ≤ lam * 4 + 1 / 2 := by gcongr
      _ = 4 * lam + 1 / 2 := by ring
  refine ⟨(σ₀ - 1 / 2) / lam + μ * ((σ₁ - 1 / 2) / lam - (σ₀ - 1 / 2) / lam), ⟨?_, ?_⟩, ?_⟩
  · have hσd : |(σ₁ - 1 / 2) / lam - (σ₀ - 1 / 2) / lam| ≤ 5 / lam := by
      rw [show (σ₁ - 1 / 2) / lam - (σ₀ - 1 / 2) / lam = (σ₁ - σ₀) / lam by ring, abs_div,
        abs_of_pos hlam0]
      apply div_le_div_of_nonneg_right _ hlam0.le
      rw [abs_le]; constructor <;> linarith [hσ₀.1, hσ₀.2, hσ₁.1, hσ₁.2]
    have hσ0 : |(σ₀ - 1 / 2) / lam| ≤ 5 / 2 / lam := by
      rw [abs_div, abs_of_pos hlam0]
      apply div_le_div_of_nonneg_right _ hlam0.le
      rw [abs_le]; constructor <;> linarith [hσ₀.1, hσ₀.2]
    have hprod : |μ * ((σ₁ - 1 / 2) / lam - (σ₀ - 1 / 2) / lam)| ≤ (4 * lam + 1 / 2) * (5 / lam) := by
      rw [abs_mul]; exact mul_le_mul hμb hσd (abs_nonneg _) (by positivity)
    have hval : (4 * lam + 1 / 2) * (5 / lam) + 5 / 2 / lam ≤ 25 := by
      rw [show (4 * lam + 1 / 2) * (5 / lam) + 5 / 2 / lam = 20 + 5 / lam by field_simp; ring]
      have : 5 / lam ≤ 5 := by rw [div_le_iff₀ hlam0]; linarith
      linarith
    have := abs_add_le ((σ₀ - 1 / 2) / lam) (μ * ((σ₁ - 1 / 2) / lam - (σ₀ - 1 / 2) / lam))
    have := (abs_le.mp (show |(σ₀ - 1 / 2) / lam + μ * ((σ₁ - 1 / 2) / lam - (σ₀ - 1 / 2) / lam)|
      ≤ 25 by linarith)).1
    linarith
  · have hσd : |(σ₁ - 1 / 2) / lam - (σ₀ - 1 / 2) / lam| ≤ 5 / lam := by
      rw [show (σ₁ - 1 / 2) / lam - (σ₀ - 1 / 2) / lam = (σ₁ - σ₀) / lam by ring, abs_div,
        abs_of_pos hlam0]
      apply div_le_div_of_nonneg_right _ hlam0.le
      rw [abs_le]; constructor <;> linarith [hσ₀.1, hσ₀.2, hσ₁.1, hσ₁.2]
    have hσ0 : |(σ₀ - 1 / 2) / lam| ≤ 5 / 2 / lam := by
      rw [abs_div, abs_of_pos hlam0]
      apply div_le_div_of_nonneg_right _ hlam0.le
      rw [abs_le]; constructor <;> linarith [hσ₀.1, hσ₀.2]
    have hprod : |μ * ((σ₁ - 1 / 2) / lam - (σ₀ - 1 / 2) / lam)| ≤ (4 * lam + 1 / 2) * (5 / lam) := by
      rw [abs_mul]; exact mul_le_mul hμb hσd (abs_nonneg _) (by positivity)
    have hval : (4 * lam + 1 / 2) * (5 / lam) + 5 / 2 / lam ≤ 25 := by
      rw [show (4 * lam + 1 / 2) * (5 / lam) + 5 / 2 / lam = 20 + 5 / lam by field_simp; ring]
      have : 5 / lam ≤ 5 := by rw [div_le_iff₀ hlam0]; linarith
      linarith
    have := abs_add_le ((σ₀ - 1 / 2) / lam) (μ * ((σ₁ - 1 / 2) / lam - (σ₀ - 1 / 2) / lam))
    have := (abs_le.mp (show |(σ₀ - 1 / 2) / lam + μ * ((σ₁ - 1 / 2) / lam - (σ₀ - 1 / 2) / lam)|
      ≤ 25 by linarith)).2
    linarith
  · have hsplit : p - (foot c z w + ((σ₀ - 1 / 2) / lam + μ * ((σ₁ - 1 / 2) / lam -
        (σ₀ - 1 / 2) / lam)) • w) = (p - (z' + t'' • w')) +
        ((foot c z' w' + t • w') - (foot c z w + ((σ₀ - 1 / 2) / lam + μ * ((σ₁ - 1 / 2) / lam -
          (σ₀ - 1 / 2) / lam)) • w)) := by
      rw [hz']; abel
    rw [hsplit]
    have hD : 0 ≤ D / lam := (norm_nonneg _).trans e₀
    calc _ ≤ ‖p - (z' + t'' • w')‖ + ‖(foot c z' w' + t • w') - (foot c z w +
          ((σ₀ - 1 / 2) / lam + μ * ((σ₁ - 1 / 2) / lam - (σ₀ - 1 / 2) / lam)) • w)‖ :=
          norm_add_le _ _
      _ < ρ + (1 + 2 * |μ|) * (D / lam) := add_lt_add_of_lt_of_le hpt hext
      _ ≤ ρ + (2 + 8 * lam) * (D / lam) := by
          have : (1 + 2 * |μ|) * (D / lam) ≤ (2 + 8 * lam) * (D / lam) :=
            mul_le_mul_of_nonneg_right (by linarith) hD
          linarith
      _ = (2 + 8 * lam) * (D / lam) + ρ := by ring

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
