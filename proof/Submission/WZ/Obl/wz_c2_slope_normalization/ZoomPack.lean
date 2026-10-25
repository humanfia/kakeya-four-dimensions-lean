-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_c2_slope_normalization.ZoomPack.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_c2_slope_normalization.ZoomConflict
import Submission.WZ.Obl.wz_c2_slope_normalization.ZoomGrains

/-!
# Conflicts between zoomed pieces and their number

Two unit pieces of zoomed tubes that are close along a stretch of length comparable to one
come from old unit tubes whose axes are close along their whole length.  Hence all old tubes
whose pieces conflict with a fixed one lie in a cylinder of radius `394 r ρ`, and the packing
bound for essentially distinct tubes limits their number by a constant times `r ^ 4`.
-/

namespace WangZahlLot.Obl.wz_c2_slope_normalization

open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

abbrev Container := WangZahlLot.Obl.wz_separated_cover_refinement.Container

/-- A unit tube whose axis is close to a line at two separated points lies in a container. -/
theorem tube_subset_container {ρ ε l Λ s₀ : ℝ} {z w z' w' : Space} (hw : ‖w‖ = 1)
    (hw' : ‖w'‖ = 1) {s₁ s₂ t₁ t₂ : ℝ} (hl : 0 < l) (hεl : 8 * ε ≤ l) (hsep : l ≤ |s₂ - s₁|)
    (h₁ : ‖(z + s₁ • w) - (z' + t₁ • w')‖ ≤ 2 * ε)
    (h₂ : ‖(z + s₂ • w) - (z' + t₂ • w')‖ ≤ 2 * ε)
    (ht₁ : |t₁| ≤ 2) (hs₁ : |s₁ - s₀| ≤ 2)
    (hΛ : ρ + 2 * ε + 3 * (16 * ε / l) < 1000 * Λ) :
    Tube ρ z' w' ⊆ Container Λ (z + s₀ • w) w := by
  obtain ⟨σ, hσ, hclose⟩ := line_close_of_two_points hw hw' hl hεl hsep h₁ h₂
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hε : 0 ≤ ε := by have := norm_nonneg ((z + s₁ • w) - (z' + t₁ • w')); linarith
  intro p hp
  obtain ⟨t, ht, hpt⟩ := exists_param_of_mem_tube' hp
  have htt : |t - t₁| ≤ 3 := by
    rw [abs_le] at ht₁ ⊢; constructor <;> linarith [ht.1, ht.2]
  apply WangZahlLot.Obl.wz_separated_cover_refinement.mem_container
    (t := s₁ - s₀ + σ * (t - t₁))
  · calc |s₁ - s₀ + σ * (t - t₁)| ≤ |s₁ - s₀| + |σ * (t - t₁)| := abs_add_le _ _
      _ ≤ 2 + 3 := by rw [abs_mul, hσabs, one_mul]; linarith
      _ ≤ 50 := by norm_num
  · have he : p - (z + s₀ • w + (s₁ - s₀ + σ * (t - t₁)) • w) =
        (p - (z' + t • w')) + ((z' + t • w') - (z + (s₁ + σ * (t - t₁)) • w)) := by module
    rw [he]
    refine (norm_add_le _ _).trans_lt ?_
    have h2 := hclose t
    have h3 : |t - t₁| * (16 * ε / l) ≤ 3 * (16 * ε / l) :=
      mul_le_mul_of_nonneg_right htt (by positivity)
    linarith

/-- Few essentially distinct unit tubes fit in a container. -/
theorem card_le_of_container {k : ℕ} {ρ Λ : ℝ} (hρ : 0 < ρ) (hΛ : 0 < Λ) (hΛ1 : Λ ≤ 1)
    (z w : Fin k → Space) (hw : ∀ j, ‖w j‖ = 1)
    (hsep : ∀ j j', j ≠ j' → volume (Tube ρ (z j) (w j) ∩ Tube ρ (z j') (w j')) ≤
      (1 / 2 : ℝ≥0∞) * volume (Tube ρ (z j) (w j)))
    (c₀ w₀ : Space) (hw₀ : ‖w₀‖ = 1) (S : Finset (Fin k))
    (hsub : ∀ j ∈ S, Tube ρ (z j) (w j) ⊆ Container Λ c₀ w₀) :
    (S.card : ℝ) * ρ ^ 4 ≤ 1000000 * (200000000000 * Λ ^ 2) ^ 2 := by
  classical
  let e : Fin S.card → Fin k := fun a => (S.equivFin.symm a).val
  have he : Function.Injective e := Subtype.val_injective.comp S.equivFin.symm.injective
  have hvol := WangZahlLot.Obl.wz_separated_cover_refinement.container_volume hΛ hΛ1 c₀ w₀ hw₀
  have hpack := WangZahlLot.Obl.wz_convex_container_tube_packing.packing hρ
    (fun a => z (e a)) (fun a => w (e a))
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvol) (fun a => hw (e a))
    (fun a => hsub _ (S.equivFin.symm a).property)
    (fun a b hab => hsep (e a) (e b) (he.ne hab))
  have h2 : ENNReal.ofReal ((S.card : ℝ) * ρ ^ 4) ≤
      ENNReal.ofReal (1000000 * (200000000000 * Λ ^ 2) ^ 2) := by
    calc _ ≤ ENNReal.ofReal 1000000 * (volume (Container Λ c₀ w₀)) ^ 2 := hpack
      _ ≤ ENNReal.ofReal 1000000 * (ENNReal.ofReal (200000000000 * Λ ^ 2)) ^ 2 := by
        gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2

/-- A new point close to a point of a zoomed line gives an old point close to the old line. -/
theorem old_of_new {r A μ : ℝ} (hr : 0 < r) {c p z w : Space}
    (h : ‖zoom r c p - (pieceBase r c z w + μ • w)‖ < A) :
    ‖p - (z + (cpar c z w + (μ - 1 / 2) / r) • w)‖ < A / r := by
  have hμ : μ = r * ((μ - 1 / 2) / r) + 1 / 2 := by field_simp; ring
  have he : zoom r c p - (pieceBase r c z w + μ • w) =
      r • (p - (z + (cpar c z w + (μ - 1 / 2) / r) • w)) := by
    set s := (μ - 1 / 2) / r
    rw [hμ]
    simp only [zoom, pieceBase, cpt]
    module
  rw [he, norm_smul, Real.norm_of_nonneg hr.le] at h
  rwa [lt_div_iff₀ hr, mul_comm]

theorem unzoom_spec {r : ℝ} (hr : 0 < r) (c q : Space) : zoom r c (unzoom r c q) = q :=
  zoom_unzoom hr.ne' c q

/-- Conflict through overlapping pieces: the old tube lies in a container around the other. -/
theorem overlap_container {r a ρ₀ ρt Λ : ℝ} (hr : 1 ≤ r) (ha : a = r * ρ₀) (hρ₀ : 0 < ρ₀)
    (ha1 : a ≤ 1 / 1024) (hρ₀r : ρ₀ ≤ 1 / (8192 * r))
    (hΛ : ρt + 2 * ρ₀ + 3 * (16 * ρ₀ / (1 / (1024 * r))) < 1000 * Λ)
    {c z w z' w' : Space} (hw : ‖w‖ = 1) (hw' : ‖w'‖ = 1)
    (hnear' : cpar c z' w' ∈ Icc (-(1 / 4) : ℝ) (5 / 4))
    (hover : (1 / 2 : ℝ≥0∞) * volume (Tube a (pieceBase r c z w) w) <
      volume (Tube a (pieceBase r c z w) w ∩ Tube a (pieceBase r c z' w') w')) :
    Tube ρt z' w' ⊆ Container Λ (cpt c z w) w := by
  have hr0 : 0 < r := by linarith
  have ha0 : 0 < a := by rw [ha]; positivity
  obtain ⟨θ₁, hθ₁, θ₂, hθ₂, hθsep, ⟨q₁, hq₁, hq₁Z⟩, ⟨q₂, hq₂, hq₂Z⟩⟩ :=
    overlap_far_points ha0 ha1 hw hover
  obtain ⟨θ₁', hθ₁', hq₁Z'⟩ := exists_param_of_mem_tube' hq₁
  obtain ⟨θ₂', hθ₂', hq₂Z'⟩ := exists_param_of_mem_tube' hq₂
  have hq : ∀ q : Space, zoom r c (unzoom r c q) = q := unzoom_spec hr0 c
  have o₁ := old_of_new hr0 (p := unzoom r c q₁) (by rw [hq]; exact hq₁Z)
  have o₂ := old_of_new hr0 (p := unzoom r c q₂) (by rw [hq]; exact hq₂Z)
  have o₁' := old_of_new hr0 (p := unzoom r c q₁) (by rw [hq]; exact hq₁Z')
  have o₂' := old_of_new hr0 (p := unzoom r c q₂) (by rw [hq]; exact hq₂Z')
  have haρ : a / r = ρ₀ := by rw [ha]; field_simp
  rw [haρ] at o₁ o₂ o₁' o₂'
  have hhalf : ∀ θ ∈ Icc (0 : ℝ) 1, |(θ - 1 / 2) / r| ≤ 1 / 2 := by
    intro θ hθ
    rw [abs_div, abs_of_pos hr0, div_le_iff₀ hr0]
    have : |θ - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2]
    nlinarith
  show Tube ρt z' w' ⊆ Container Λ (z + cpar c z w • w) w
  apply tube_subset_container hw hw' (ε := ρ₀) (l := 1 / (1024 * r))
    (s₁ := cpar c z w + (θ₁ - 1 / 2) / r) (s₂ := cpar c z w + (θ₂ - 1 / 2) / r)
    (t₁ := cpar c z' w' + (θ₁' - 1 / 2) / r) (t₂ := cpar c z' w' + (θ₂' - 1 / 2) / r)
    (by positivity)
  · rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hρ₀r (show (0 : ℝ) ≤ 8 * (1024 * r) by positivity)
    rw [show 8 * (1024 * r) * (1 / (8192 * r)) = 1 by field_simp; ring] at this
    linarith
  · rw [show cpar c z w + (θ₂ - 1 / 2) / r - (cpar c z w + (θ₁ - 1 / 2) / r) =
      (θ₂ - θ₁) / r by ring, abs_div, abs_of_pos hr0]
    rw [div_le_div_iff₀ (by positivity) hr0]
    nlinarith
  · have he : (z + (cpar c z w + (θ₁ - 1 / 2) / r) • w) -
        (z' + (cpar c z' w' + (θ₁' - 1 / 2) / r) • w') =
        -(unzoom r c q₁ - (z + (cpar c z w + (θ₁ - 1 / 2) / r) • w)) +
          (unzoom r c q₁ - (z' + (cpar c z' w' + (θ₁' - 1 / 2) / r) • w')) := by abel
    rw [he]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]; linarith
  · have he : (z + (cpar c z w + (θ₂ - 1 / 2) / r) • w) -
        (z' + (cpar c z' w' + (θ₂' - 1 / 2) / r) • w') =
        -(unzoom r c q₂ - (z + (cpar c z w + (θ₂ - 1 / 2) / r) • w)) +
          (unzoom r c q₂ - (z' + (cpar c z' w' + (θ₂' - 1 / 2) / r) • w')) := by abel
    rw [he]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]; linarith
  · have h1 := hhalf θ₁' hθ₁'
    have h2 : |cpar c z' w'| ≤ 5 / 4 := abs_le.mpr ⟨by linarith [hnear'.1], hnear'.2⟩
    calc |cpar c z' w' + (θ₁' - 1 / 2) / r| ≤ |cpar c z' w'| + |(θ₁' - 1 / 2) / r| :=
          abs_add_le _ _
      _ ≤ 2 := by linarith
  · rw [show cpar c z w + (θ₁ - 1 / 2) / r - cpar c z w = (θ₁ - 1 / 2) / r by ring]
    linarith [hhalf θ₁ hθ₁]
  · exact hΛ

/-- Conflict through a common fine piece in two tenfold dilates. -/
theorem dilate_container {r δ ρ : ℝ} (hr : 16 ≤ r) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hρr : ρ ≤ 1 / (1280 * r))
    {c x v z w z' w' : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hw' : ‖w'‖ = 1)
    (hnear' : cpar c z' w' ∈ Icc (-(1 / 4) : ℝ) (5 / 4))
    (hA : Tube (r * δ) (pieceBase r c x v) v ⊆ Dilate (8 * r * ρ) (pieceBase r c z w) w)
    (hA' : Tube (r * δ) (pieceBase r c x v) v ⊆ Dilate (8 * r * ρ) (pieceBase r c z' w') w') :
    Tube ρ z' w' ⊆ Container (394 * r * ρ) (cpt c z w) w := by
  have hr0 : 0 < r := by linarith
  have hrδ : 0 < r * δ := mul_pos hr0 hδ
  set X := pieceBase r c x v
  have hX : X ∈ Tube (r * δ) X v := self_subset_thickening hrδ _ (left_mem_segment ℝ X (X + v))
  have hXv : X + v ∈ Tube (r * δ) X v :=
    self_subset_thickening hrδ _ (right_mem_segment ℝ X (X + v))
  obtain ⟨μ₀, hμ₀, h₀⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.dilate_param (hA hX)
  obtain ⟨μ₁, hμ₁, h₁⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.dilate_param (hA hXv)
  obtain ⟨μ₀', hμ₀', h₀'⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.dilate_param (hA' hX)
  obtain ⟨μ₁', hμ₁', h₁'⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.dilate_param (hA' hXv)
  have hq : ∀ q : Space, zoom r c (unzoom r c q) = q := unzoom_spec hr0 c
  have e80 : 10 * (8 * r * ρ) / r = 80 * ρ := by field_simp; ring
  have o₀ := old_of_new hr0 (p := unzoom r c X) (by rw [hq]; exact h₀)
  have o₁ := old_of_new hr0 (p := unzoom r c (X + v)) (by rw [hq]; exact h₁)
  have o₀' := old_of_new hr0 (p := unzoom r c X) (by rw [hq]; exact h₀')
  have o₁' := old_of_new hr0 (p := unzoom r c (X + v)) (by rw [hq]; exact h₁')
  rw [e80] at o₀ o₁ o₀' o₁'
  set s₀ := cpar c z w + (μ₀ - 1 / 2) / r
  set s₁ := cpar c z w + (μ₁ - 1 / 2) / r
  set t₀ := cpar c z' w' + (μ₀' - 1 / 2) / r
  set t₁ := cpar c z' w' + (μ₁' - 1 / 2) / r
  have hpp : ‖unzoom r c (X + v) - unzoom r c X‖ = 1 / r := by
    simp only [unzoom, add_sub_add_left_eq_sub, ← smul_sub, add_sub_cancel_left, norm_smul,
      hv, Real.norm_of_nonneg (inv_nonneg.mpr hr0.le), mul_one, one_div]
  have hsmall : |μ₀ - 1 / 2| / r ≤ 1 / 2 := by
    rw [div_le_iff₀ hr0]
    have : |μ₀ - 1 / 2| ≤ 13 / 2 := by
      rw [abs_le] at hμ₀ ⊢; constructor <;> linarith [hμ₀.1, hμ₀.2]
    linarith
  have hsmall' : |μ₀' - 1 / 2| / r ≤ 1 / 2 := by
    rw [div_le_iff₀ hr0]
    have : |μ₀' - 1 / 2| ≤ 13 / 2 := by
      rw [abs_le] at hμ₀' ⊢; constructor <;> linarith [hμ₀'.1, hμ₀'.2]
    linarith
  have hρr' : 160 * ρ ≤ 1 / (8 * r) := by
    have := mul_le_mul_of_nonneg_left hρr (show (0 : ℝ) ≤ 160 by norm_num)
    calc 160 * ρ ≤ 160 * (1 / (1280 * r)) := this
      _ = 1 / (8 * r) := by field_simp; ring
  show Tube ρ z' w' ⊆ Container (394 * r * ρ) (z + cpar c z w • w) w
  apply tube_subset_container hw hw' (ε := 80 * ρ) (l := 1 / (2 * r))
    (s₁ := s₀) (s₂ := s₁) (t₁ := t₀) (t₂ := t₁) (by positivity)
  · have : 640 * ρ ≤ 4 * (1 / (8 * r)) := by linarith
    calc 8 * (80 * ρ) = 640 * ρ := by ring
      _ ≤ 4 * (1 / (8 * r)) := this
      _ = 1 / (2 * r) := by field_simp; ring
  · have hA1 : ‖(z + s₁ • w) - (z + s₀ • w)‖ = |s₁ - s₀| := by
      rw [show (z + s₁ • w) - (z + s₀ • w) = (s₁ - s₀) • w by module, norm_smul,
        Real.norm_eq_abs, hw, mul_one]
    have htri : ‖unzoom r c (X + v) - unzoom r c X‖ ≤
        ‖unzoom r c (X + v) - (z + s₁ • w)‖ + ‖(z + s₁ • w) - (z + s₀ • w)‖ +
          ‖unzoom r c X - (z + s₀ • w)‖ := by
      have he : unzoom r c (X + v) - unzoom r c X =
          (unzoom r c (X + v) - (z + s₁ • w)) + ((z + s₁ • w) - (z + s₀ • w)) -
            (unzoom r c X - (z + s₀ • w)) := by abel
      rw [he]
      exact (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    rw [hpp, hA1] at htri
    have : 1 / r = 2 * (1 / (2 * r)) := by field_simp
    have h8 : 1 / (8 * r) ≤ 1 / (2 * r) / 2 := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  · have he : (z + s₀ • w) - (z' + t₀ • w') =
        -(unzoom r c X - (z + s₀ • w)) + (unzoom r c X - (z' + t₀ • w')) := by abel
    rw [he]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]; linarith
  · have he : (z + s₁ • w) - (z' + t₁ • w') =
        -(unzoom r c (X + v) - (z + s₁ • w)) + (unzoom r c (X + v) - (z' + t₁ • w')) := by
      abel
    rw [he]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]; linarith
  · have h2 : |cpar c z' w'| ≤ 5 / 4 := abs_le.mpr ⟨by linarith [hnear'.1], hnear'.2⟩
    calc |t₀| ≤ |cpar c z' w'| + |(μ₀' - 1 / 2) / r| := abs_add_le _ _
      _ ≤ 2 := by rw [abs_div, abs_of_pos hr0]; linarith
  · rw [show s₀ - cpar c z w = (μ₀ - 1 / 2) / r by simp only [s₀]; ring, abs_div,
      abs_of_pos hr0]
    linarith
  · have e1 : 3 * (16 * (80 * ρ) / (1 / (2 * r))) = 7680 * r * ρ := by field_simp; ring
    rw [e1]
    have : ρ ≤ r * ρ := le_mul_of_one_le_left hρ.le (by linarith)
    nlinarith

/-- Conflict through pieces overlapping in more than half of the second one: the old second
tube still lies in a container around the first. -/
theorem overlap_container_rev {r a ρ₀ ρt Λ : ℝ} (hr : 1 ≤ r) (ha : a = r * ρ₀) (hρ₀ : 0 < ρ₀)
    (ha1 : a ≤ 1 / 1024) (hρ₀r : ρ₀ ≤ 1 / (16384 * r))
    (hΛ : ρt + 2 * ρ₀ + 3 * (16 * ρ₀ / (1 / (2048 * r))) < 1000 * Λ)
    {c z w z' w' : Space} (hw : ‖w‖ = 1) (hw' : ‖w'‖ = 1)
    (hnear' : cpar c z' w' ∈ Icc (-(1 / 4) : ℝ) (5 / 4))
    (hover : (1 / 2 : ℝ≥0∞) * volume (Tube a (pieceBase r c z' w') w') <
      volume (Tube a (pieceBase r c z' w') w' ∩ Tube a (pieceBase r c z w) w)) :
    Tube ρt z' w' ⊆ Container Λ (cpt c z w) w := by
  have hr0 : 0 < r := by linarith
  have ha0 : 0 < a := by rw [ha]; positivity
  obtain ⟨θ₁', hθ₁', θ₂', hθ₂', hθsep, ⟨q₁, hq₁, hq₁Z'⟩, ⟨q₂, hq₂, hq₂Z'⟩⟩ :=
    overlap_far_points ha0 ha1 hw' hover
  obtain ⟨θ₁, hθ₁, hq₁Z⟩ := exists_param_of_mem_tube' hq₁
  obtain ⟨θ₂, hθ₂, hq₂Z⟩ := exists_param_of_mem_tube' hq₂
  have hq : ∀ q : Space, zoom r c (unzoom r c q) = q := unzoom_spec hr0 c
  have o₁ := old_of_new hr0 (p := unzoom r c q₁) (by rw [hq]; exact hq₁Z)
  have o₂ := old_of_new hr0 (p := unzoom r c q₂) (by rw [hq]; exact hq₂Z)
  have o₁' := old_of_new hr0 (p := unzoom r c q₁) (by rw [hq]; exact hq₁Z')
  have o₂' := old_of_new hr0 (p := unzoom r c q₂) (by rw [hq]; exact hq₂Z')
  have haρ : a / r = ρ₀ := by rw [ha]; field_simp
  rw [haρ] at o₁ o₂ o₁' o₂'
  have hhalf : ∀ θ ∈ Icc (0 : ℝ) 1, |(θ - 1 / 2) / r| ≤ 1 / 2 := by
    intro θ hθ
    rw [abs_div, abs_of_pos hr0, div_le_iff₀ hr0]
    have : |θ - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2]
    nlinarith
  set s₁ := cpar c z w + (θ₁ - 1 / 2) / r
  set s₂ := cpar c z w + (θ₂ - 1 / 2) / r
  set t₁ := cpar c z' w' + (θ₁' - 1 / 2) / r
  set t₂ := cpar c z' w' + (θ₂' - 1 / 2) / r
  have d₁ : ‖(z + s₁ • w) - (z' + t₁ • w')‖ ≤ 2 * ρ₀ := by
    have he : (z + s₁ • w) - (z' + t₁ • w') =
        -(unzoom r c q₁ - (z + s₁ • w)) + (unzoom r c q₁ - (z' + t₁ • w')) := by abel
    rw [he]; refine (norm_add_le _ _).trans ?_; rw [norm_neg]; linarith
  have d₂ : ‖(z + s₂ • w) - (z' + t₂ • w')‖ ≤ 2 * ρ₀ := by
    have he : (z + s₂ • w) - (z' + t₂ • w') =
        -(unzoom r c q₂ - (z + s₂ • w)) + (unzoom r c q₂ - (z' + t₂ • w')) := by abel
    rw [he]; refine (norm_add_le _ _).trans ?_; rw [norm_neg]; linarith
  have htsep : 1 / (1024 * r) < |t₂ - t₁| := by
    rw [show t₂ - t₁ = (θ₂' - θ₁') / r by simp only [t₁, t₂]; ring, abs_div, abs_of_pos hr0,
      lt_div_iff₀ hr0]
    have : 1 / (1024 * r) * r = 1 / 1024 := by field_simp
    linarith
  have hssep : 1 / (2048 * r) ≤ |s₂ - s₁| := by
    have h4 : ‖(t₂ - t₁) • w' - (s₂ - s₁) • w‖ ≤ 4 * ρ₀ := by
      have he : (t₂ - t₁) • w' - (s₂ - s₁) • w =
          ((z + s₁ • w) - (z' + t₁ • w')) - ((z + s₂ • w) - (z' + t₂ • w')) := by module
      rw [he]; exact (norm_sub_le _ _).trans (by linarith)
    have h5 := norm_sub_norm_le ((t₂ - t₁) • w') ((s₂ - s₁) • w)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hw, hw', mul_one,
      mul_one] at h5
    have h6 : 4 * ρ₀ ≤ 1 / (2048 * r) := by
      have := mul_le_mul_of_nonneg_left hρ₀r (show (0 : ℝ) ≤ 4 by norm_num)
      calc 4 * ρ₀ ≤ 4 * (1 / (16384 * r)) := this
        _ ≤ 1 / (2048 * r) := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have h7 : 1 / (1024 * r) = 2 * (1 / (2048 * r)) := by field_simp; ring
    linarith
  show Tube ρt z' w' ⊆ Container Λ (z + cpar c z w • w) w
  apply tube_subset_container hw hw' (ε := ρ₀) (l := 1 / (2048 * r))
    (s₁ := s₁) (s₂ := s₂) (t₁ := t₁) (t₂ := t₂) (by positivity) _ hssep d₁ d₂
  · have h1 := hhalf θ₁' hθ₁'
    have h2 : |cpar c z' w'| ≤ 5 / 4 := abs_le.mpr ⟨by linarith [hnear'.1], hnear'.2⟩
    calc |t₁| ≤ |cpar c z' w'| + |(θ₁' - 1 / 2) / r| := abs_add_le _ _
      _ ≤ 2 := by linarith
  · rw [show s₁ - cpar c z w = (θ₁ - 1 / 2) / r by simp only [s₁]; ring]
    linarith [hhalf θ₁ hθ₁]
  · exact hΛ
  · rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hρ₀r (show (0 : ℝ) ≤ 8 * (2048 * r) by positivity)
    rw [show 8 * (2048 * r) * (1 / (16384 * r)) = 1 by field_simp; ring] at this
    linarith

end

end WangZahlLot.Obl.wz_c2_slope_normalization
