/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file ZoomStateLists.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.ZoomIncidenceCaps
import Submission.Obl.k4_scalar_graph_residual_discovery.CurveCells
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PointStateCounts

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice

namespace Zoom

noncomputable section

theorem center_abs_le_of_coarse {ρ H : ℝ} (hρ : 0 < ρ)
    {q : Fin 5 → ℤ} {l : ScalarLine} (hl : cell ρ l.2 = q)
    (hbound : ∀ e, |l.2 e| ≤ H) (e : Fin 5) : |(center ρ q).2 e| ≤ H + ρ := by
  have hf := Int.floor_eq_iff.mp (congrFun hl e)
  have hlo := (le_div_iff₀ hρ).mp hf.1
  have hhi := (div_lt_iff₀ hρ).mp hf.2
  have he := abs_le.mp (hbound e)
  change |(q e : ℝ) * ρ| ≤ H + ρ
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The coefficient-world zoom has a controlled change on every original
physical fine state, despite the moving central curve. -/
theorem position_sub_le_of_physical_sub_le {ρ H b : ℝ}
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hH : 1 ≤ H) (q : Fin 5 → ℤ)
    (hcenter : ∀ e, |(center ρ q).2 e| ≤ H)
    (p p' : ScalarIncidence) (ht : p.2 ∈ Icc (0 : ℝ) 1) (ht' : p'.2 ∈ Icc (0 : ℝ) 1)
    (hphysical : ‖scalarPosition p - scalarPosition p'‖ ≤ b) :
    ‖position ρ q p - position ρ q p'‖ ≤ (1 + 3 * H) * b / ρ := by
  have hb : 0 ≤ b := (norm_nonneg _).trans hphysical
  have hphysical' (e : Fin 3) :
      |scalarPosition p e - scalarPosition p' e| ≤ b :=
    (norm_le_pi_norm (scalarPosition p - scalarPosition p') e).trans hphysical
  have hgap : |p.2 - p'.2| ≤ b := hphysical' 0
  have hcentral := (scalarPosition_time_lipschitz hH (center ρ q) hcenter ht ht').trans
    (mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ 3 * H))
  have hcentral' (e : Fin 3) :
      |scalarPosition (center ρ q, p.2) e - scalarPosition (center ρ q, p'.2) e| ≤ 3 * H * b :=
    (norm_le_pi_norm (scalarPosition (center ρ q, p.2) -
      scalarPosition (center ρ q, p'.2)) e).trans hcentral
  have hscaled {a a' c c' : ℝ} (ha : |a - a'| ≤ b) (hc : |c - c'| ≤ 3 * H * b) :
      |(a - c) / ρ - (a' - c') / ρ| ≤ (1 + 3 * H) * b / ρ := by
    rw [← sub_div, abs_div, abs_of_pos hρ,
      show (a - c) - (a' - c') = (a - a') - (c - c') by ring]
    exact div_le_div_of_nonneg_right
      (((abs_sub _ _).trans (add_le_add ha hc)).trans_eq (by ring)) hρ.le
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (1 + 3 * H) * b / ρ)).mpr
  intro e
  fin_cases e
  · change |p.2 - p'.2| ≤ (1 + 3 * H) * b / ρ
    apply hgap.trans
    apply (le_div_iff₀ hρ).mpr
    have hsmall := mul_le_mul_of_nonneg_right hρ₁ hb
    have hlarge := mul_nonneg (by positivity : 0 ≤ 3 * H) hb
    nlinarith
  · change |y ρ q p.1 p.2 - y ρ q p'.1 p'.2| ≤ _
    rw [y_eq, y_eq]
    exact hscaled (hphysical' 1) (hcentral' 1)
  · change |x ρ q p.1 p.2 - x ρ q p'.1 p'.2| ≤ _
    rw [x_eq, x_eq]
    exact hscaled (hphysical' 2) (hcentral' 2)

/-- Per original fine state and coefficient world there are at most 64
actual zoom-cell labels. This factor belongs in the globally charged
posterior-entry budget. -/
theorem original_state_zoom_cell_list {ρ b r H : ℝ}
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hb : 0 < b) (hr : 0 < r) (hH : 1 ≤ H)
    (hsmall : (1 + 3 * H) * b ≤ ρ * r) (q : Fin 5 → ℤ)
    (hcenter : ∀ e, |(center ρ q).2 e| ≤ H) (w : Fin 3 → ℤ)
    (E : Set ScalarIncidence) (htime : ∀ p ∈ E, p.2 ∈ Icc (0 : ℝ) 1)
    (hstate : ∀ p ∈ E, cell b (scalarPosition p) = w) :
    ∃ Q : Finset (Fin 3 → ℤ), (Q.card : ℝ) ≤ 64 ∧
      ∀ p ∈ E, cell r (position ρ q p) ∈ Q := by
  classical
  have hdiam (p : ScalarIncidence) (hp : p ∈ E) (p' : ScalarIncidence) (hp' : p' ∈ E) :
      ‖position ρ q p - position ρ q p'‖ ≤ r := by
    apply (position_sub_le_of_physical_sub_le hρ hρ₁ hH q hcenter p p'
      (htime p hp) (htime p' hp')
      (norm_sub_lt_of_cell_eq hb ((hstate p hp).trans (hstate p' hp').symm)).le).trans
    exact (div_le_iff₀ hρ).mpr (by nlinarith only [hsmall])
  have hrec := Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PointStateCounts.records_finite_card_of_relative_diameter
    E (position ρ q) (fun _ => r) 1 (fun _ => hr) (by norm_num) (by
      intro e p hp p' hp'
      simpa only [one_mul, Pi.sub_apply, Real.norm_eq_abs] using (norm_le_pi_norm (position ρ q p - position ρ q p') e).trans
        (hdiam p hp p' hp'))
  have hfin : ((fun p => cell r (position ρ q p)) '' E).Finite := hrec.1
  have hcard := hrec.2
  norm_num at hcard
  refine ⟨hfin.toFinset, ?_, fun p hp => hfin.mem_toFinset.mpr ⟨p, hp, rfl⟩⟩
  rw [← Set.ncard_eq_toFinset_card _ hfin]
  exact_mod_cast hcard

/-- Add actual zoom physical-cell labels to an original coefficient-world
list. The number of posterior entries grows only by an absolute factor. -/
theorem posterior_entry_list {ρ b r H D : ℝ}
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hb : 0 < b) (hr : 0 < r) (hH : 1 ≤ H)
    (hsmall : (1 + 3 * (H + 1)) * b ≤ ρ * r) (w : Fin 3 → ℤ)
    (E : Set ScalarIncidence) (htime : ∀ p ∈ E, p.2 ∈ Icc (0 : ℝ) 1)
    (hcoeff : ∀ p ∈ E, ∀ e, |p.1.2 e| ≤ H)
    (hstate : ∀ p ∈ E, cell b (scalarPosition p) = w)
    (coarse : Finset (Fin 5 → ℤ)) (hcard : (coarse.card : ℝ) ≤ D)
    (hcoarse : ∀ p ∈ E, cell ρ p.1.2 ∈ coarse) :
    ∃ L : Finset ((Fin 5 → ℤ) × (Fin 3 → ℤ)), (L.card : ℝ) ≤ 64 * D ∧
      ∀ p ∈ E, (cell ρ p.1.2, cell r (position ρ (cell ρ p.1.2) p)) ∈ L := by
  classical
  have hcell (q : Fin 5 → ℤ) : ∃ Q : Finset (Fin 3 → ℤ), (Q.card : ℝ) ≤ 64 ∧
      ∀ p ∈ E, cell ρ p.1.2 = q → cell r (position ρ q p) ∈ Q := by
    by_cases hne : ({p ∈ E | cell ρ p.1.2 = q}).Nonempty
    · obtain ⟨p₀, hp₀⟩ := hne
      have hcenter (e : Fin 5) : |(center ρ q).2 e| ≤ H + 1 :=
        (center_abs_le_of_coarse hρ hp₀.2 (hcoeff p₀ hp₀.1) e).trans
          (add_le_add le_rfl hρ₁)
      obtain ⟨Q, hQ, hmem⟩ := original_state_zoom_cell_list hρ hρ₁ hb hr
        (by linarith : 1 ≤ H + 1) hsmall q hcenter w {p ∈ E | cell ρ p.1.2 = q}
        (fun p hp => htime p hp.1) (fun p hp => hstate p hp.1)
      exact ⟨Q, hQ, fun p hp hq => hmem p ⟨hp, hq⟩⟩
    · exact ⟨∅, by simp, fun p hp hq => False.elim (hne ⟨p, hp, hq⟩)⟩
  choose Q hQ hmem using hcell
  let L := coarse.biUnion (fun q => (Q q).image (fun z => (q, z)))
  refine ⟨L, ?_, ?_⟩
  · calc
      (L.card : ℝ) ≤ ∑ q ∈ coarse, (((Q q).image (fun z => (q, z))).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ q ∈ coarse, ((Q q).card : ℝ) := Finset.sum_le_sum
        (fun q _ => by exact_mod_cast Finset.card_image_le)
      _ ≤ ∑ _q ∈ coarse, (64 : ℝ) := Finset.sum_le_sum (fun q _ => hQ q)
      _ = (coarse.card : ℝ) * 64 := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 64 * D := by nlinarith only [hcard]
  · intro p hp
    apply Finset.mem_biUnion.mpr
    refine ⟨cell ρ p.1.2, hcoarse p hp, ?_⟩
    exact Finset.mem_image.mpr ⟨_, hmem _ p hp rfl, rfl⟩

end

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
