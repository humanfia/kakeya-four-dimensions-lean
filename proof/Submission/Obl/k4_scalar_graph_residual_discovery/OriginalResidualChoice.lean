/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file OriginalResidualChoice.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.RepresentativeChoice
import Submission.Obl.k4_scalar_graph_residual_discovery.ResidualZoom
import Submission.Obl.k4_scalar_graph_residual_discovery.ZoomStateLists

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice

namespace Zoom

noncomputable section

theorem abs_residual_le {ρ H : ℝ} (hρ : 0 < ρ) {q : Fin 5 → ℤ} {l : ScalarLine}
    (hl : cell ρ l.2 = q) {F : ℝ → ℝ} {t : ℝ} (ht : |t| ≤ 1) (hF : |F t| ≤ H) :
    |residual ρ q F l t| ≤ 3 + H := by
  have hH : 0 ≤ H := (abs_nonneg _).trans hF
  have hquad : |2 * t * coeff ρ q l 2| ≤ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 2))
      (coeff_abs_le_one hρ hl 2) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2 * 1)
    simpa only [mul_one] using hh
  have hprod : |F t * coeff ρ q l 4| ≤ H := by
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul hF (coeff_abs_le_one hρ hl 4) (abs_nonneg _) hH
  unfold residual
  exact ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    (by linarith [coeff_abs_le_one hρ hl 1])

/-- Raw scalar residual lists at finitely many scales give actual `ResC`
by selecting WHOLE original fine states. The original graph error and
time-row approximation supply the representative errors; no fresh zoom
state or selected-label prior is introduced. -/
theorem original_state_residual_common_choice
    (μ : Measure ScalarIncidence) (E : Set ScalarIncidence) (hE : μ Eᶜ = 0)
    {ρ b ζ H Hc δ ε : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hb : 0 < b)
    (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) (hH : 0 ≤ H) (hHc : 1 ≤ Hc)
    (q : Fin 5 → ℤ) (F : ℝ → ℝ) (G : (Fin 3 → ℤ) → Fin 2 → ℝ)
    (hworld : ∀ p ∈ E, cell ρ p.1.2 = q)
    (htime : ∀ p ∈ E, p.2 ∈ Icc (0 : ℝ) 1)
    (hF : ∀ p ∈ E, |F p.2| ≤ H)
    (hcenter : ∀ e, |(center ρ q).2 e| ≤ Hc)
    (hrow : ∀ p ∈ E, |G (cell b (scalarPosition p)) 1 - F p.2| ≤ δ)
    (hgraph : ∀ p ∈ E,
      |p.1.2 3 + 2 * p.2 * p.1.2 4 - G (cell b (scalarPosition p)) 0 -
        G (cell b (scalarPosition p)) 1 * p.1.2 1| ≤ ε)
    (hdiam : (1 + 3 * Hc) * b / ρ ≤ ζ)
    (herror : δ + ε / ρ + 2 * Hc * b / ρ ≤ ζ)
    (L : ℕ) (hL : 1 ≤ L) (s : ℕ → ℝ) (K : ℕ → ℕ)
    (A : ℝ) (hA : 1 ≤ A) (hs₀ : s 0 = 1) (hs : ∀ i, 0 < s i)
    (hratio : ∀ i, i + 1 < L → s i ≤ A * s (i + 1)) (hlast : s (L - 1) = ζ)
    (lists : ℕ → (Fin 3 → ℤ) → Finset ℤ)
    (hcard : ∀ i < L, ∀ z, (lists i z).card ≤ K i)
    (hlist : ∀ i < L, ∀ p ∈ E,
      ⌊stateResidual ρ b q G (cell b (scalarPosition p)) / s i⌋ ∈
        lists i (cell (s i) (position ρ q p))) :
    ∃ S : Set (Fin 3 → ℤ), MeasurableSet S ∧
      μ univ ≤ (∏ i ∈ Finset.range L, ((4 : ℝ≥0∞) ^ 3 * K i)) *
        μ {p | cell b (scalarPosition p) ∈ S} ∧
      ∀ p ∈ E, cell b (scalarPosition p) ∈ S →
        ∀ p' ∈ E, cell b (scalarPosition p') ∈ S →
          |residual ρ q F p.1 p.2 - residual ρ q F p'.1 p'.2| ≤
            6 * (A + H + 5) * (‖position ρ q p - position ρ q p'‖ + ζ) := by
  classical
  let record (p : ScalarIncidence) := cell b (scalarPosition p)
  let Y (w : Fin 3 → ℤ) (_ : Fin 1) := stateResidual ρ b q G w
  let actual (p : ScalarIncidence) (_ : Fin 1) := residual ρ q F p.1 p.2
  have hrecord : Measurable record := measurable_cell b measurable_scalarPosition
  have hstateerror (p : ScalarIncidence) (hp : p ∈ E) :
      |residual ρ q F p.1 p.2 - stateResidual ρ b q G (record p)| ≤ ζ :=
    (residual_near_original_state hρ hb q F G p (record p) (hworld p hp) rfl
      (hcenter 4) (hrow p hp) (hgraph p hp)).trans herror
  have habs (p : ScalarIncidence) (hp : p ∈ E) : |residual ρ q F p.1 p.2| ≤ 3 + H := by
    have ht : |p.2| ≤ 1 := by rw [abs_of_nonneg (htime p hp).1]; exact (htime p hp).2
    exact abs_residual_le hρ (hworld p hp) ht (hF p hp)
  have hbound (p : ScalarIncidence) (hp : p ∈ E) : ‖Y (record p)‖ ≤ 4 + H := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 4 + H)).mpr
    intro e
    have hh : |stateResidual ρ b q G (record p)| ≤
        |residual ρ q F p.1 p.2| +
          |residual ρ q F p.1 p.2 - stateResidual ρ b q G (record p)| := by
      have hid : stateResidual ρ b q G (record p) =
          residual ρ q F p.1 p.2 - (residual ρ q F p.1 p.2 - stateResidual ρ b q G (record p)) := by ring
      conv_lhs => rw [hid]
      exact abs_sub _ _
    change |stateResidual ρ b q G (record p)| ≤ 4 + H
    linarith only [hh, habs p hp, hstateerror p hp, hζ₁]
  have hrepdiam (p : ScalarIncidence) (hp : p ∈ E) (p' : ScalarIncidence) (hp' : p' ∈ E)
      (heq : record p = record p') : ‖position ρ q p - position ρ q p'‖ ≤ ζ :=
    (position_sub_le_of_physical_sub_le hρ hρ₁ hHc q hcenter p p'
      (htime p hp) (htime p' hp') (norm_sub_lt_of_cell_eq hb heq).le).trans hdiam
  have hrepError (p : ScalarIncidence) (hp : p ∈ E) : ‖actual p - Y (record p)‖ ≤ ζ := by
    apply (pi_norm_le_iff_of_nonneg hζ.le).mpr
    intro e
    exact hstateerror p hp
  let vectorLists (i : ℕ) (z : Fin 3 → ℤ) := (lists i z).image (fun j => fun _ : Fin 1 => j)
  have hvectorcard (i : ℕ) (hi : i < L) (z : Fin 3 → ℤ) :
      (vectorLists i z).card ≤ K i := Finset.card_image_le.trans (hcard i hi z)
  have hvectorList (i : ℕ) (hi : i < L) (p : ScalarIncidence) (hp : p ∈ E) :
      cell (s i) (Y (record p)) ∈ vectorLists i (cell (s i) (position ρ q p)) :=
    Finset.mem_image.mpr ⟨_, hlist i hi p hp, rfl⟩
  obtain ⟨S, hS, hmass, hcmp⟩ := representative_whole_state_choice μ record hrecord
    (position ρ q) Y actual E hE (by positivity : 0 ≤ 4 + H) hbound hrepdiam hrepError
    L hL s K A hA hs₀ hs hratio hlast.symm.le hlast.symm.le vectorLists hvectorcard hvectorList
  refine ⟨S, hS, hmass, ?_⟩
  intro p hp hpS p' hp' hp'S
  calc
    _ ≤ ‖actual p - actual p'‖ := norm_le_pi_norm (actual p - actual p') (0 : Fin 1)
    _ ≤ 6 * (A + (4 + H) + 1) * (‖position ρ q p - position ρ q p'‖ + s (L - 1)) :=
      hcmp p hp hpS p' hp' hp'S
    _ = _ := by rw [hlast]; ring

end

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
