/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file RepresentativeChoice.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.GraphSelection

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice

noncomputable section

/-- Choose representatives in the actual final entries and apply common
local choice to the original state record. Errors below the finest scale
transfer its comparison to the actual residual, without splitting a state. -/
theorem representative_whole_state_choice {X Q : Type*}
    [MeasurableSpace X] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    {D q : ℕ} (μ : Measure X) (record : X → Q) (hrecord : Measurable record)
    (Z : X → Fin D → ℝ) (Y : Q → Fin q → ℝ) (actual : X → Fin q → ℝ)
    (E : Set X) (hE : μ Eᶜ = 0) {B εZ εY : ℝ} (hB₀ : 0 ≤ B)
    (hB : ∀ p ∈ E, ‖Y (record p)‖ ≤ B)
    (hdiam : ∀ p ∈ E, ∀ p' ∈ E, record p = record p' → ‖Z p - Z p'‖ ≤ εZ)
    (herror : ∀ p ∈ E, ‖actual p - Y (record p)‖ ≤ εY)
    (L : ℕ) (hL : 1 ≤ L) (s : ℕ → ℝ) (K : ℕ → ℕ) (A : ℝ) (hA₁ : 1 ≤ A)
    (hs₀ : s 0 = 1) (hs : ∀ i, 0 < s i)
    (hA : ∀ i, i + 1 < L → s i ≤ A * s (i + 1))
    (hεZ : εZ ≤ s (L - 1)) (hεY : εY ≤ s (L - 1))
    (F : ℕ → (Fin D → ℤ) → Finset (Fin q → ℤ))
    (hFcard : ∀ i < L, ∀ n, (F i n).card ≤ K i)
    (hF : ∀ i < L, ∀ p ∈ E, cell (s i) (Y (record p)) ∈ F i (cell (s i) (Z p))) :
    ∃ S : Set Q, MeasurableSet S ∧
      μ univ ≤ (∏ i ∈ Finset.range L, ((4 : ℝ≥0∞) ^ D * K i)) * μ (record ⁻¹' S) ∧
      ∀ p ∈ E, record p ∈ S → ∀ p' ∈ E, record p' ∈ S →
        ‖actual p - actual p'‖ ≤
          6 * (A + B + 1) * (‖Z p - Z p'‖ + s (L - 1)) := by
  classical
  have hwitness (a : Q) (ha : (μ.map record) {a} ≠ 0) : ∃ p ∈ E, record p = a := by
    have hpos : μ (record ⁻¹' {a} ∩ E) ≠ 0 := by
      rw [measure_inter_conull hE]
      simpa only [Measure.map_apply hrecord (measurableSet_singleton a)] using ha
    obtain ⟨p, hpa, hpE⟩ := nonempty_of_measure_ne_zero hpos
    exact ⟨p, hpE, hpa⟩
  let Zrep (a : Q) : Fin D → ℝ :=
    if ha : (μ.map record) {a} ≠ 0 then Z (Classical.choose (hwitness a ha)) else 0
  have hrep (a : Q) (ha : (μ.map record) {a} ≠ 0) :
      ∃ p ∈ E, record p = a ∧ Zrep a = Z p := by
    refine ⟨Classical.choose (hwitness a ha), (Classical.choose_spec (hwitness a ha)).1,
      (Classical.choose_spec (hwitness a ha)).2, ?_⟩
    simp only [Zrep, dite_eq_left ha]
  have hbound (a : Q) (ha : (μ.map record) {a} ≠ 0) : ‖Y a‖ ≤ B := by
    obtain ⟨p, hp, hpa, _⟩ := hrep a ha
    simpa only [hpa] using hB p hp
  have hlist (i : ℕ) (hi : i < L) (n : Fin D → ℤ) :
      ∃ G : Finset (Fin q → ℤ), G.card ≤ K i ∧
        ∀ a, (μ.map record) {a} ≠ 0 → cell (s i) (Zrep a) = n → cell (s i) (Y a) ∈ G := by
    refine ⟨F i n, hFcard i hi n, ?_⟩
    intro a ha han
    obtain ⟨p, hp, hpa, hZpa⟩ := hrep a ha
    have hcell : cell (s i) (Z p) = n := by rw [← hZpa]; exact han
    simpa only [hpa, hcell] using hF i hi p hp
  obtain ⟨S, hS, hpositive, hmass, hcmp⟩ := whole_state_common_choice μ record hrecord Zrep Y
    hB₀ hbound L hL s K A hA₁ hs₀ hs hA hlist
  refine ⟨S, hS, hmass, ?_⟩
  intro p hp hpS p' hp' hp'S
  have hclose (z : X) (hz : z ∈ E) (hzS : record z ∈ S) :
      ‖Z z - Zrep (record z)‖ ≤ εZ := by
    obtain ⟨u, hu, hzu, hZzu⟩ := hrep (record z) (hpositive _ hzS)
    rw [hZzu]
    exact hdiam z hz u hu hzu.symm
  have hrepdist : ‖Zrep (record p) - Zrep (record p')‖ ≤
      ‖Z p - Z p'‖ + 2 * s (L - 1) := by
    calc
      _ ≤ ‖Zrep (record p) - Z p‖ + ‖Z p - Zrep (record p')‖ := by
        simpa only [dist_eq_norm] using dist_triangle (Zrep (record p)) (Z p) (Zrep (record p'))
      _ ≤ εZ + (‖Z p - Z p'‖ + εZ) := by
        apply add_le_add (by simpa only [norm_sub_rev] using hclose p hp hpS)
        apply (show ‖Z p - Zrep (record p')‖ ≤ ‖Z p - Z p'‖ + ‖Z p' - Zrep (record p')‖ from
          by simpa only [dist_eq_norm] using dist_triangle (Z p) (Z p') (Zrep (record p'))).trans
        exact add_le_add le_rfl (hclose p' hp' hp'S)
      _ ≤ _ := by linarith only [hεZ]
  have hcanonical : ‖Y (record p) - Y (record p')‖ ≤
      2 * (A + B) * (‖Z p - Z p'‖ + 3 * s (L - 1)) := by
    apply (hcmp _ hpS _ hp'S).trans
    exact mul_le_mul_of_nonneg_left (by linarith only [hrepdist]) (by positivity)
  have htriangle : ‖actual p - actual p'‖ ≤
      ‖actual p - Y (record p)‖ + ‖Y (record p) - Y (record p')‖ +
        ‖Y (record p') - actual p'‖ := by
    calc
      _ ≤ ‖actual p - Y (record p)‖ + ‖Y (record p) - actual p'‖ := by
        simpa only [dist_eq_norm] using dist_triangle (actual p) (Y (record p)) (actual p')
      _ ≤ ‖actual p - Y (record p)‖ +
          (‖Y (record p) - Y (record p')‖ + ‖Y (record p') - actual p'‖) := by
        apply add_le_add le_rfl
        simpa only [dist_eq_norm] using dist_triangle (Y (record p)) (Y (record p')) (actual p')
      _ = _ := by ring
  have he₁ := herror p hp
  have he₂ : ‖Y (record p') - actual p'‖ ≤ εY := by simpa only [norm_sub_rev] using herror p' hp'
  have hnonneg : 0 ≤ (4 * (A + B) + 6) * ‖Z p - Z p'‖ := by positivity
  have hlast := hs (L - 1)
  nlinarith only [htriangle, he₁, he₂, hcanonical, hεY, hnonneg, hlast]

end

end Submission.Obl.k4_scalar_graph_residual_discovery
