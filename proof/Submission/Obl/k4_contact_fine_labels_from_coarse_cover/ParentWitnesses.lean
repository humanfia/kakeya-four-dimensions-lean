-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/ParentWitnesses.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.NearbyWitnesses
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.NestedWitnesses

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

open Set MeasureTheory Filter MvPolynomial

variable {α : Type*} [MeasurableSpace α] (p : Model α)

/-- Actual deep-label witnesses belong to the SAME original shallow label,
so its polynomial fit holds on their whole shallow time block. -/
def ParentNearbyVelocities (k : ℕ) (s t v : ℝ) : Prop :=
  ∀ᵐ u ∂p.μ k, ∀ i : Fin (p.n k s), u.1 ∈ p.B k s i → u.2 ∈ p.I k s i →
    (p.K k)⁻¹ ≤ |eval (p.x k u.1 u.2) (pderiv 3 (p.F k s i))| ∧
    ∃ w : Fin 3 → α × ℝ,
      (∀ e, (w e).1 ∈ p.B k s i ∧ (w e).2 ∈ p.I k s i ∧
        p.GoodPoint k (w e) ∧
        (p.K k)⁻¹ ≤ |eval (p.x k (w e).1 (w e).2) (pderiv 3 (p.F k s i))| ∧
        ‖p.base k (w e) - p.base k u‖ ≤ 6 * p.K k ^ 2 * p.q k t) ∧
      ∀ e e', e ≠ e' → p.N k ^ (-v) < |p.b k (w e).1 3 - p.b k (w e').1 3|

theorem eventually_parent_nearby_velocities (hp : p.Valid) {s t v : ℝ}
    (hs : 0 < s) (hst : s < t) (htU : t ≤ p.U) (hv : 0 < v) :
    ∀ᶠ k in atTop, p.ParentNearbyVelocities k s t v := by
  classical
  have ht : 0 < t := hs.trans hst
  have hsU : s ≤ p.U := hst.le.trans htU
  let R : ℝ := 2 + s⁻¹ + t⁻¹
  have hsi : 0 < s⁻¹ := inv_pos.mpr hs
  have hti : 0 < t⁻¹ := inv_pos.mpr ht
  have hR : 1 < R := by dsimp [R]; linarith
  have hsR : R⁻¹ ≤ s := by
    have hle : s⁻¹ ≤ R := by dsimp [R]; linarith
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le hsi hle
  have htR : R⁻¹ ≤ t := by
    have hle : t⁻¹ ≤ R := by dsimp [R]; linarith
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le hti hle
  filter_upwards [hp.labels R hR, hp.nested R hR,
    eventually_label_velocities p hp ht htU hv] with k hlabels hnested hvel
  obtain ⟨_, _, hABs, hdisj, hFs, hcover, _⟩ := hlabels s hsR hsU
  obtain ⟨_, _, hABt, _, hFt, hcovert, _⟩ := hlabels t htR htU
  choose parent hparent hJ using hnested s t hsR hst htU
  have : IsProbabilityMeasure (p.ν k) := (hp.basic k).2.1
  have hparent_ae : ∀ᵐ u ∂p.μ k, ∀ j : Fin (p.n k t),
      u.1 ∈ p.B k t j → u.2 ∈ p.I k t j → u.1 ∈ p.B k s (parent j) := by
    apply ae_child_in_true_parent (p.μ k) (p.ν k) (ENNReal.ofReal (p.K k))
      (hp.basic k).2.2.2.1 (p.j k s) (p.A k s) (p.B k s)
      (fun i => (hABs i).2.2) hdisj hcover (p.B k t) (p.I k t) parent
      (fun j => (hABt j).2.2.trans (hparent j)) hJ
  have hregular : ∀ᵐ u ∂p.μ k, ∀ i : Fin (p.n k s),
      u.1 ∈ p.B k s i → u.2 ∈ p.I k s i →
        (p.K k)⁻¹ ≤ |eval (p.x k u.1 u.2) (pderiv 3 (p.F k s i))| :=
    ae_all_iff.mpr (fun i => (hFs i).2.2.2.2.2.2.2)
  let G : Set (α × ℝ) := {u | p.GoodPoint k u ∧
    (∀ j : Fin (p.n k t), u.1 ∈ p.B k t j → u.2 ∈ p.I k t j →
      u.1 ∈ p.B k s (parent j)) ∧
    ∀ i : Fin (p.n k s), u.1 ∈ p.B k s i → u.2 ∈ p.I k s i →
      (p.K k)⁻¹ ≤ |eval (p.x k u.1 u.2) (pderiv 3 (p.F k s i))|}
  have hG : ∀ᵐ u ∂p.μ k, u ∈ G := by
    filter_upwards [Valid.ae_good p hp k, hparent_ae, hregular] with u hu hpa hr
    exact ⟨hu, hpa, hr⟩
  filter_upwards [hcovert, hregular,
    ae_time_away_from_endpoints (p.μ k) (p.ν k) (ENNReal.ofReal (p.K k))
      (hp.basic k).2.2.2.1 (p.T k s)] with u hu hru htime
  intro i hui huti
  obtain ⟨j, huj, hutj⟩ := hu
  have hji : parent j = i := by
    have hindex : p.j k s (parent j) = p.j k s i :=
      timeBlock_index_unique _ _ _ u.2 (hJ j hutj) huti htime
    by_contra hne
    exact Set.disjoint_left.mp (hdisj (parent j) i hne hindex)
      (hparent j ((hABt j).2.2 huj)) ((hABs i).2.2 hui)
  obtain ⟨w₀, hw₀, w₁, hw₁, w₂, hw₂, h01, h02, h12⟩ := hvel j G hG
  let w : Fin 3 → α × ℝ := ![w₀, w₁, w₂]
  have hmem : ∀ e, w e ∈ (p.B k t j ×ˢ p.I k t j) ∩ G := by
    intro e
    fin_cases e <;> simp only [w]
    · exact hw₀
    · exact hw₁
    · exact hw₂
  refine ⟨hru i hui huti, w, ?_, ?_⟩
  · intro e
    have hw := hmem e
    have hwB : (w e).1 ∈ p.B k s i := by
      rw [← hji]
      exact hw.2.2.1 j hw.1.1 hw.1.2
    have hwI : (w e).2 ∈ p.I k s i := by
      rw [← hji]
      exact hJ j hw.1.2
    exact ⟨hwB, hwI, hw.2.1, hw.2.2.2 i hwB hwI,
      label_base_diameter p hp ht.le (hFt j) (hABt j).2.2 hw.1 ⟨huj, hutj⟩⟩
  · intro e e' hne
    fin_cases e <;> fin_cases e'
    all_goals first
      | exact (hne rfl).elim
      | simpa [w, abs_sub_comm] using h01
      | simpa [w, abs_sub_comm] using h02
      | simpa [w, abs_sub_comm] using h12

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model
