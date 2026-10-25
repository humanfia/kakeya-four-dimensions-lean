-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.ClusteredFilling.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_transverse_cell_weighted_cover.Local

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover

theorem clustered_filling_arithmetic {a b h θ r M L V : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hθ : 0 < θ) (hL : 0 < L)
    (hgrid : r * a * b ^ 2 ≤ 20 * a * b * (32 * a / θ) * M)
    (hmoment : (h * a * b ^ 2 / 8) ^ 2 * M ≤ 10000 * a * b ^ 2 * L * V) :
    r * h ^ 2 * θ * b ^ 3 / (409600000 * L) ≤ V := by
  have hM : r * b * θ / (640 * a) ≤ M := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hgrid hθ.le
    have he : (20 * a * b * (32 * a / θ) * M) * θ = (a * b) * (640 * a * M) := by
      field_simp
      ring
    rw [he] at hh
    apply le_of_mul_le_mul_left (a := a * b) _ (by positivity)
    nlinarith
  have hcoef : 0 ≤ (h * a * b ^ 2 / 8) ^ 2 / (10000 * a * b ^ 2 * L) := by positivity
  calc
    _ = ((h * a * b ^ 2 / 8) ^ 2 / (10000 * a * b ^ 2 * L)) *
        (r * b * θ / (640 * a)) := by field_simp; ring
    _ ≤ ((h * a * b ^ 2 / 8) ^ 2 / (10000 * a * b ^ 2 * L)) * M :=
      mul_le_mul_of_nonneg_left hM hcoef
    _ ≤ V := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [hmoment]

/-- Transverse filling for a single class of close oriented normals. The angle
appears only once, matching the volume of the thin neighbourhood being filled;
there is no loss from an angular pigeonhole in this statement. -/
theorem clustered_filling_in_container {n : ℕ} (K : Finset (Fin n))
    {a b h θ r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 1000000)
    (hh : 0 < h) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hr : 0 < r)
    (c : Fin n → Space) (u : Fin n → Fin 3 → Space) (H : Fin n → Set Space)
    (c₀ x w v : Space) (u₀ : Fin 3 → Space) (A E : Set Space)
    (hu : ∀ i ∈ K, Orthonormal ℝ (u i))
    (hHm : ∀ i ∈ K, MeasurableSet (H i))
    (hHU : ∀ i ∈ K, H i ⊆ prism a b (c i) (u i))
    (hregular : ∀ i ∈ K, ∀ p ∈ H i,
      ENNReal.ofReal h * volume (prism a b (c i) (u i) ∩ ball p b) ≤ volume (H i ∩ ball p b))
    (hu₀ : Orthonormal ℝ u₀) (hframe : Orthonormal ℝ ![u₀ 0, w, v])
    (hA : A ⊆ prism a b c₀ u₀ ∩ ball x b)
    (hcover : A ⊆ ⋃ i ∈ K, H i) (hmass : ENNReal.ofReal (r * a * b ^ 2) ≤ volume A)
    (htrans : ∀ i ∈ K, θ / 4 ≤ inner ℝ (sgnNormal (u i 0)) v)
    (hclose : ∀ i ∈ K, ∀ j ∈ K, ‖sgnNormal (u i 0) - sgnNormal (u j 0)‖ ≤ θ / 4)
    (hEm : MeasurableSet E) (hEfin : volume E ≠ ⊤)
    (hneighborhoods : ∀ i ∈ K, ∀ y ∈ A, y ∈ H i → H i ∩ ball y b ⊆ E) :
    ENNReal.ofReal (r * h ^ 2 * θ * b ^ 3 / (409600000 * (1 + Real.log (b / a)))) ≤
      volume E := by
  classical
  have hb0 : 0 < b := ha.trans_le hab
  have hL : 0 < 1 + Real.log (b / a) := by
    have := Real.log_nonneg ((one_le_div ha).mpr hab)
    linarith
  have hApos : volume A ≠ 0 := (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) hmass).ne'
  obtain ⟨q₀, hq₀⟩ := nonempty_of_measure_ne_zero hApos
  obtain ⟨i₀, hi₀, _⟩ := mem_iUnion₂.mp (hcover hq₀)
  have hstep : a ≤ 32 * a / θ := by rw [le_div_iff₀ hθ]; nlinarith
  obtain ⟨J, y, hy, hgrid, hpairs, hjbound⟩ := grid_selection ha hab hstep hu₀ hframe A hA
  have hchoice : ∀ j : ℤ, ∃ i : Fin n, j ∈ J → i ∈ K ∧ y j ∈ H i := by
    intro j
    by_cases hj : j ∈ J
    · obtain ⟨i, hi, hiy⟩ := mem_iUnion₂.mp (hcover (hy j hj))
      exact ⟨i, fun _ => ⟨hi, hiy⟩⟩
    · exact ⟨i₀, fun hj' => (hj hj').elim⟩
  choose sel hsel using hchoice
  let Z : ℤ → Set Space := fun j => H (sel j) ∩ ball (y j) b
  have hZm : ∀ j ∈ J, MeasurableSet (Z j) := fun j hj => (hHm _ (hsel j hj).1).inter measurableSet_ball
  have hZE : ∀ j ∈ J, Z j ⊆ E := fun j hj =>
    hneighborhoods (sel j) (hsel j hj).1 (y j) (hy j hj) (hsel j hj).2
  have hlower : ∀ j ∈ J, h * a * b ^ 2 / 8 ≤ (volume (Z j)).toReal := by
    intro j hj
    have hi := hsel j hj
    have h := loc_regular_lower ha hab hb hh.le (hu _ hi.1) (hHU _ hi.1 hi.2)
      (hregular _ hi.1 _ hi.2)
    exact (ENNReal.ofReal_le_iff_le_toReal
      (ne_top_of_le_ne_top hEfin (measure_mono (hZE j hj)))).mp h
  have hslabs : ∀ j ∈ J, Z j ⊆
      {p | |inner ℝ (sgnNormal (u (sel j) 0)) (p - y j)| ≤ 2 * a} ∩ ball (y j) b := by
    intro j hj p hp
    have hi := hsel j hj
    exact ⟨loc_slab_of_prism (hHU _ hi.1 hi.2) (hHU _ hi.1 hp.1), hp.2⟩
  have hnormalcoord : ∀ j ∈ J, ∀ j' ∈ J, |inner ℝ (u₀ 0) (y j' - y j)| ≤ 2 * a := by
    intro j hj j' hj'
    simpa only [abs_inner_sgnNormal] using
      loc_slab_of_prism (hA (hy j hj)).1 (hA (hy j' hj')).1
  have hdist : ∀ j ∈ J, ∀ j' ∈ J, ‖y j' - y j‖ ≤ 2 * b := by
    intro j hj j' hj'
    have hjx : ‖y j - x‖ < b := by simpa only [mem_ball, dist_eq_norm] using (hA (hy j hj)).2
    have hj'x : ‖y j' - x‖ < b := by simpa only [mem_ball, dist_eq_norm] using (hA (hy j' hj')).2
    have he : y j' - y j = (y j' - x) - (y j - x) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith)
  have hrow := loc_row_bound ha hab hθ hθ1 hframe J y (fun j => sgnNormal (u (sel j) 0)) Z
    (fun j hj => by rw [norm_sgnNormal]; exact (hu _ (hsel j hj).1).1 0)
    (fun j hj => htrans _ (hsel j hj).1)
    (fun j hj j' hj' => hclose _ (hsel j hj).1 _ (hsel j' hj').1)
    hslabs hnormalcoord hdist hpairs hjbound
  have hmoment := loc_second_moment J Z E (h * a * b ^ 2 / 8)
    (10000 * a * b ^ 2 * (1 + Real.log (b / a))) hEm hEfin hZm hZE
    (by positivity) (by positivity) hlower hrow
  have hgrid' : r * a * b ^ 2 ≤ 20 * a * b * (32 * a / θ) * J.card :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hmass.trans hgrid)
  have hbound := clustered_filling_arithmetic ha hb0 hθ hL hgrid' hmoment
  exact (ENNReal.ofReal_le_ofReal hbound).trans_eq (ENNReal.ofReal_toReal hEfin)

/-- The clustered filling estimate in an ordinary ball. -/
theorem clustered_local_filling {n : ℕ} (K : Finset (Fin n))
    {a b h θ r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 1000000)
    (hh : 0 < h) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hr : 0 < r)
    (c : Fin n → Space) (u : Fin n → Fin 3 → Space) (H : Fin n → Set Space)
    (c₀ x w v : Space) (u₀ : Fin 3 → Space) (A : Set Space)
    (hu : ∀ i ∈ K, Orthonormal ℝ (u i))
    (hHm : ∀ i ∈ K, MeasurableSet (H i))
    (hHU : ∀ i ∈ K, H i ⊆ prism a b (c i) (u i))
    (hregular : ∀ i ∈ K, ∀ p ∈ H i,
      ENNReal.ofReal h * volume (prism a b (c i) (u i) ∩ ball p b) ≤ volume (H i ∩ ball p b))
    (hu₀ : Orthonormal ℝ u₀) (hframe : Orthonormal ℝ ![u₀ 0, w, v])
    (hA : A ⊆ prism a b c₀ u₀ ∩ ball x b)
    (hcover : A ⊆ ⋃ i ∈ K, H i) (hmass : ENNReal.ofReal (r * a * b ^ 2) ≤ volume A)
    (htrans : ∀ i ∈ K, θ / 4 ≤ inner ℝ (sgnNormal (u i 0)) v)
    (hclose : ∀ i ∈ K, ∀ j ∈ K, ‖sgnNormal (u i 0) - sgnNormal (u j 0)‖ ≤ θ / 4) :
    ENNReal.ofReal (r * h ^ 2 * θ * b ^ 3 / (409600000 * (1 + Real.log (b / a)))) ≤
      volume (ball x (2 * b) ∩ ⋃ i ∈ K, H i) := by
  apply clustered_filling_in_container K ha hab hb hh hθ hθ1 hr c u H c₀ x w v u₀ A _
    hu hHm hHU hregular hu₀ hframe hA hcover hmass htrans hclose
    (measurableSet_ball.inter (Finset.measurableSet_biUnion K hHm))
    (ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono inter_subset_left))
  intro i hi y hyA hyH p hp
  refine ⟨?_, mem_iUnion₂.mpr ⟨i, hi, hp.1⟩⟩
  have hp' : dist p y < b := hp.2
  have hy' : dist y x < b := (hA hyA).2
  change dist p x < 2 * b
  exact (dist_triangle _ _ _).trans_lt (by linarith)

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
