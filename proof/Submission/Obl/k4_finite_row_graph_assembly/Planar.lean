import Submission.Obl.k4_finite_row_graph_assembly.GraphBounds

-- Relocated from this LOT tree, o072, x0245/3b29ff1,
-- Submission/Obl/k4_row_incidence_graph_construction/Planar.lean.
import Submission.Obl.k4_finite_row_graph_assembly.DirectionCap

open scoped BigOperators

namespace Submission.Obl.k4_finite_row_graph_assembly

namespace SelectedCells

variable {h K R s : ℝ} {f : FiniteIncidenceData h K R s} (c : SelectedCells f)

noncomputable def index : Fin c.directions.card ≃ {d // d ∈ c.directions} :=
  (Fintype.equivFinOfCardEq (by simp)).symm

theorem sum_index (g : ℤ → ℝ) :
    ∑ i : Fin c.directions.card, g (c.index i) = ∑ d ∈ c.directions, g d := by
  calc
    _ = ∑ d : {d // d ∈ c.directions}, g d :=
      Fintype.sum_equiv c.index _ _ (fun _ => rfl)
    _ = _ := by
      simpa only [Finset.attach_eq_univ] using Finset.sum_attach c.directions g

noncomputable def planar {L : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hK : 1 ≤ K) (hR : 2 ≤ R) (hKR : K ≤ R) (hs : 0 ≤ s) (hL : LossBounds K R s L) :
    PlanarGraphData h L s := by
  classical
  have hKpos : 0 < K := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hDpos : 0 < graphDenominator K R := by dsimp [graphDenominator]; positivity
  have hDle : graphDenominator K R ≤ L := by
    have hh := mul_le_mul_of_nonneg_right (show 1 ≤ K by linarith) hDpos.le
    linarith [hL.endpoint_count]
  have hNpos : (0 : ℝ) < c.directions.card := by
    exact_mod_cast c.directions_nonempty.card_pos
  have hLpos : 0 < L := hKpos.trans_le hL.base
  let dval := fun i : Fin c.directions.card => (c.index i).val
  have hdval : ∀ i, dval i ∈ c.directions := fun i => (c.index i).property
  refine {
    size := c.directions.card
    weight := fun _ => 1 / c.directions.card
    ratio := fun i => ratio (f.velocity c.first) (f.velocity c.second) (f.velocity (dval i))
    left := c.left
    right := c.right
    graph := fun i => c.graph (dval i)
    left_grid := c.left_grid
    right_grid := c.right_grid
    left_bound := ?_
    right_bound := ?_
    left_card_lower := ?_
    left_card_upper := (c.left_card hh.ne').trans (div_le_div_of_nonneg_right hL.base hh.le)
    right_card_lower := ?_
    right_card_upper := (c.right_card hh.ne').trans (div_le_div_of_nonneg_right hL.base hh.le)
    weight_nonneg := fun _ => by positivity
    sum_weight := ?_
    ratio_bound := ?_
    ratio_cap := ?_
    graph_subset := fun i => c.graph_subset (dval i) (hdval i)
    graph_card := ?_
    sum_card := ?_
    first_coordinate_cap := ?_ }
  · intro a ha
    have hb := c.left_bound hh.le a ha
    exact ⟨hb.1.trans (by linarith [hL.endpoint]), hb.2.trans (by linarith [hL.endpoint])⟩
  · intro a ha
    have hb := c.right_bound hh.le a ha
    exact ⟨hb.1.trans (by linarith [hL.endpoint]), hb.2.trans (by linarith [hL.endpoint])⟩
  · exact (one_div_le_one_div_of_le (by positivity : 0 < K * graphDenominator K R * h)
      (mul_le_mul_of_nonneg_right hL.endpoint_count hh.le)).trans
        (c.endpoint_lower_bounds hh hKpos hR1 hKR).1
  · exact (one_div_le_one_div_of_le (by positivity : 0 < K * graphDenominator K R * h)
      (mul_le_mul_of_nonneg_right hL.endpoint_count hh.le)).trans
        (c.endpoint_lower_bounds hh hKpos hR1 hKR).2
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel (ne_of_gt hNpos)
  · intro i
    have hb := ratio_bounds hR
      ((f.velocity_bound c.first c.first_mem).trans hKR)
      ((f.velocity_bound c.second c.second_mem).trans hKR)
      ((f.velocity_bound (dval i) (c.directions_subset (hdval i))).trans hKR)
      (c.separated (dval i) (hdval i)).1
      (by simpa only [abs_sub_comm] using (c.separated (dval i) (hdval i)).2)
    exact ⟨(one_div_le_one_div_of_le (by positivity : 0 < R ^ 3) hL.ratio).trans hb.1,
      hb.2.1.trans hL.ratio⟩
  · intro x r hr hr1
    have hc := selected_ratio_cap f hh (by linarith) hR hKR hs
      c.first_mem c.second_mem c.separation c.directions c.directions_subset
      c.directions_nonempty c.directions_card (fun d hd => (c.separated d hd).2) x r hr hr1
    have he : (∑ i : Fin c.directions.card,
        if ratio (f.velocity c.first) (f.velocity c.second) (f.velocity (dval i)) ∈
          Set.Icc x (x + r) then 1 / (c.directions.card : ℝ) else 0) =
        ((c.directions.filter (fun d => ratio (f.velocity c.first) (f.velocity c.second)
          (f.velocity d) ∈ Set.Icc x (x + r))).card : ℝ) / c.directions.card := by
      dsimp only [dval]
      rw [c.sum_index (fun d => if ratio (f.velocity c.first) (f.velocity c.second)
        (f.velocity d) ∈ Set.Icc x (x + r) then 1 / (c.directions.card : ℝ) else 0)]
      simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul,
        Finset.sum_const_zero, add_zero]
      ring
    rw [he]
    exact hc.trans (mul_le_mul_of_nonneg_right hL.directions (Real.rpow_nonneg (hh.le.trans hr) s))
  · intro i
    exact (one_div_le_one_div_of_le (mul_pos hDpos (sq_pos_of_pos hh))
      (mul_le_mul_of_nonneg_right hDle (sq_nonneg h))).trans
        (c.graph_card hh hR1 hKR hKpos (dval i) (hdval i))
  · intro i
    exact (c.sum_card hh hR hKR hKpos.le (dval i) (hdval i)).trans
      (div_le_div_of_nonneg_right hL.sum_count hh.le)
  · intro i x y
    have hG := c.graph_card hh hR1 hKR hKpos (dval i) (hdval i)
    have he : L * h ^ 2 * (1 / (graphDenominator K R * h ^ 2)) =
        L / graphDenominator K R := by field_simp
    calc
      _ ≤ (6 * R ^ 2 + 2) ^ 2 * K :=
        c.rectangle_card hh hKpos.le hR1 hKR (dval i) (hdval i) x y
      _ ≤ L / graphDenominator K R := (le_div_iff₀ hDpos).mpr hL.rectangle
      _ = L * h ^ 2 * (1 / (graphDenominator K R * h ^ 2)) := he.symm
      _ ≤ L * h ^ 2 * ((c.graph (dval i)).card : ℝ) :=
        mul_le_mul_of_nonneg_left hG (by positivity)

end SelectedCells
end Submission.Obl.k4_finite_row_graph_assembly
