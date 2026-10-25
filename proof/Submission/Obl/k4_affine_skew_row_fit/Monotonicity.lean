import Submission.Obl.k4_affine_skew_row_fit.Interfaces

namespace Submission.Obl.k4_affine_skew_row_fit

/-- All finite planar hypotheses weaken monotonically with the common loss factor. -/
noncomputable def PlanarGraphData.enlarge {h K K' S : ℝ}
    (d : PlanarGraphData h K S) (hh : 0 < h) (hK : 0 < K) (hKK' : K ≤ K') :
    PlanarGraphData h K' S where
  size := d.size
  weight := d.weight
  ratio := d.ratio
  left := d.left
  right := d.right
  graph := d.graph
  left_grid := d.left_grid
  right_grid := d.right_grid
  left_bound := fun x hx => ⟨(d.left_bound x hx).1.trans hKK', (d.left_bound x hx).2.trans hKK'⟩
  right_bound := fun x hx => ⟨(d.right_bound x hx).1.trans hKK', (d.right_bound x hx).2.trans hKK'⟩
  left_card_lower :=
    (one_div_le_one_div_of_le (mul_pos hK hh)
      (mul_le_mul_of_nonneg_right hKK' hh.le)).trans d.left_card_lower
  left_card_upper := d.left_card_upper.trans (div_le_div_of_nonneg_right hKK' hh.le)
  right_card_lower :=
    (one_div_le_one_div_of_le (mul_pos hK hh)
      (mul_le_mul_of_nonneg_right hKK' hh.le)).trans d.right_card_lower
  right_card_upper := d.right_card_upper.trans (div_le_div_of_nonneg_right hKK' hh.le)
  weight_nonneg := d.weight_nonneg
  sum_weight := d.sum_weight
  ratio_bound := fun i =>
    ⟨(one_div_le_one_div_of_le hK hKK').trans (d.ratio_bound i).1,
      (d.ratio_bound i).2.trans hKK'⟩
  ratio_cap := fun x r hr hr1 => (d.ratio_cap x r hr hr1).trans
    (mul_le_mul_of_nonneg_right hKK' (Real.rpow_nonneg (hh.le.trans hr) S))
  graph_subset := d.graph_subset
  graph_card := fun i =>
    (one_div_le_one_div_of_le (mul_pos hK (sq_pos_of_pos hh))
      (mul_le_mul_of_nonneg_right hKK' (sq_nonneg h))).trans (d.graph_card i)
  sum_card := fun i => (d.sum_card i).trans (div_le_div_of_nonneg_right hKK' hh.le)
  first_coordinate_cap := fun i x y => (d.first_coordinate_cap i x y).trans (by
    have := mul_le_mul_of_nonneg_right hKK'
      (mul_nonneg (sq_nonneg h) (Nat.cast_nonneg (d.graph i).card))
    simpa only [mul_assoc] using this)

/-- Enlarging the loss also preserves the same original incidence witness sets. -/
noncomputable def RowGraphWitness.enlarge {α : Type} [MeasurableSpace α]
    {ν : MeasureTheory.Measure α} {μ : MeasureTheory.Measure (α × ℝ)}
    {z T : α × ℝ → Fin 2 → ℝ} {h E K K' S : ℝ}
    (d : RowGraphWitness ν μ z T h E K S) (hh : 0 < h) (hK : 0 < K) (hKK' : K ≤ K') :
    RowGraphWitness ν μ z T h E K' S where
  planar := d.planar.enlarge hh hK hKK'
  v₁ := d.v₁
  v₂ := d.v₂
  velocity_bound₁ := d.velocity_bound₁.trans hKK'
  velocity_bound₂ := d.velocity_bound₂.trans hKK'
  velocity_separation := (one_div_le_one_div_of_le hK hKK').trans d.velocity_separation
  domination := d.domination.trans (by
    intro s
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hKK')
      (zero_le : (0 : ENNReal) ≤ (ν.prod MeasureTheory.volume) s))
  witness := d.witness
  measurable_witness := d.measurable_witness
  disjoint_witness := d.disjoint_witness
  witness_mass := fun i e he =>
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (sq_nonneg h) hK hKK')).trans
      (d.witness_mass i e he)
  witness_bounds := fun i e he p hp =>
    ⟨(d.witness_bounds i e he p hp).1,
      (d.witness_bounds i e he p hp).2.1.trans hKK',
      fun j => ((d.witness_bounds i e he p hp).2.2 j).trans hKK'⟩
  witness_projections := fun i e he p hp =>
    ⟨(d.witness_projections i e he p hp).1.trans (mul_le_mul_of_nonneg_right hKK' hh.le),
      (d.witness_projections i e he p hp).2.1.trans (mul_le_mul_of_nonneg_right hKK' hh.le),
      (d.witness_projections i e he p hp).2.2.1.trans (mul_le_mul_of_nonneg_right hKK' hh.le),
      (d.witness_projections i e he p hp).2.2.2.trans (mul_le_mul_of_nonneg_right hKK' hh.le)⟩

end Submission.Obl.k4_affine_skew_row_fit
