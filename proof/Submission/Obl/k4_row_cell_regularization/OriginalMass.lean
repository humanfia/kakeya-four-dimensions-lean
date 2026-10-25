import Submission.Obl.k4_row_cell_regularization.ProjectionCover

open MeasureTheory Set
open scoped ENNReal BigOperators Classical

namespace Submission.Obl.k4_row_cell_regularization

variable {α : Type} [MeasurableSpace α]

/-- Original measurable point-cell witnesses, before choosing directions. -/
def originalCell (h E L : ℝ) (b v H : α → ℝ) (T : α × ℝ → Fin 2 → ℝ)
    (F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)) (p : Point) : Set (α × ℝ) :=
  {x | x ∈ goodSet h E L b v H T F ∧ incCell h E b v T x = p}

/-- The part of an original point cell on long trajectories in direction bin `d`. -/
def directionCell (h E L : ℝ) (b v H : α → ℝ) (T : α × ℝ → Fin 2 → ℝ)
    (F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)) (p : Point) (d : ℤ) : Set (α × ℝ) :=
  {x | x ∈ longGood h E L b v H T F ∧ incCell h E b v T x = p ∧ incBin h v x = d}

noncomputable def originalMass (μ : Measure (α × ℝ)) (h E L : ℝ) (b v H : α → ℝ)
    (T : α × ℝ → Fin 2 → ℝ) (F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ))
    (p : Point) (d : ℤ) : ℝ :=
  μ.real (directionCell h E L b v H T F p d)

/-- Palette mass of a half-open velocity bin. -/
noncomputable def binWeight (π : Measure ℝ) (h : ℝ) (d : ℤ) : ℝ :=
  π.real (Ico ((d : ℝ) * h) (((d : ℝ) + 1) * h))

variable {ν : Measure α} {μ : Measure (α × ℝ)} {b v H : α → ℝ}
    {T : α × ℝ → Fin 2 → ℝ} {π : Measure ℝ} {E : ℝ}
    {F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)} {h L S : ℝ}

theorem IncHyp.measurable_originalCell (hyp : IncHyp ν μ b v H T π E F h L S) (p : Point) :
    MeasurableSet (originalCell h E L b v H T F p) :=
  hyp.measurableSet_goodSet.inter
    (measurableSet_incCell_eq hyp.meas_b hyp.meas_v hyp.meas_T p)

theorem originalCell_disjoint :
    Pairwise (fun p q : Point => Disjoint (originalCell h E L b v H T F p)
      (originalCell h E L b v H T F q)) := by
  intro p q hpq
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hpq (hx.2.symm.trans hy.2)

theorem IncHyp.measurable_longGood (hyp : IncHyp ν μ b v H T π E F h L S) :
    MeasurableSet (longGood h E L b v H T F) :=
  measurableSet_longSet hyp.measurableSet_goodSet _

theorem IncHyp.measurable_directionCell (hyp : IncHyp ν μ b v H T π E F h L S)
    (p : Point) (d : ℤ) : MeasurableSet (directionCell h E L b v H T F p d) :=
  hyp.measurable_longGood.inter
    ((measurableSet_incCell_eq hyp.meas_b hyp.meas_v hyp.meas_T p).inter
      (measurableSet_incBin_eq hyp.meas_v d))

theorem originalMass_nonneg (p : Point) (d : ℤ) :
    0 ≤ originalMass μ h E L b v H T F p d := ENNReal.toReal_nonneg

/-- Every finite direction restriction is bounded by its original point-cell mass. -/
theorem IncHyp.originalCell_mass (hyp : IncHyp ν μ b v H T π E F h L S)
    (p : Point) (D : Finset ℤ) :
    ENNReal.ofReal (∑ d ∈ D, originalMass μ h E L b v H T F p d) ≤
      μ (originalCell h E L b v H T F p) := by
  have hd : PairwiseDisjoint (D : Set ℤ) (directionCell h E L b v H T F p) := by
    intro d _ d' _ hdd
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hdd (hx.2.2.symm.trans hy.2.2)
  have hs : (⋃ d ∈ D, directionCell h E L b v H T F p d) ⊆
      originalCell h E L b v H T F p := by
    intro x hx
    obtain ⟨d, hd, hx⟩ := mem_iUnion₂.mp hx
    exact ⟨hx.1.1, hx.2.1⟩
  have heq := measureReal_biUnion_finset hd
    (fun d _ => hyp.measurable_directionCell p d) (fun d _ => hyp.measure_ne_top _)
  have hr : (∑ d ∈ D, originalMass μ h E L b v H T F p d) ≤
      μ.real (originalCell h E L b v H T F p) := by
    simp only [originalMass]
    rw [← heq]
    exact measureReal_mono hs (hyp.measure_ne_top _)
  exact (ENNReal.ofReal_le_ofReal hr).trans_eq (ofReal_measureReal (hyp.measure_ne_top _))

/-- The finite original table has exactly the mass retained on long trajectories. -/
theorem IncHyp.originalMass_sum (hyp : IncHyp ν μ b v H T π E F h L S) :
    (∑ p ∈ incPoints h E L F, ∑ d ∈ incBins h L, originalMass μ h E L b v H T F p d) =
      μ.real (longGood h E L b v H T F) := by
  let B := incPoints h E L F ×ˢ incBins h L
  let A : (Point × ℤ) → Set (α × ℝ) := fun pd => directionCell h E L b v H T F pd.1 pd.2
  have hd : PairwiseDisjoint (B : Set (Point × ℤ)) A := by
    intro pd _ qd _ hpq
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hpq (Prod.ext (hx.2.1.symm.trans hy.2.1) (hx.2.2.symm.trans hy.2.2))
  have hu : (⋃ pd ∈ B, A pd) = longGood h E L b v H T F := by
    ext x
    constructor
    · intro hx
      obtain ⟨pd, _, hx⟩ := mem_iUnion₂.mp hx
      exact hx.1
    · intro hx
      apply mem_iUnion₂.mpr
      refine ⟨(incCell h E b v T x, incBin h v x), ?_, hx, rfl, rfl⟩
      exact Finset.mem_product.mpr
        ⟨incCell_mem_incPoints hyp.h_pos hyp.h_le_E hyp.traj_bound hx.1,
          incBin_mem_incBins hyp.h_pos hyp.traj_bound x⟩
  have hm := measureReal_biUnion_finset hd
    (fun pd _ => hyp.measurable_directionCell pd.1 pd.2) (fun pd _ => hyp.measure_ne_top _)
  rw [hu] at hm
  simpa only [B, A, Finset.sum_product, originalMass] using hm.symm

theorem IncHyp.originalMass_total (hyp : IncHyp ν μ b v H T π E F h L S) :
    1 / (2 * L) ≤ ∑ p ∈ incPoints h E L F,
      ∑ d ∈ incBins h L, originalMass μ h E L b v H T F p d := by
  rw [hyp.originalMass_sum]
  have hL : 0 < L := lt_of_lt_of_le one_pos hyp.one_le_L
  have hm := ENNReal.toReal_mono (hyp.measure_ne_top _) hyp.measure_longSet
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (2 * L)),
    Measure.real, longGood] using hm

/-- The original joint cap bounds every refined point/direction cell. -/
theorem IncHyp.originalMass_upper (hyp : IncHyp ν μ b v H T π E F h L S)
    (p : Point) (d : ℤ) :
    originalMass μ h E L b v H T F p d ≤ L * h ^ 2 * binWeight π h d := by
  have hπ := hyp.prob_π
  have hsub : directionCell h E L b v H T F p d ⊆
      {x | posCell h b v x = ![p 0, p 1] ∧ incBin h v x = d} := by
    intro x hx
    exact ⟨posCell_eq_of_incCell hx.2.1, hx.2.2⟩
  have hm := (measure_mono hsub).trans (hyp.joint_cap ![p 0, p 1] d)
  have hR : ENNReal.ofReal (L * h ^ 2) *
      π (Ico ((d : ℝ) * h) (((d : ℝ) + 1) * h)) ≠ ⊤ := by finiteness
  have hreal := ENNReal.toReal_mono hR hm
  have hL : 0 < L := lt_of_lt_of_le one_pos hyp.one_le_L
  simpa only [originalMass, binWeight, Measure.real, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ L * h ^ 2)] using hreal

/-- Positive table entries lie in the already frozen projection cover. -/
theorem originalMass_pos_occupied {p : Point} {d : ℤ}
    (hp : p ∈ incPoints h E L F) (hm : 0 < originalMass μ h E L b v H T F p d) :
    p ∈ occupiedCells h E L b v H T F d := by
  apply Finset.mem_filter.mpr
  refine ⟨hp, ?_⟩
  by_contra hx
  have he : directionCell h E L b v H T F p d = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hxm
    exact hx ⟨x, hxm.1, hxm.2⟩
  simp only [originalMass, he, measureReal_empty] at hm
  exact lt_irrefl 0 hm

/-- Original witnesses satisfy the point bounds and both mesh approximation statements. -/
theorem IncHyp.originalCell_bounds (hyp : IncHyp ν μ b v H T π E F h L S)
    {p : Point} {x : α × ℝ} (hx : x ∈ originalCell h E L b v H T F p) :
    |trajPos b v x 0| ≤ 1 ∧ |trajPos b v x 1| ≤ L ∧ ∀ j, |T x j| ≤ L := by
  refine ⟨?_, goodSet_pos hyp.traj_bound hx.1, goodSet_row hx.1⟩
  change |x.2| ≤ 1
  rw [abs_of_nonneg hx.1.1.1]
  exact hx.1.1.2

theorem IncHyp.originalCell_position (hyp : IncHyp ν μ b v H T π E F h L S)
    {p : Point} {x : α × ℝ} (hx : x ∈ originalCell h E L b v H T F p) (j : Fin 2) :
    |trajPos b v x j - h * ((![p 0, p 1] : Fin 2 → ℤ) j : ℝ)| ≤ h := by
  rw [← hx.2]
  fin_cases j
  · exact incCell_pos_error_zero (E := E) (b := b) (v := v) (T := T) hyp.h_pos x
  · exact incCell_pos_error_one (E := E) (b := b) (v := v) (T := T) hyp.h_pos x

theorem IncHyp.originalCell_row (hyp : IncHyp ν μ b v H T π E F h L S)
    {p : Point} {x : α × ℝ} (hx : x ∈ originalCell h E L b v H T F p) (j : Fin 2) :
    |(h / E) * T x j - h * ((![p 2, p 3] : Fin 2 → ℤ) j : ℝ)| ≤ h := by
  rw [← hx.2]
  fin_cases j
  · exact incCell_row_error hyp.h_pos hyp.h_le_E x 0
  · exact incCell_row_error hyp.h_pos hyp.h_le_E x 1

/-- The mass table inherits the original frozen projection cover. -/
theorem IncHyp.originalMass_projection_card (hyp : IncHyp ν μ b v H T π E F h L S)
    (d : ℤ) :
    ((((incPoints h E L F).filter (fun p => 0 < originalMass μ h E L b v H T F p d)).image
      (roundedProjection (binVel h d))).card : ℝ) ≤ 2 ^ 18 * L ^ 6 / h := by
  have hs : (incPoints h E L F).filter (fun p => 0 < originalMass μ h E L b v H T F p d) ⊆
      occupiedCells h E L b v H T F d := by
    intro p hp
    obtain ⟨hp, hm⟩ := Finset.mem_filter.mp hp
    exact originalMass_pos_occupied hp hm
  exact (Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image hs))).trans
    (hyp.occupied_projection_card d)

/-- The prescribed row palette controls every position fiber. -/
theorem IncHyp.position_fiber_card (hyp : IncHyp ν μ b v H T π E F h L S)
    (q : ℤ × ℤ) :
    (((incPoints h E L F).filter (fun p => (p 0, p 1) = q)).card : ℝ) ≤ L := by
  have hs : (incPoints h E L F).filter (fun p => (p 0, p 1) = q) ⊆
      (incPoints h E L F).filter (fun p => ![p 0, p 1] = ![q.1, q.2]) := by
    intro p hp
    obtain ⟨hp, hq⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨hp, ?_⟩
    exact congrArg (fun c : ℤ × ℤ => (![c.1, c.2] : Fin 2 → ℤ)) hq
  exact (Nat.cast_le.mpr ((Finset.card_le_card hs).trans (incPoints_fiber_card _))).trans
    (hyp.bins_card _)

end Submission.Obl.k4_row_cell_regularization
