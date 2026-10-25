import Submission.Obl.k4_scalar_guarded_tangent_preparation.DensityCaps
import Submission.Obl.k4_row_cell_regularization.Palette

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open MeasureTheory Set
open scoped ENNReal

abbrev scalarCell := Submission.Obl.k4_row_cell_regularization.velocityCell

/-- The original half-open square associated to a pair of floor bins. -/
def baseCell (a : ℝ) (q : Fin 2 → ℤ) : Set (Fin 2 → ℝ) :=
  Set.univ.pi fun i => scalarCell a (q i)

theorem measurableSet_baseCell (a : ℝ) (q : Fin 2 → ℤ) :
    MeasurableSet (baseCell a q) := by
  exact MeasurableSet.univ_pi fun i => measurableSet_Ico

theorem baseCell_eq_floor {a : ℝ} (ha : 0 < a) (q : Fin 2 → ℤ) :
    baseCell a q = {z | (fun i => (⌊z i / a⌋ : ℤ)) = q} := by
  ext z
  simp only [baseCell, Set.mem_univ_pi,
    Submission.Obl.k4_row_cell_regularization.velocityCell_eq_floor ha,
    Set.mem_ofPred_eq, funext_iff]

theorem volume_baseCell (a : ℝ) (q : Fin 2 → ℤ) :
    volume (baseCell a q) = ENNReal.ofReal a ^ 2 := by
  change volume (Set.univ.pi fun i => Ico ((q i : ℝ) * a) (((q i : ℝ) + 1) * a)) = _
  rw [Real.volume_pi_Ico]
  have hwidth (i : Fin 2) : ((q i : ℝ) + 1) * a - (q i : ℝ) * a = a := by ring
  simp_rw [hwidth]
  simp [pow_two]

/-- The pure observation reference assigns area `a²` to every base square
and mass one to its original hidden-bin tag. -/
theorem pure_reference_cell (a : ℝ) (q : Fin 2 → ℤ) (c : ℤ) :
    ((volume : Measure (Fin 2 → ℝ)).prod Measure.count)
      (baseCell a q ×ˢ {c}) = ENNReal.ofReal a ^ 2 := by
  rw [Measure.prod_prod, volume_baseCell, Measure.count_singleton, mul_one]

/-- Rectangular pure caps follow from the observation ceiling, with no
renormalization of either the incidence law or its prior. -/
theorem pure_cell_le
    {Ω : Type*} [MeasurableSpace Ω] {ρ : Measure Ω}
    (Y : Ω → Fin 2 → ℝ) (X : Ω → ℝ)
    (hY : Measurable Y) (hX : Measurable X)
    {a b : ℝ} (ha : 0 < a) {C : ℝ≥0∞}
    (hcap : ρ.map (fun z => (Y z, (⌊X z / b⌋ : ℤ))) ≤
      C • ((volume : Measure (Fin 2 → ℝ)).prod Measure.count))
    (q : Fin 2 → ℤ) (c : ℤ) :
    ρ {z | (fun i => (⌊Y z i / a⌋ : ℤ)) = q ∧ (⌊X z / b⌋ : ℤ) = c} ≤
      C * ENNReal.ofReal a ^ 2 := by
  have hQ : Measurable (fun z => (Y z, (⌊X z / b⌋ : ℤ))) :=
    hY.prodMk (hX.div_const b).floor
  have hB : MeasurableSet (baseCell a q ×ˢ ({c} : Set ℤ)) :=
    (measurableSet_baseCell a q).prod (measurableSet_singleton c)
  have h := observation_cell_le hQ hcap hB
  rw [pure_reference_cell, baseCell_eq_floor ha] at h
  exact h

/-- The joint reference retains the palette fixed before the incidence
restriction; a velocity-bin tag has its original palette mass. -/
theorem joint_reference_cell (π : Measure ℝ) [IsFiniteMeasure π] (a b : ℝ)
    (q : Fin 2 → ℤ) (c e : ℤ) :
    ((((volume : Measure (Fin 2 → ℝ)).prod Measure.count).prod
      (π.map (fun v => (⌊v / b⌋ : ℤ)))))
        ((baseCell a q ×ˢ {c}) ×ˢ {e}) =
      ENNReal.ofReal a ^ 2 * π {v | (⌊v / b⌋ : ℤ) = e} := by
  have hV : Measurable (fun v : ℝ => (⌊v / b⌋ : ℤ)) :=
    (measurable_id.div_const b).floor
  rw [Measure.prod_prod, pure_reference_cell, Measure.map_apply hV (measurableSet_singleton e)]
  rfl

/-- A joint ceiling gives the literal pure-state times original-palette
bound for each rectangular base, hidden and velocity cell. -/
theorem joint_cell_le
    {Ω : Type*} [MeasurableSpace Ω] {ρ : Measure Ω}
    (π : Measure ℝ) [IsFiniteMeasure π]
    (Y : Ω → Fin 2 → ℝ) (X V : Ω → ℝ)
    (hY : Measurable Y) (hX : Measurable X) (hV : Measurable V)
    {a b e : ℝ} (ha : 0 < a) {C : ℝ≥0∞}
    (hcap : ρ.map (fun z => ((Y z, (⌊X z / b⌋ : ℤ)), (⌊V z / e⌋ : ℤ))) ≤
      C • (((volume : Measure (Fin 2 → ℝ)).prod Measure.count).prod
        (π.map (fun v => (⌊v / e⌋ : ℤ)))))
    (q : Fin 2 → ℤ) (c d : ℤ) :
    ρ {z | (fun i => (⌊Y z i / a⌋ : ℤ)) = q ∧ (⌊X z / b⌋ : ℤ) = c ∧
      (⌊V z / e⌋ : ℤ) = d} ≤
      (C * ENNReal.ofReal a ^ 2) * π {v | (⌊v / e⌋ : ℤ) = d} := by
  have hQ : Measurable (fun z => ((Y z, (⌊X z / b⌋ : ℤ)), (⌊V z / e⌋ : ℤ))) :=
    (hY.prodMk (hX.div_const b).floor).prodMk (hV.div_const e).floor
  have hB : MeasurableSet ((baseCell a q ×ˢ ({c} : Set ℤ)) ×ˢ ({d} : Set ℤ)) :=
    ((measurableSet_baseCell a q).prod (measurableSet_singleton c)).prod
      (measurableSet_singleton d)
  have h := observation_cell_le hQ hcap hB
  rw [joint_reference_cell, baseCell_eq_floor ha, ← mul_assoc] at h
  simpa only [Set.preimage, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_singleton_iff,
    and_assoc] using h

/-- Multiplying a pure density at depth `s` by a base-cell area at depth
`r` gives exactly the STI exponent. -/
theorem pure_cell_rpow {N : ℝ} (hN : 0 < N) (K d r s : ℝ) (hK : 0 ≤ K) :
    ENNReal.ofReal (K * N ^ (-d * s)) * ENNReal.ofReal (N ^ (-r)) ^ 2 =
      ENNReal.ofReal (K * N ^ (-2 * r - d * s)) := by
  rw [← ENNReal.ofReal_pow (Real.rpow_nonneg hN.le _),
    ← ENNReal.ofReal_mul (mul_nonneg hK (Real.rpow_nonneg hN.le _))]
  congr 1
  rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_add hN]
  congr 2
  ring

end Submission.Obl.k4_scalar_guarded_tangent_preparation
