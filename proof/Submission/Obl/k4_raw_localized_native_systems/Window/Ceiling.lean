/- Adapted from this LOT tree, o197, session x0690, Window/Ceiling.lean,
   branch snapshot f7206748; preserving original attributions below. -/
import Submission.Obl.k4_raw_localized_native_systems.Window.Normalize
import Submission.Obl.k4_scalar_angular_pair_agreement.CapIntegration
import Submission.Obl.k4_coarsened_outer_horizon_composition.Crossings

/-!
# Base ceilings from counted observation densities

A density cap on a counted observation law gives a base ceiling for every
unchanged submeasure whose observations lie, above each base point, in a set
of at most `C` labels.  Applied to the observation of a chart at its own depth,
the crossing set of the chart test allows at most `64 κ²` hidden bins above
each base point.

`base_ceiling_of_counted_observation` is adapted from this LOT tree, o120
(`k4_unbounded_width_exclusion`), session x0649, branch x0649, file
`Submission/Obl/k4_unbounded_width_exclusion/NativeBaseCeiling.lean` (that
session's own code); `chart_crossing_fiber_count` and
`chart_depth_base_ceiling` generalize its zero-depth native statement to an
arbitrary depth, frame and test.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- A cap on an original counted observation gives a base ceiling for any
unchanged submeasure supported on at most `C` observed labels per base point. -/
theorem base_ceiling_of_counted_observation {Ω X I : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (μ ρ : Measure Ω) (hρ : ρ ≤ μ) (ν : Measure X)
    (O : Ω → X × I) (hO : Measurable O)
    (g : X × I → ENNReal) (hg : Measurable g)
    (hlaw : μ.map O = (ν.prod Measure.count).withDensity g)
    (H : Set (X × I)) (hH : MeasurableSet H) (M C : ENNReal)
    (hcount : ∀ x, Measure.count {i : I | (x, i) ∈ H} ≤ C)
    (hgood : ∀ᵐ p ∂ρ, O p ∈ H ∧ g (O p) ≤ M) :
    ρ.map (fun p => (O p).1) ≤ (M * C) • ν := by
  apply Measure.le_iff.mpr
  intro E hE
  let U : Set (X × I) := (E ×ˢ univ) ∩ H
  have hU : MeasurableSet U := (hE.prod MeasurableSet.univ).inter hH
  have href : (ν.prod Measure.count) U ≤ C * ν E := by
    apply Submission.Obl.k4_scalar_angular_pair_agreement.prod_mass_le_fiber_bound
      ν Measure.count E U C hU
    · exact fun p hp => hp.1.1
    · intro x hx
      apply (measure_mono (show {i : I | (x, i) ∈ U} ⊆ {i : I | (x, i) ∈ H}
        from fun _ hp => hp.2)).trans (hcount x)
  change (ρ.map (Prod.fst ∘ O)) E ≤ ((M * C) • ν) E
  rw [Measure.map_apply (measurable_fst.comp hO) hE, Measure.smul_apply, smul_eq_mul]
  have heq : ρ ((Prod.fst ∘ O) ⁻¹' E) =
      ρ {p | O p ∈ U ∧ g (O p) ≤ M} := by
    apply measure_congr
    filter_upwards [hgood] with p hp
    simp only [mem_preimage, Function.comp_apply, U, mem_inter_iff, mem_prod, mem_univ,
      and_true, hp.1, hp.2, and_true]
  rw [heq]
  calc
    _ ≤ μ {p | O p ∈ U ∧ g (O p) ≤ M} := hρ _
    _ ≤ M * (C * ν E) :=
      Submission.Obl.k4_scalar_angular_pair_agreement.capped_observation_mass_le
        μ (ν.prod Measure.count) O hO g hg hlaw U hU M (C * ν E) href
    _ = _ := by ring

/-- A chart test of degree at most two allows at most `64 κ²` hidden bins of
width `a` above each base point. -/
theorem chart_crossing_fiber_count {κ a B t₀ t₁ : ℝ} (hκ : 1 ≤ κ) (ha : 0 < a) (hB : 0 < B)
    (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    (z : EuclideanSpace ℝ (Fin 3)) :
    Measure.count {j : ℤ | (z, j) ∈
      Submission.Obl.k4_coarsened_outer_horizon_composition.crossing
        κ t₀ t₁ (a / B) B c u Q R} ≤ ENNReal.ofReal (64 * κ ^ 2) := by
  let P := Submission.Obl.k4_coarsened_outer_horizon_composition.hiddenPolynomial R z
  have hP : P.natDegree ≤ 2 :=
    Submission.Obl.k4_coarsened_outer_horizon_composition.hiddenPolynomial_degree R z hR
  have hbins := Submission.Obl.k4_coarsened_outer_horizon_composition.binTest_count P hP hκ
    (div_pos ha hB) hB
  apply (measure_mono (show {j : ℤ | (z, j) ∈
      Submission.Obl.k4_coarsened_outer_horizon_composition.crossing
        κ t₀ t₁ (a / B) B c u Q R} ⊆
      {j : ℤ | Submission.Obl.k4_coarsened_outer_horizon_composition.binTest P κ (a / B) B j}
    from fun _ hj => hj.2)).trans
  rw [Measure.count_apply_finite _ hbins.1, ← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  simpa only [Set.ncard_eq_toFinset_card _ hbins.1] using hbins.2

/-- The base point `(t, y)` of an incidence: the first component of every observation. -/
def basePt (q : Point) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![q.2, x q.1 q.2 1, x q.1 q.2 2]

theorem obs_fst (B a : ℝ) (q : Point) : (obs B a q).1 = basePt q := rfl

theorem measurable_basePt : Measurable basePt := by
  unfold basePt x
  fun_prop

theorem measurable_obs' (B a : ℝ) : Measurable (obs B a) := by
  unfold obs x
  fun_prop

/-- The chart-depth base ceiling: an unchanged submeasure of a selected law whose
incidences satisfy the chart tests of one chart at depth width `a` and whose
observation density at that width is at most `M` has base law at most
`M · 64 κ²` times Lebesgue measure. -/
theorem chart_depth_base_ceiling
    (μ ρ : Measure Point) (hρ : ρ ≤ μ)
    {κ a B t₀ t₁ : ℝ} (hκ : 1 ≤ κ) (ha : 0 < a) (hB : 0 < B)
    (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    (g : (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal) (hg : Measurable g)
    (hlaw : μ.map (obs B a) = (volume.prod Measure.count).withDensity g)
    (M : ENNReal)
    (hgood : ∀ᵐ q ∂ρ, q.2 ∈ Icc t₀ t₁ ∧
      ‖Matrix.toEuclideanLin Q⁻¹ (y q.1 q.2 - c - q.2 • u)‖ ≤ κ ∧
      |MvPolynomial.eval (x q.1 q.2) R| ≤ κ * a ∧
      |MvPolynomial.eval (x q.1 q.2) (MvPolynomial.pderiv (3 : Fin 4) R)| ≤ κ * B ∧
      |MvPolynomial.eval (x q.1 q.2)
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) R))| ≤ κ * B ^ 2 / a ∧
      B / κ ≤ |MvPolynomial.eval (x q.1 q.2) (MvPolynomial.pderiv (3 : Fin 4) R)| ∧
      g (obs B a q) ≤ M) :
    ρ.map basePt ≤ (M * ENNReal.ofReal (64 * κ ^ 2)) • volume := by
  have hmap := base_ceiling_of_counted_observation μ ρ hρ volume (obs B a) (measurable_obs' B a)
    g hg hlaw
    (Submission.Obl.k4_coarsened_outer_horizon_composition.crossing κ t₀ t₁ (a / B) B c u Q R)
    (Submission.Obl.k4_coarsened_outer_horizon_composition.measurableSet_crossing _ _ _ _ _ _ _ _ _)
    M (ENNReal.ofReal (64 * κ ^ 2)) (chart_crossing_fiber_count hκ ha hB c u Q R hR)
    (by
      filter_upwards [hgood] with q hq
      obtain ⟨ht, hs, hv, hd, hc, hf, hgq⟩ := hq
      refine ⟨?_, hgq⟩
      have hκpos : 0 < κ := by linarith only [hκ]
      exact Submission.Obl.k4_coarsened_outer_horizon_composition.obs_mem_crossing
        hκpos ha hB c u Q R hR q ht hs hv hd hc hf)
  simpa only [obs_fst] using hmap

end
end Submission.Obl.k4_raw_localized_native_systems.Window
