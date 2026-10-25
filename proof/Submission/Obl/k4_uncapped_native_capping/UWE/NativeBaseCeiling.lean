/-
Adapted from this LOT tree o198, session x0693, commit b5c1b640df5e526ffc014739d6614359923ec044,
Submission/Obl/k4_balanced_native_packet_transport/UWE/NativeBaseCeiling.lean. Existing source attributions below are retained.
-/
/-
Adapted from this LOT tree, o120, session x0649, commit 99e461c8faeab846d12253887b2a587a38b5aa0e,
Submission/Obl/k4_unbounded_width_exclusion/NativeBaseCeiling.lean (namespace Submission.Obl.k4_unbounded_width_exclusion renamed to
Submission.Obl.k4_uncapped_native_capping.UWE).
-/
import Submission.Obl.k4_uncapped_native_capping.UWE.Interface
import Submission.Obl.k4_scalar_angular_pair_agreement.CapIntegration
import Submission.Obl.k4_coarsened_outer_horizon_composition.Crossings

noncomputable section

namespace Submission.Obl.k4_uncapped_native_capping.UWE

open MeasureTheory Set

/-- A cap on an original counted observation gives a base ceiling for any
unchanged submeasure supported on at most `C` observed labels per base point.
The density mask is imposed before the label count; there is no loss factor
from the number of charts. -/
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

/-- Native quadratic tests allow only a polynomial number of unit-depth
hidden labels at every exact base, without bounding the hidden coordinate. -/
theorem native_crossing_fiber_count {κ B : ℝ} (hκ : 1 ≤ κ) (hB : 0 < B)
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (z : EuclideanSpace ℝ (Fin 3)) :
    Measure.count {j : ℤ | (z, j) ∈
      Submission.Obl.k4_coarsened_outer_horizon_composition.crossing
        κ 0 1 (1 / B) B 0 0 (1 : Matrix (Fin 2) (Fin 2) ℝ) P} ≤
      ENNReal.ofReal (64 * κ ^ 2) := by
  let p := Submission.Obl.k4_coarsened_outer_horizon_composition.hiddenPolynomial P z
  have hp : p.natDegree ≤ 2 :=
    Submission.Obl.k4_coarsened_outer_horizon_composition.hiddenPolynomial_degree P z hP
  have hbins := Submission.Obl.k4_coarsened_outer_horizon_composition.binTest_count p hp hκ
    (by positivity : 0 < 1 / B) hB
  apply (measure_mono (show {j : ℤ | (z, j) ∈
      Submission.Obl.k4_coarsened_outer_horizon_composition.crossing
        κ 0 1 (1 / B) B 0 0 (1 : Matrix (Fin 2) (Fin 2) ℝ) P} ⊆
      {j : ℤ | Submission.Obl.k4_coarsened_outer_horizon_composition.binTest p κ (1 / B) B j}
    from fun _ hj => hj.2)).trans
  rw [Measure.count_apply_finite _ hbins.1, ← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  simpa only [Set.ncard_eq_toFinset_card _ hbins.1] using hbins.2

/-- The zero-depth native base cap, retaining the original measure and an
arbitrary original-law submeasure. The pure-density bound may come from an
analytical mask and need not be a geometric output predicate. -/
theorem native_zero_depth_base_ceiling
    (μ ρ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hρ : ρ ≤ μ)
    {κ B : ℝ} (hκ : 1 ≤ κ) (hB : 0 < B)
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (g : (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal) (hg : Measurable g)
    (hlaw : μ.map (obs B 1) = (volume.prod Measure.count).withDensity g)
    (M : ENNReal)
    (hgood : ∀ᵐ p ∂ρ, p.2 ∈ Icc (0 : ℝ) 1 ∧ ‖y p.1 p.2‖ ≤ κ ∧
      |MvPolynomial.eval (x p.1 p.2) P| ≤ κ ∧
      |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) P)| ≤ κ * B ∧
      |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) P))|
        ≤ κ * B ^ 2 ∧
      B / κ ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) P)| ∧
      g (obs B 1 p) ≤ M) :
    ρ.map (fun p => (obs B 1 p).1) ≤ (M * ENNReal.ofReal (64 * κ ^ 2)) • volume := by
  apply base_ceiling_of_counted_observation μ ρ hρ volume (obs B 1) (by unfold obs x; fun_prop)
    g hg hlaw
    (Submission.Obl.k4_coarsened_outer_horizon_composition.crossing
      κ 0 1 (1 / B) B 0 0 (1 : Matrix (Fin 2) (Fin 2) ℝ) P)
    (Submission.Obl.k4_coarsened_outer_horizon_composition.measurableSet_crossing _ _ _ _ _ _ _ _ _)
    M (ENNReal.ofReal (64 * κ ^ 2)) (native_crossing_fiber_count hκ hB P hP)
  filter_upwards [hgood] with p hp
  obtain ⟨ht, hy, hPval, hPd, hPdd, hPf, hgval⟩ := hp
  refine ⟨?_, hgval⟩
  have hκpos : 0 < κ := by linarith only [hκ]
  apply Submission.Obl.k4_coarsened_outer_horizon_composition.obs_mem_crossing
    hκpos (by norm_num : (0 : ℝ) < 1) hB 0 0 (1 : Matrix (Fin 2) (Fin 2) ℝ) P hP p ht
  · simpa [Submission.Obl.k4_coarsened_outer_horizon_composition.y,
      Submission.Obl.k4_coarsened_outer_horizon_composition.x, y, x] using hy
  · simpa only [Submission.Obl.k4_coarsened_outer_horizon_composition.x, x, mul_one] using hPval
  · exact hPd
  · simpa only [Submission.Obl.k4_coarsened_outer_horizon_composition.x, x, div_one] using hPdd
  · exact hPf

end Submission.Obl.k4_uncapped_native_capping.UWE
