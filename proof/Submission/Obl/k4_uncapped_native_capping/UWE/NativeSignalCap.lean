/-
Adapted from this LOT tree o198, session x0693, commit b5c1b640df5e526ffc014739d6614359923ec044,
Submission/Obl/k4_balanced_native_packet_transport/UWE/NativeSignalCap.lean. Existing source attributions below are retained.
-/
/-
Adapted from this LOT tree, o120, session x0649, commit 99e461c8faeab846d12253887b2a587a38b5aa0e,
Submission/Obl/k4_unbounded_width_exclusion/NativeSignalCap.lean (namespace Submission.Obl.k4_unbounded_width_exclusion renamed to
Submission.Obl.k4_uncapped_native_capping.UWE).
-/
import Submission.Obl.k4_uncapped_native_capping.UWE.Problems
import Submission.Obl.k4_uncapped_native_capping.UWE.NativeBaseCeiling

noncomputable section

namespace Submission.Obl.k4_uncapped_native_capping.UWE

open MeasureTheory Set

/-- An observable envelope for a native signal band. -/
def nativeSignalCrossing (κ B a : ℝ) (P : MvPolynomial (Fin 4) ℝ) (b : ℝ) : Set Observation :=
  Submission.Obl.k4_coarsened_outer_horizon_composition.crossing
    κ 0 1 (a / B) B 0 0 (1 : Matrix (Fin 2) (Fin 2) ℝ) (P - MvPolynomial.C b)

theorem measurableSet_nativeSignalCrossing (κ B a : ℝ) (P : MvPolynomial (Fin 4) ℝ) (b : ℝ) :
    MeasurableSet (nativeSignalCrossing κ B a P b) :=
  Submission.Obl.k4_coarsened_outer_horizon_composition.measurableSet_crossing _ _ _ _ _ _ _ _ _

theorem nativeSignalCrossing_count {κ B a : ℝ} (hκ : 1 ≤ κ) (hB : 0 < B) (ha : 0 < a)
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) (b : ℝ)
    (z : EuclideanSpace ℝ (Fin 3)) :
    Measure.count {j : ℤ | (z, j) ∈ nativeSignalCrossing κ B a P b} ≤
      ENNReal.ofReal (64 * κ ^ 2) := by
  let R := P - MvPolynomial.C b
  have hR : R.totalDegree ≤ 2 := (MvPolynomial.totalDegree_sub_C_le P b).trans hP
  let p := Submission.Obl.k4_coarsened_outer_horizon_composition.hiddenPolynomial R z
  have hp := Submission.Obl.k4_coarsened_outer_horizon_composition.hiddenPolynomial_degree R z hR
  have hbins := Submission.Obl.k4_coarsened_outer_horizon_composition.binTest_count p hp hκ
    (div_pos ha hB) hB
  apply (measure_mono (show {j : ℤ | (z, j) ∈ nativeSignalCrossing κ B a P b} ⊆
      {j : ℤ | Submission.Obl.k4_coarsened_outer_horizon_composition.binTest p κ (a / B) B j}
    from fun _ hj => hj.2)).trans
  rw [Measure.count_apply_finite _ hbins.1, ← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  simpa only [Set.ncard_eq_toFinset_card _ hbins.1] using hbins.2

theorem obs_mem_nativeSignalCrossing {κ B a : ℝ} (hκ : 1 ≤ κ) (hB : 0 < B) (ha : 0 < a)
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) (b : ℝ) (p : Incidence)
    (ht : p.2 ∈ Icc (0 : ℝ) 1) (hy : ‖y p.1 p.2‖ ≤ κ)
    (hv : |MvPolynomial.eval (x p.1 p.2) P - b| ≤ κ * a)
    (hd : |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) P)| ≤ κ * B)
    (hdd : |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4)
      (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ κ * B ^ 2 / a)
    (hf : B / κ ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) P)|) :
    obs B a p ∈ nativeSignalCrossing κ B a P b := by
  let R := P - MvPolynomial.C b
  have hR : R.totalDegree ≤ 2 := (MvPolynomial.totalDegree_sub_C_le P b).trans hP
  have hdR : MvPolynomial.pderiv (3 : Fin 4) R = MvPolynomial.pderiv (3 : Fin 4) P := by simp [R]
  apply Submission.Obl.k4_coarsened_outer_horizon_composition.obs_mem_crossing
    (by linarith only [hκ] : 0 < κ) ha hB 0 0 (1 : Matrix (Fin 2) (Fin 2) ℝ) R hR p ht
  · simpa [Submission.Obl.k4_coarsened_outer_horizon_composition.y,
      Submission.Obl.k4_coarsened_outer_horizon_composition.x, y, x] using hy
  · simpa [Submission.Obl.k4_coarsened_outer_horizon_composition.x, x, R] using hv
  · simpa only [hdR, Submission.Obl.k4_coarsened_outer_horizon_composition.x, x] using hd
  · simpa only [hdR, Submission.Obl.k4_coarsened_outer_horizon_composition.x, x] using hdd
  · simpa only [hdR, Submission.Obl.k4_coarsened_outer_horizon_composition.x, x] using hf

/-- A native signal band at the hidden observation scale meets only a
quadratic number of hidden bins over each exact base. The band center may be
arbitrarily large; all density bounds refer to the original law. -/
theorem native_signal_band_base_cap
    (μ ρ : Measure Incidence) (hρ : ρ ≤ μ)
    {κ B a : ℝ} (hκ : 1 ≤ κ) (hB : 0 < B) (ha : 0 < a)
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) (b : ℝ)
    (g : Observation → ENNReal) (hg : Measurable g)
    (hlaw : μ.map (obs B a) = (volume.prod Measure.count).withDensity g) (M : ENNReal)
    (hgood : ∀ᵐ p ∂ρ, p.2 ∈ Icc (0 : ℝ) 1 ∧ ‖y p.1 p.2‖ ≤ κ ∧
      |MvPolynomial.eval (x p.1 p.2) P - b| ≤ κ * a ∧
      |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) P)| ≤ κ * B ∧
      |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4)
        (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ κ * B ^ 2 / a ∧
      B / κ ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) P)| ∧
      g (obs B a p) ≤ M) :
    ρ.map (fun p => (obs B a p).1) ≤ (M * ENNReal.ofReal (64 * κ ^ 2)) • volume := by
  apply base_ceiling_of_counted_observation μ ρ hρ volume (obs B a) (by unfold obs x; fun_prop)
    g hg hlaw (nativeSignalCrossing κ B a P b) (measurableSet_nativeSignalCrossing _ _ _ _ _)
    M (ENNReal.ofReal (64 * κ ^ 2)) (nativeSignalCrossing_count hκ hB ha P hP b)
  filter_upwards [hgood] with p hp
  obtain ⟨ht, hy, hv, hd, hdd, hf, hgm⟩ := hp
  exact ⟨obs_mem_nativeSignalCrossing hκ hB ha P hP b p ht hy hv hd hdd hf, hgm⟩

end Submission.Obl.k4_uncapped_native_capping.UWE
