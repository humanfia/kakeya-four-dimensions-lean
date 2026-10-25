/-
Adapted from this LOT tree, o120, session x0649, commit 99e461c8faeab846d12253887b2a587a38b5aa0e,
Submission/Obl/k4_unbounded_width_exclusion/NonparallelMass.lean (namespace Submission.Obl.k4_unbounded_width_exclusion renamed to
Submission.Obl.k4_balanced_native_packet_transport.UWE).
-/
import Submission.Obl.k4_balanced_native_packet_transport.UWE.Problems
import Submission.Obl.k4_balanced_native_packet_transport.UWE.AngularListMass
import Submission.Obl.k4_balanced_native_packet_transport.UWE.AngularPairBins
import Submission.Obl.k4_balanced_native_packet_transport.UWE.StripWindow
import Submission.Lib.K4Homogenization.DyadicObservations

noncomputable section

namespace Submission.Obl.k4_balanced_native_packet_transport.UWE

open MeasureTheory Set

def nativeAngularBin (w : ℝ) (p : Incidence) : Fin 2 → ℤ :=
  fun j => ⌊v p.1 j / w⌋

theorem measurable_nativeAngularBin (w : ℝ) : Measurable (nativeAngularBin w) := by
  unfold nativeAngularBin v
  fun_prop

/-- The three observation laws used in the original-law angular estimate.
They all belong to the same unnormalized original incidence measure. -/
structure NativeAngularSample (μ : Measure Incidence) (N L B w : ℝ) where
  terminalDensity : Observation → ENNReal
  zeroDensity : Observation → ENNReal
  jointDensity : Observation × (Fin 2 → ℤ) → ENNReal
  measurable_terminal : Measurable terminalDensity
  measurable_zero : Measurable zeroDensity
  measurable_joint : Measurable jointDensity
  terminal_law : μ.map (obs B (δ N L)) =
    (volume.prod Measure.count).withDensity terminalDensity
  zero_law : μ.map (obs B 1) = (volume.prod Measure.count).withDensity zeroDensity
  joint_law : μ.map (fun p => (obs B (δ N L) p, nativeAngularBin w p)) =
    ((volume.prod Measure.count).prod Measure.count).withDensity jointDensity

/-- The bad second occurrences for one fixed first chart have small original
mass. The short angular list is charged through the coarse native law and the
actual extrapolated strip window, before any first-label sum. -/
theorem nonparallel_native_mass_le
    {μ ρ : Measure Incidence} (hρ : ρ ≤ μ)
    {N L B w κ K g H : ℝ} (hN : 1 ≤ N) (hL : 0 ≤ L)
    (hB : 0 < B) (hw : 0 < w) (hκ : 1 ≤ κ) (hK : 0 ≤ K)
    (hg : 0 < g) (hH : 0 < H) (hscale : 16 * K ≤ H * w)
    (data : NativeAngularSample μ N L B w)
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (n : EuclideanSpace ℝ (Fin 2)) (hn : ‖n‖ = 1) (a b : ℝ)
    {C : ℕ} (normal : Fin C → EuclideanSpace ℝ (Fin 2)) (speed : Fin C → ℝ)
    (hnormal : ∀ i, ‖normal i‖ = 1) (tag : Incidence → Fin C)
    (lst : Observation → Finset (Fin C))
    (hlst : ∀ i, MeasurableSet {o | i ∈ lst o}) (Λ c M : ENNReal)
    (hcard : ∀ o, ((lst o).card : ENNReal) ≤ Λ)
    (hgood : ∀ᵐ p ∂ρ,
      (obs B 1 p).1 ∈ originalStripWindow n a b K g ∧
      obs B 1 p ∈ Submission.Obl.k4_coarsened_outer_horizon_composition.crossing
        κ 0 1 (1 / B) B 0 0 (1 : Matrix (Fin 2) (Fin 2) ℝ) P ∧
      data.zeroDensity (obs B 1 p) ≤ M ∧
      tag p ∈ lst (obs B (δ N L) p) ∧
      g * H < min ‖n - normal (tag p)‖ ‖n + normal (tag p)‖ ∧
      |inner ℝ n (v p.1) - b| ≤ K * g ∧
      |inner ℝ (normal (tag p)) (v p.1) - speed (tag p)| ≤ K * g ∧
      data.jointDensity (obs B (δ N L) p, nativeAngularBin w p) ≤
        c * data.terminalDensity (obs B (δ N L) p)) :
    ρ univ ≤ c * (Λ * 16) * M * ENNReal.ofReal (64 * κ ^ 2) *
      ENNReal.ofReal (4 * K ^ 2 * g) := by
  classical
  have hV (i : Fin C) : ∃ V : Finset (Fin 2 → ℤ), V.card ≤ 16 ∧
      (g * H < min ‖n - normal i‖ ‖n + normal i‖ →
        ∀ u : EuclideanSpace ℝ (Fin 2), |inner ℝ n u - b| ≤ K * g →
        |inner ℝ (normal i) u - speed i| ≤ K * g → (fun j => ⌊u j / w⌋) ∈ V) := by
    by_cases hi : g * H < min ‖n - normal i‖ ‖n + normal i‖
    · obtain ⟨V, hV, hmem⟩ := nonparallel_velocity_bins hn (hnormal i) hK hg hH hw hi hscale
      exact ⟨V, by exact_mod_cast hV, fun _ => hmem⟩
    · exact ⟨∅, by simp, fun h => (hi h).elim⟩
  choose V hVcard hVmem using hV
  let W : Observation → Finset (Fin 2 → ℤ) := fun o => (lst o).biUnion V
  have hW (j : Fin 2 → ℤ) : MeasurableSet {o | j ∈ W o} := by
    have heq : {o | j ∈ W o} = ⋃ i : Fin C, {o | i ∈ lst o} ∩ {o | j ∈ V i} := by
      ext o
      simp [W]
    rw [heq]
    apply MeasurableSet.iUnion
    intro i
    apply (hlst i).inter
    by_cases hi : j ∈ V i <;> simp [hi]
  have hWcard (o : Observation) : ((W o).card : ENNReal) ≤ Λ * 16 := by
    calc
      _ ≤ ((∑ i ∈ lst o, (V i).card : ℕ) : ENNReal) := by
        exact_mod_cast Finset.card_biUnion_le
      _ = ∑ i ∈ lst o, ((V i).card : ENNReal) := by simp only [Nat.cast_sum]
      _ ≤ ∑ _i ∈ lst o, (16 : ENNReal) := Finset.sum_le_sum (fun i _ => by exact_mod_cast hVcard i)
      _ = ((lst o).card : ENNReal) * 16 := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Λ * 16 := by gcongr; exact hcard o
  let q : Observation → Observation := Submission.Lib.K4Homogenization.coarsenObservation N 0 L
  have hq : Measurable q := Submission.Lib.K4Homogenization.measurable_coarsenObservation N 0 L
  have hfac (p : Incidence) : q (obs B (δ N L) p) = obs B 1 p := by
    apply Prod.ext
    · rfl
    · have h := Submission.Lib.K4Homogenization.observation_bin_coarsen hN hL
        (B * x p.1 p.2 3)
      simpa [q, obs, δ, Submission.Lib.K4Homogenization.coarsenObservation,
        Submission.Lib.K4Homogenization.observationWidth,
        Submission.Lib.K4Homogenization.observationDepth] using h.symm
  have hcoarse : μ.map (q ∘ obs B (δ N L)) =
      (volume.prod Measure.count).withDensity data.zeroDensity := by
    have heq : q ∘ obs B (δ N L) = obs B 1 := funext hfac
    rw [heq]
    exact data.zero_law
  have hmass : ρ univ ≤ c * (Λ * 16) * M * ENNReal.ofReal (64 * κ ^ 2) *
      volume (originalStripWindow n a b K g) := by
    apply angular_list_coarse_window_mass_le μ ρ hρ (volume.prod Measure.count)
      (obs B (δ N L)) (by unfold obs x; fun_prop)
      (nativeAngularBin w) (measurable_nativeAngularBin w)
      data.terminalDensity data.measurable_terminal data.jointDensity data.measurable_joint
      data.terminal_law data.joint_law volume q hq data.zeroDensity data.measurable_zero hcoarse
      (Submission.Obl.k4_coarsened_outer_horizon_composition.crossing
        κ 0 1 (1 / B) B 0 0 (1 : Matrix (Fin 2) (Fin 2) ℝ) P)
      (Submission.Obl.k4_coarsened_outer_horizon_composition.measurableSet_crossing _ _ _ _ _ _ _ _ _)
      (originalStripWindow n a b K g) (measurableSet_originalStripWindow n a b K g)
      c (Λ * 16) M (ENNReal.ofReal (64 * κ ^ 2))
      (native_crossing_fiber_count hκ hB P hP) W hW hWcard
    filter_upwards [hgood] with p hp
    rw [hfac]
    refine ⟨hp.1, hp.2.1, hp.2.2.1, ?_, hp.2.2.2.2.2.2.2⟩
    exact Finset.mem_biUnion.mpr ⟨tag p, hp.2.2.2.1,
      hVmem (tag p) hp.2.2.2.2.1 (v p.1) hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.1⟩
  exact hmass.trans (by gcongr; exact volume_originalStripWindow n hn a b hK hg.le)

end Submission.Obl.k4_balanced_native_packet_transport.UWE
