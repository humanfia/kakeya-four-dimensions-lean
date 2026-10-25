import Mathlib
import ChallengeDeps
import Submission.Obl.k4_stable_native_signal_oscillation.PolynomialControl
import Submission.Obl.k4_stable_native_signal_oscillation.RootDerivative
import Submission.Obl.k4_stable_native_signal_oscillation.Transport
import Submission.Obl.k4_stable_native_signal_oscillation.WitnessVolume
import Submission.Obl.k4_stable_native_signal_oscillation.Partition

set_option linter.unusedVariables false

namespace Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Obl.k4_quadratic_atlas_normalization
open MvPolynomial MeasureTheory Set

lemma of_exact_root_partition (rootInput : ∀ A : ℕ, ∃ C : ℕ, 1 ≤ C ∧ ∀ (K : ℝ) (P S : MvPolynomial (Fin 4) ℝ) (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 4))), 2 ≤ K → P.totalDegree ≤ 2 → S.totalDegree ≤ 2 → MeasureTheory.IsProbabilityMeasure μ → (fun base : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 3) => MeasureTheory.Measure.map base μ ≤ ENNReal.ofReal K • MeasureTheory.volume → (∀ᵐ p ∂μ, ‖base p‖ ≤ K ∧ MvPolynomial.eval (fun i => p i) P = 0 ∧ K⁻¹ ≤ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3 : Fin 4) P)| ∧ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3 : Fin 4) P)| ≤ K ∧ |MvPolynomial.eval (fun i => p i) S| ≤ K) → ∃ (n : ℕ) (E : Fin n → Set (EuclideanSpace ℝ (Fin 4))), (n : ℝ) ≤ K ^ C ∧ (∀ i, MeasurableSet (E i)) ∧ (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧ μ (⋃ i, E i)ᶜ ≤ ENNReal.ofReal ((K ^ A)⁻¹) ∧ ∀ i p, p ∈ E i → ∀ q, q ∈ E i → |MvPolynomial.eval (fun j => p j) S - MvPolynomial.eval (fun j => q j) S| ≤ K ^ C * ‖base p - base q‖) (fun p => WithLp.toLp 2 ![p 0, p 1, p 2])) :  ((fun (V₀:Prop) => V₀) (∀ A:ℕ,∃ C:ℕ,1 ≤ C∧∀ (K a:ℝ) (P S:MvPolynomial (Fin 4) ℝ) (μ:MeasureTheory.Measure (EuclideanSpace ℝ (Fin 4))),2 ≤ K→ 0 < a→ a ≤ 1→ P.totalDegree ≤ 2→ S.totalDegree ≤ 2→ MeasureTheory.IsProbabilityMeasure μ→ (fun base:EuclideanSpace ℝ (Fin 4)→ EuclideanSpace ℝ (Fin 3) => MeasureTheory.Measure.map base μ ≤ ENNReal.ofReal K • MeasureTheory.volume→ (∀ᵐ p ∂μ,‖base p‖ ≤ K∧ |MvPolynomial.eval (fun i => p i) P| ≤ K * a∧K⁻¹ ≤ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3:Fin 4) P)|∧ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3:Fin 4) P)| ≤ K∧ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3:Fin 4) (MvPolynomial.pderiv (3:Fin 4) P))| ≤ K / a∧ |MvPolynomial.eval (fun i => p i) S| ≤ K∧ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3:Fin 4) S)| ≤ K∧ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3:Fin 4) (MvPolynomial.pderiv (3:Fin 4) S))| ≤ K)→ ∃ (n:ℕ) (E:Fin n→ Set (EuclideanSpace ℝ (Fin 4))),(n:ℝ) ≤ K ^ C∧(∀ i,MeasurableSet (E i))∧(∀ i j,i ≠ j→ Disjoint (E i) (E j))∧μ (⋃ i,E i)ᶜ ≤ ENNReal.ofReal ((K ^ A)⁻¹)∧∀ i p,p ∈ E i→ ∀ q,q ∈ E i→ |MvPolynomial.eval (fun j => p j) S - MvPolynomial.eval (fun j => q j) S| ≤ K ^ C * (a + ‖base p - base q‖)) (fun p => WithLp.toLp 2 ![p 0,p 1,p 2])))  := by
  intro A
  obtain ⟨Cp, hCp, hpoly⟩ := exists_center_polynomial_lipschitz
  obtain ⟨Cr, hCr, hroot⟩ := rootInput A
  let C := max 15 (max Cp (16 * Cr))
  have hC15 : 15 ≤ C := le_max_left _ _
  have hCpoly : Cp ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCroot : 16 * Cr ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, by omega, ?_⟩
  intro K a P S μ hK ha ha1 hP hS hprob hdensity hae
  haveI : IsProbabilityMeasure μ := hprob
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hgood : ∀ᵐ p ∂μ, p ∈ goodSet K a P S := by
    simpa only [goodSet, Set.mem_ofPred_eq, value, nativeBase, second_pderiv_eq_curvature P hP 3,
      second_pderiv_eq_curvature S hS 3, eval_C] using hae
  have hGm := measurableSet_goodSet K a P S
  by_cases hc : (K ^ 5 * a)⁻¹ ≤ |curvature P 3|
  · let F := centerSignal P S
    let T : Set BasePoint := {u | ‖u‖ ≤ K ∧ |baseValue F u| ≤ K ^ 15}
    have hTm : MeasurableSet T :=
      (measurableSet_le measurable_id.norm measurable_const).inter
        (measurableSet_le (continuous_baseValue F).abs.measurable measurable_const)
    have hTfull : ∀ᵐ p ∂μ, nativeBase p ∈ T := by
      filter_upwards [hgood] with p hp
      exact ⟨hp.1, signal_bound_from_error hK ha1
        (center_signal_error P S hP hS hK ha ha1 hc hp) hp.2.2.2.2.2.1⟩
    have hTvol := witness_volume μ hK0 hdensity T hTm hTfull
    have hFdeg : F.totalDegree ≤ 2 := (centerSignal_degree P S hP).trans hS
    have hLip := hpoly K hK F hFdeg T
      (fun u hu => mem_closedBall_zero_iff.mpr hu.1) hTvol (fun u hu => hu.2)
    refine ⟨1, (fun _ => goodSet K a P S), ?_, (fun _ => hGm), ?_, ?_, ?_⟩
    · simpa using one_le_pow₀ hK1 (n := C)
    · intro i j hij
      exact (hij (Subsingleton.elim i j)).elim
    · have hzero : μ (goodSet K a P S)ᶜ = 0 := ae_iff.mp hgood
      rw [Set.iUnion_const, hzero]
      exact bot_le
    · intro i p hp q hq
      have hep := center_signal_error P S hP hS hK ha ha1 hc hp
      have heq := center_signal_error P S hP hS hK ha ha1 hc hq
      rw [abs_sub_comm] at hep heq
      have hosc := signal_oscillation_of_graph nativeBase (value S) (baseValue F)
        hep heq (hLip (nativeBase p) (nativeBase q) hp.1 hq.1)
      exact hosc.trans (absorb_signal_error hK ha.le (norm_nonneg _) hCpoly hC15)
  · have hcsmall : |curvature P 3| ≤ (K ^ 5 * a)⁻¹ := le_of_lt (lt_of_not_ge hc)
    have hKL : K ≤ K ^ 16 := by
      simpa using pow_le_pow_right₀ hK1 (by decide : 1 ≤ 16)
    let ν := Measure.map (rootLift P) μ
    have hν : IsProbabilityMeasure ν := inferInstance
    have hνdensity : Measure.map nativeBase ν ≤ ENNReal.ofReal (K ^ 16) • volume :=
      base_density_rootLift μ P hKL hdensity
    have hνgood : ∀ᵐ p ∂ν, ‖nativeBase p‖ ≤ K ^ 16 ∧ value P p = 0 ∧
        (K ^ 16)⁻¹ ≤ |value (pderiv 3 P) p| ∧ |value (pderiv 3 P) p| ≤ K ^ 16 ∧ |value S p| ≤ K ^ 16 := by
      apply (ae_map_iff (measurable_rootLift P).aemeasurable ?_).mpr
      · filter_upwards [hgood] with p hp
        obtain ⟨hr, hsimple, he⟩ := rootLift_spec P S hP hS hK ha ha1 hcsmall p
          hp.2.1 hp.2.2.1 hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2
        obtain ⟨hdlo, hdhi⟩ := rootLift_derivative_bounds P hP hK ha hcsmall
          hp.2.2.2.2.1 p hp.2.1 hp.2.2.1 hp.2.2.2.1 hr
        have hlower : (K ^ 16)⁻¹ ≤ K⁻¹ / 2 := by
          have h2K : 2 * K ≤ K ^ 16 := by
            calc
              _ ≤ K * K := mul_le_mul_of_nonneg_right hK hK0.le
              _ = K ^ 2 := by ring
              _ ≤ K ^ 16 := pow_le_pow_right₀ hK1 (by decide : 2 ≤ 16)
          calc
            _ ≤ (2 * K)⁻¹ := inv_anti₀ (by positivity) h2K
            _ = K⁻¹ / 2 := by field_simp
        refine ⟨?_, hr, hlower.trans hdlo, hdhi.trans
          (pow_le_pow_right₀ hK1 (by decide : 2 ≤ 16)), ?_⟩
        · rw [nativeBase_rootLift]
          exact hp.1.trans hKL
        · exact (signal_bound_from_error hK ha1 he hp.2.2.2.2.2.1).trans
            (pow_le_pow_right₀ hK1 (by decide : 15 ≤ 16))
      · exact (measurableSet_le measurable_nativeBase.norm measurable_const).inter
          ((measurableSet_eq_fun (continuous_value P).measurable measurable_const).inter
          ((measurableSet_le measurable_const (continuous_value (pderiv 3 P)).abs.measurable).inter
          ((measurableSet_le (continuous_value (pderiv 3 P)).abs.measurable measurable_const).inter
            (measurableSet_le (continuous_value S).abs.measurable measurable_const))))
    obtain ⟨n, F, hnum, hFm, hFd, hmass, hFl⟩ :=
      hroot (K ^ 16) P S ν (hK.trans hKL) hP hS hν hνdensity hνgood
    obtain ⟨E, hEm, hEd, hEloss, hEosc⟩ := pullback_signal_partition μ (rootLift P)
      (measurable_rootLift P) (nativeBase_rootLift P) S (goodSet K a P S) hGm hgood
      (fun p hp => (rootLift_spec P S hP hS hK ha ha1 hcsmall p
        hp.2.1 hp.2.2.1 hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2).2.2)
      F hFm hFd hFl
    refine ⟨n, E, ?_, hEm, hEd, ?_, ?_⟩
    · rw [← pow_mul] at hnum
      exact hnum.trans (pow_le_pow_right₀ hK1 hCroot)
    · apply hEloss.trans (hmass.trans (ENNReal.ofReal_le_ofReal ?_))
      exact inv_anti₀ (pow_pos hK0 A) (pow_le_pow_left₀ hK0.le hKL A)
    · intro i p hp q hq
      have he := hEosc i p hp q hq
      rw [← pow_mul] at he
      exact he.trans (absorb_signal_error hK ha.le (norm_nonneg _) hCroot hC15)

end Submission.Obl.k4_stable_native_signal_oscillation
