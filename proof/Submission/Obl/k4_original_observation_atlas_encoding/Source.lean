import Submission.Obl.k4_horizon_light_cell_mass.Source
import Submission.Lib.K4XInterface.Charts
import Submission.Lib.K4XInterface.Formats

namespace Submission.Obl.k4_original_observation_atlas_encoding

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4XInterface
open Submission.Obl.k4_horizon_light_cell_mass
open Submission.Obl.k4_native_base_flattening (NativeMixtureFormat eventFiber)

def PriorFormat (N : ℝ) (M D : ℕ) (ν : Measure (ℕ × (Fin 6 → ℝ))) : Prop :=
  ∃ n : ℕ, (n : ℝ) ≤ N ^ M ∧ ∃ (c : Fin n → ℝ) (copy : Fin n → ℕ)
    (S : Fin n → Set (Fin 6 → ℝ)),
    (∀ a, 0 ≤ c a ∧ c a ≤ N ^ M ∧ (copy a : ℝ) ≤ N ^ M ∧
      gfmt 6 (N ^ M) D (S a) ∧ ∀ z ∈ S a, ∀ e, |z e| ≤ N ^ M) ∧
    ν = ∑ a, ENNReal.ofReal (c a) •
      Measure.map (fun z => (copy a, z)) (volume.restrict (S a))

def temperedLaw (N : ℝ) (M D W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))) (B : Fin W → ℝ) : Prop :=
  (W : ℝ) ≤ N ^ M ∧ (∀ w, 0 ≤ ω w) ∧ (∑ w, ω w) = 1 ∧
    ∀ w, IsProbabilityMeasure (ν w) ∧ 0 < B w ∧ B w ≤ N ^ M ∧
      (B w)⁻¹ ≤ N ^ M ∧ PriorFormat N M D (ν w)

theorem PriorFormat.mono {N : ℝ} {M M' D D' : ℕ}
    {ν : Measure (ℕ × (Fin 6 → ℝ))} (hN : 1 ≤ N) (hM : M ≤ M') (hD : D ≤ D')
    (h : PriorFormat N M D ν) : PriorFormat N M' D' ν := by
  have hpow : N ^ M ≤ N ^ M' := pow_le_pow_right₀ hN hM
  obtain ⟨n, hn, c, copy, S, hj, hν⟩ := h
  refine ⟨n, hn.trans hpow, c, copy, S, fun a => ?_, hν⟩
  obtain ⟨hc0, hc, hi, hf, hs⟩ := hj a
  exact ⟨hc0, hc.trans hpow, hi.trans hpow, gfmt_mono hpow hD hf,
    fun z hz e => (hs z hz e).trans hpow⟩

theorem chart_time_subset {N κ r B : ℝ} {M D T : ℕ} (j : Fin (2 ^ T))
    {E : Set State} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ}
    {A : Set (ℕ × (Fin 6 → ℝ))} {F : Set State} {ex : Prop}
    (h : gchart N M D κ T (j : ℝ) r B E c u Q R A F ex) :
    F ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hF, _⟩ := h
  intro p hp
  have ht := (hF p hp).2.2.1
  have h2 : (0 : ℝ) < 2 ^ T := by positivity
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hj1 : (j : ℝ) + 1 ≤ (2 : ℝ) ^ T := by
    have hh : j.val + 1 ≤ 2 ^ T := j.isLt
    exact_mod_cast hh
  exact ⟨mem_univ _, (div_nonneg hj0 h2.le).trans ht.1,
    ht.2.trans ((div_le_one h2).mpr hj1)⟩

/-- Every supplied chart has an exact formatted density under its original prior. -/
theorem source_of_chart {N κ r B : ℝ} {Mν Dν M D T : ℕ} (hN : 2 ≤ N)
    (ν : Measure (ℕ × (Fin 6 → ℝ))) (hν : PriorFormat N Mν Dν ν)
    (j : Fin (2 ^ T)) {E : Set State} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ}
    {A : Set (ℕ × (Fin 6 → ℝ))} {F : Set State} {ex : Prop}
    (h : gchart N M D κ T (j : ℝ) r B E c u Q R A F ex) :
    ∃ f : Raw → ℝ, NativeMixtureFormat N (max Mν M) (max Dν D) f ∧
      Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, |f x| ≤ N ^ (2 * max Mν M)) ∧
      ((ν.prod volume).restrict F).map rawChart =
        volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  have hN1 : 1 ≤ N := by linarith
  have hν' : PriorFormat N (max Mν M) (max Dν D) ν :=
    hν.mono hN1 (le_max_left _ _) (le_max_left _ _)
  have htime := chart_time_subset j h
  obtain ⟨_, _, _, _, _, _, _, hF, hfmt, _⟩ := h
  apply exists_formatted_source N (max Mν M) (max Dν D) hN ν F hν' hF htime
  intro i
  exact gfmt_mono (pow_le_pow_right₀ hN1 (le_max_right _ _)) (le_max_right _ _) (hfmt i).2

theorem observation_mass (μ : Measure State) (F : Set State)
    (B a : ℝ) (f : Raw → ℝ≥0∞) (hf : Measurable f)
    (hraw : (μ.restrict F).map rawChart = volume.withDensity f)
    (S : Set Observation) (hS : MeasurableSet S) :
    μ {p | p ∈ F ∧ pureMap B a p ∈ S} =
      ∫⁻ z, S.indicator (pureMarginal B a f) z ∂reference := by
  have hmap : (μ.restrict F).map (pureMap B a) =
      reference.withDensity (pureMarginal B a f) := by
    rw [pureMap_eq, ← Measure.map_map (rawObserve_measurable B a) rawChart_measurable,
      hraw, map_rawObserve_withDensity B a hf]
  have hh := congrArg (fun ν : Measure Observation => ν S) hmap
  rw [Measure.map_apply (pureMap_measurable B a) hS,
    Measure.restrict_apply ((pureMap_measurable B a) hS), withDensity_apply _ hS] at hh
  rw [lintegral_indicator hS]
  convert hh using 1
  congr 1
  ext p
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
  exact and_comm

theorem chart_coeff_bound {N κ r B j : ℝ} {M D T : ℕ}
    {E : Set State} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ}
    {A : Set (ℕ × (Fin 6 → ℝ))} {F : Set State} {ex : Prop}
    (h : gchart N M D κ T j r B E c u Q R A F ex) :
    ∀ p ∈ F, ∀ e, |p.1.2 e| ≤ N ^ M := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hA, hF, _⟩ := h
  intro p hp e
  exact (hA p.1 (hF p hp).2.1).2.1 e

end Submission.Obl.k4_original_observation_atlas_encoding
