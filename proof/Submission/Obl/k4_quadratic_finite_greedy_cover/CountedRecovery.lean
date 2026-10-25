-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/CountedRecovery.lean.

import Submission.Obl.k4_quadratic_finite_greedy_cover.FamilyLoss

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

open MeasureTheory Set
open scoped ENNReal

/-- Counted incidences use a half-open block and the relaxed hidden derivative floor. -/
def countedPacket (H : Set Incidence) (A : Set Trajectory)
    (R : MvPolynomial (Fin 4) ℝ) (b : ℝ) (T j : ℕ) : Set Incidence :=
  {p | p ∈ H ∧ p.1 ∈ A ∧ p.2 ∈ Ico ((j : ℝ) / (2 : ℝ) ^ T)
    (((j : ℝ) + 1) / (2 : ℝ) ^ T) ∧
    b ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)|}

def badPacket (A : Set Trajectory) (R : MvPolynomial (Fin 4) ℝ)
    (b : ℝ) (T j : ℕ) : Set Incidence :=
  {p | p.1 ∈ A ∧ p.2 ∈ Icc ((j : ℝ) / (2 : ℝ) ^ T)
    (((j : ℝ) + 1) / (2 : ℝ) ^ T) ∧
    |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)| < b}

theorem countedPacket_measurable
    (H : Set Incidence) (A : Set Trajectory) (hH : MeasurableSet H) (hA : MeasurableSet A)
    (R : MvPolynomial (Fin 4) ℝ) (b : ℝ) (T j : ℕ) :
    MeasurableSet (countedPacket H A R b T j) := by
  have hD : Continuous (fun p : Incidence =>
      |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)|) :=
    ((MvPolynomial.continuous_eval _).comp continuous_trajectory_point).abs
  have hd : MeasurableSet {p : Incidence | b ≤
      |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)|} :=
    measurableSet_le measurable_const hD.measurable
  have ht : MeasurableSet {p : Incidence | p.2 ∈ Ico ((j : ℝ) / (2 : ℝ) ^ T)
      (((j : ℝ) + 1) / (2 : ℝ) ^ T)} := measurableSet_Ico.preimage measurable_snd
  simpa only [countedPacket, Set.inter_def, Set.mem_ofPred_eq, Set.mem_preimage, and_assoc] using
    ((hH.inter (hA.preimage measurable_fst)).inter ht).inter hd

theorem badPacket_finite (ν : Measure Trajectory) [IsProbabilityMeasure ν]
    (A : Set Trajectory) (R : MvPolynomial (Fin 4) ℝ) (b : ℝ) (T j : ℕ) :
    ν.prod volume (badPacket A R b T j) ≠ ∞ := by
  have hsub : badPacket A R b T j ⊆ A ×ˢ Icc ((j : ℝ) / (2 : ℝ) ^ T)
      (((j : ℝ) + 1) / (2 : ℝ) ^ T) := fun p hp => ⟨hp.1, hp.2.1⟩
  have hf : ν.prod volume (A ×ˢ Icc ((j : ℝ) / (2 : ℝ) ^ T)
      (((j : ℝ) + 1) / (2 : ℝ) ^ T)) ≠ ∞ := by
    rw [Measure.prod_prod, Real.volume_Icc]
    finiteness
  exact measure_ne_top_of_subset hsub hf

/-- Any closed-block witness is retained by the half-open counted packet,
up to a null endpoint, when its derivative lower bound is at least the cutoff. -/
theorem countedPacket_measure_ge_witness
    (ν : Measure Trajectory) (H : Set Incidence) (A : Set Trajectory)
    (R : MvPolynomial (Fin 4) ℝ) (b : ℝ) (T j : ℕ) (V : Set Incidence)
    (hV : ∀ p ∈ V, p ∈ H ∧ p.1 ∈ A ∧
      p.2 ∈ Icc ((j : ℝ) / (2 : ℝ) ^ T) (((j : ℝ) + 1) / (2 : ℝ) ^ T) ∧
      b ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)|) :
    ν.prod volume V ≤ ν.prod volume (countedPacket H A R b T j) := by
  rw [← measure_trim_right ν V (((j : ℝ) + 1) / (2 : ℝ) ^ T)
    (fun p hp => (hV p hp).2.2.1.2)]
  apply measure_mono
  rintro p ⟨hp, ht⟩
  exact ⟨(hV p hp).1, (hV p hp).2.1, ⟨(hV p hp).2.2.1.1, ht⟩, (hV p hp).2.2.2⟩

/-- The original candidate floor survives both enlargement of the incidence
ambient set and relaxation of the hidden derivative threshold. -/
theorem candidate_countedPacket_floor_of_gain_le
    (Nk L : ℝ) (W C : ℕ) (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ)
    (d₁ ρ gain ε hmax cutoff : ℝ) (T : ℕ → ℕ) (lev : Fin C → ℕ)
    (γ : Fin C → Fin W) (j : Fin C → ℕ) (A : Fin C → Set Trajectory)
    (H₀ H : Fin W → Set Incidence) (a : CandidateDatum C)
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hd₁ : 0 ≤ d₁) (hgain : a.gain ≤ hmax)
    (hH : H₀ (γ a.parent) ⊆ H (γ a.parent))
    (hcut : cutoff ≤ B (γ a.parent) / Nk ^ (ρ * gain * L + ε))
    (hcount : CandidateCounted Nk L W C ν B d₁ ρ gain ε T lev γ j A H₀ a) :
    ENNReal.ofReal (Nk ^ (-((d₁ * hmax + ρ * gain) * L) - ε) /
      (2 : ℝ) ^ T (lev a.parent)) * ν (γ a.parent) (A a.parent) ≤
      (ν (γ a.parent)).prod volume (countedPacket (H (γ a.parent)) a.trajectories
        a.test cutoff (T (lev a.parent)) (j a.parent)) := by
  have hw := countedPacket_measure_ge_witness (ν (γ a.parent)) (H (γ a.parent))
    a.trajectories a.test cutoff (T (lev a.parent)) (j a.parent) a.counted
    (fun p hp => ⟨hH (hcount.2.1 hp), (hcount.2.2.1 p hp).1,
      (hcount.2.2.1 p hp).2.1, hcut.trans (hcount.2.2.1 p hp).2.2⟩)
  calc
    _ = ENNReal.ofReal (Nk ^ (-((d₁ * hmax + ρ * gain) * L) - ε)) *
        (ν (γ a.parent) (A a.parent) * ENNReal.ofReal (1 / (2 : ℝ) ^ T (lev a.parent))) := by
      rw [div_eq_mul_inv, ENNReal.ofReal_mul (Real.rpow_nonneg (le_trans zero_le_one hN) _)]
      simp only [one_div]
      ac_rfl
    _ ≤ (ν (γ a.parent)).prod volume a.counted := by
      simpa only [packetRegion_measure] using
        candidate_relative_floor_of_gain_le Nk L W C ν B d₁ ρ gain ε hmax
          T lev γ j A H₀ a hN hL hd₁ hgain hcount
    _ ≤ _ := hw

/-- At a single packet the only loss in passing from enlarged trajectory
coverage to counted coverage is its small-derivative sublevel. Endpoints cost zero. -/
theorem full_mass_le_counted_add_bad
    (ν : Measure Trajectory) [IsProbabilityMeasure ν]
    (H₀ H : Set Incidence) (hsubH : H₀ ⊆ H) (hHfin : ν.prod volume H ≠ ∞)
    (A : Set Trajectory) (R : MvPolynomial (Fin 4) ℝ) (b : ℝ) (T j : ℕ) :
    (ν.prod volume).real (H₀ ∩ (A ×ˢ Icc ((j : ℝ) / (2 : ℝ) ^ T)
      (((j : ℝ) + 1) / (2 : ℝ) ^ T))) ≤
    (ν.prod volume).real (countedPacket H A R b T j) +
      (ν.prod volume).real (badPacket A R b T j) := by
  let Q := H₀ ∩ (A ×ˢ Icc ((j : ℝ) / (2 : ℝ) ^ T) (((j : ℝ) + 1) / (2 : ℝ) ^ T))
  have hVfin : ν.prod volume (countedPacket H A R b T j) ≠ ∞ :=
    measure_ne_top_of_subset (fun p hp => hp.1) hHfin
  have hBfin := badPacket_finite ν A R b T j
  have hcover : ν.prod volume Q ≤ ν.prod volume (countedPacket H A R b T j) +
      ν.prod volume (badPacket A R b T j) := by
    rw [← measure_trim_right ν Q (((j : ℝ) + 1) / (2 : ℝ) ^ T) (fun p hp => hp.2.2.2)]
    apply (measure_mono (t := countedPacket H A R b T j ∪ badPacket A R b T j) ?_).trans
      (measure_union_le _ _)
    rintro p ⟨hp, ht⟩
    by_cases hg : b ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)|
    · exact Or.inl ⟨hsubH hp.1, hp.2.1, ⟨hp.2.2.1, ht⟩, hg⟩
    · exact Or.inr ⟨hp.2.1, hp.2.2, lt_of_not_ge hg⟩
  have hh := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hVfin, hBfin⟩) hcover
  rw [ENNReal.toReal_add hVfin hBfin] at hh
  exact hh

/-- The relaxed derivative floor recovers the full enlarged cover at one path
level, up to an inverse cubic loss independent of the family size. -/
theorem family_counted_recovery {ι : Type*} [Fintype ι]
    (W : ℕ) (ν : Fin W → Measure Trajectory) (ω : Fin W → ℝ)
    (γ : ι → Fin W) (j : ι → ℕ) (T : ℕ) (A : ι → Set Trajectory)
    (R : ι → MvPolynomial (Fin 4) ℝ) (B : Fin W → ℝ) (K : ℝ)
    (H₀ H : Fin W → Set Incidence)
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hω : ∀ w, 0 ≤ ω w)
    (hωsum : (∑ w, ω w) = 1) (hAm : ∀ a, MeasurableSet (A a))
    (hR : ∀ a, (R a).totalDegree ≤ 2) (hB : ∀ w, 0 < B w) (hK : 2 ≤ K)
    (hj : ∀ a, j a < 2 ^ T) (hsubH : ∀ w, H₀ w ⊆ H w)
    (hHfin : ∀ w, (ν w).prod volume (H w) ≠ ∞)
    (hdisj : ∀ a a', a ≠ a' → γ a = γ a' → j a = j a' → Disjoint (A a) (A a'))
    (hlarge : ∀ a l, l ∈ A a → ∃ t ∈ Icc ((j a : ℝ) / (2 : ℝ) ^ T)
      (((j a : ℝ) + 1) / (2 : ℝ) ^ T),
      B (γ a) / K ≤ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (R a))|) :
    (∑ a, ω (γ a) * ((ν (γ a)).prod volume).real
      (H₀ (γ a) ∩ (A a ×ˢ Icc ((j a : ℝ) / (2 : ℝ) ^ T)
        (((j a : ℝ) + 1) / (2 : ℝ) ^ T)))) ≤
    (∑ a, ω (γ a) * ((ν (γ a)).prod volume).real
      (countedPacket (H (γ a)) (A a) (R a) (B (γ a) / K ^ 4) T (j a))) + 8 / K ^ 3 := by
  have (w : Fin W) : IsProbabilityMeasure (ν w) := hν w
  have hKpos : 0 < K := by linarith
  let Bad : ι → Set Incidence := fun a => badPacket (A a) (R a) (B (γ a) / K ^ 4) T (j a)
  have hbadENN : (∑ a, ENNReal.ofReal (ω (γ a)) * (ν (γ a)).prod volume (Bad a)) ≤
      ENNReal.ofReal (8 / K ^ 3) :=
    family_bad_derivative_le W ν ω γ j T A R B K hν hω hωsum hAm hR hB hK hj hdisj hlarge
  have hbadreal : (∑ a, ω (γ a) * ((ν (γ a)).prod volume).real (Bad a)) ≤ 8 / K ^ 3 := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 8 / K ^ 3)).mp
    rw [ofReal_weighted_mass (fun a => (ν (γ a)).prod volume) (fun a => ω (γ a)) Bad
      (fun a => hω _) (fun a => badPacket_finite _ _ _ _ _ _)]
    exact hbadENN
  have hpoint (a : ι) := full_mass_le_counted_add_bad (ν (γ a)) (H₀ (γ a)) (H (γ a))
    (hsubH _) (hHfin _) (A a) (R a) (B (γ a) / K ^ 4) T (j a)
  calc
    _ ≤ ∑ a, ω (γ a) *
        (((ν (γ a)).prod volume).real (countedPacket (H (γ a)) (A a) (R a)
          (B (γ a) / K ^ 4) T (j a)) + ((ν (γ a)).prod volume).real (Bad a)) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hpoint a) (hω _))
    _ = (∑ a, ω (γ a) * ((ν (γ a)).prod volume).real
        (countedPacket (H (γ a)) (A a) (R a) (B (γ a) / K ^ 4) T (j a))) +
        ∑ a, ω (γ a) * ((ν (γ a)).prod volume).real (Bad a) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
    _ ≤ _ := add_le_add le_rfl hbadreal

end Submission.Obl.k4_quadratic_finite_greedy_cover
