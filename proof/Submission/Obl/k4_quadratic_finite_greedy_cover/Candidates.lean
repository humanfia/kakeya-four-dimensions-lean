-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/Candidates.lean.

import Submission.Obl.k4_quadratic_finite_greedy_cover.Coverage

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

open MeasureTheory Set
open scoped ENNReal

abbrev Trajectory := ℕ × (Fin 6 → ℝ)
abbrev Incidence := Trajectory × ℝ

/-- One candidate with its original, unnormalized counted incidences. -/
structure CandidateDatum (C : ℕ) where
  parent : Fin C
  gain : ℝ
  test : MvPolynomial (Fin 4) ℝ
  trajectories : Set Trajectory
  counted : Set Incidence

/-- The original whole-block geometry of a quadratic candidate. -/
def CandidateGeometry (Nk L : ℝ) (W C Mc : ℕ) (B : Fin W → ℝ)
    (ρ gain ε : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ) (lev : Fin C → ℕ)
    (γ : Fin C → Fin W) (j : Fin C → ℕ) (A : Fin C → Set Trajectory)
    (a : CandidateDatum C) : Prop :=
  gain ≤ a.gain ∧ a.gain ≤ 1 / 8 ∧ r (lev a.parent) + 2 * a.gain * L ≤ L ∧
  a.test.totalDegree ≤ 2 ∧ (∀ e, |a.test.coeff e| ≤ Nk ^ Mc) ∧
  MeasurableSet a.trajectories ∧ a.trajectories ⊆ A a.parent ∧
  ∀ l ∈ a.trajectories, ∀ t ∈ Icc ((j a.parent : ℝ) / (2 : ℝ) ^ T (lev a.parent))
      (((j a.parent : ℝ) + 1) / (2 : ℝ) ^ T (lev a.parent)),
    |MvPolynomial.eval (x l t) a.test| ≤
      Nk ^ (ρ * gain * L + ε) * δ Nk (r (lev a.parent) + a.gain * L) ∧
    |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) a.test)| ≤
      Nk ^ (ρ * gain * L + ε) * B (γ a.parent) ∧
    |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4)
      (MvPolynomial.pderiv (3 : Fin 4) a.test))| ≤
      Nk ^ (ρ * gain * L + ε) * B (γ a.parent) ^ 2 /
        δ Nk (r (lev a.parent) + a.gain * L)

/-- The mass and support certificate remains under the old trajectory law. -/
def CandidateCounted (Nk L : ℝ) (W C : ℕ) (ν : Fin W → Measure Trajectory)
    (B : Fin W → ℝ) (d₁ ρ gain ε : ℝ) (T : ℕ → ℕ) (lev : Fin C → ℕ)
    (γ : Fin C → Fin W) (j : Fin C → ℕ) (A : Fin C → Set Trajectory)
    (H : Fin W → Set Incidence) (a : CandidateDatum C) : Prop :=
  MeasurableSet a.counted ∧ a.counted ⊆ H (γ a.parent) ∧
  (∀ p ∈ a.counted, p.1 ∈ a.trajectories ∧
    p.2 ∈ Icc ((j a.parent : ℝ) / (2 : ℝ) ^ T (lev a.parent))
      (((j a.parent : ℝ) + 1) / (2 : ℝ) ^ T (lev a.parent)) ∧
    B (γ a.parent) / Nk ^ (ρ * gain * L + ε) ≤
      |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) a.test)|) ∧
  ENNReal.ofReal (Nk ^ (-((d₁ * a.gain + ρ * gain) * L) - ε) /
    (2 : ℝ) ^ T (lev a.parent)) * ν (γ a.parent) (A a.parent) ≤
      (ν (γ a.parent)).prod volume a.counted

theorem continuous_trajectory_point : Continuous (fun p : Incidence => x p.1 p.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [x] <;> fun_prop

/-- A frozen candidate is a datum with measurable counted incidences. -/
theorem candidate_has_counted_data
    (Nk L : ℝ) (W C Mc : ℕ) (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ)
    (d₁ ρ gain ε : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ) (lev : Fin C → ℕ)
    (γ : Fin C → Fin W) (j : Fin C → ℕ) (A : Fin C → Set Trajectory)
    (H : Fin W → Set Incidence) (hHm : ∀ w, MeasurableSet (H w))
    (hc : candidate Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H) :
    ∃ a : CandidateDatum C,
      CandidateGeometry Nk L W C Mc B ρ gain ε r T lev γ j A a ∧
      CandidateCounted Nk L W C ν B d₁ ρ gain ε T lev γ j A H a := by
  rcases hc with ⟨b, h, hgain, hcap, hroom, R, A', hdeg, hcoeff, hAm, hAsub, hupper, hmass⟩
  let V : Set Incidence := {p | p ∈ H (γ b) ∧ p.1 ∈ A' ∧
    p.2 ∈ Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b))
      (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b)) ∧
    B (γ b) / Nk ^ (ρ * gain * L + ε) ≤
      |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)|}
  have hD : Continuous (fun p : Incidence =>
      |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)|) :=
    ((MvPolynomial.continuous_eval _).comp continuous_trajectory_point).abs
  have hVm : MeasurableSet V := by
    have hDset : MeasurableSet {p : Incidence |
        B (γ b) / Nk ^ (ρ * gain * L + ε) ≤
          |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)|} :=
      measurableSet_le measurable_const hD.measurable
    have htime : MeasurableSet {p : Incidence |
        p.2 ∈ Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b))
          (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b))} :=
      measurableSet_Icc.preimage measurable_snd
    have hApre := hAm.preimage (measurable_fst : Measurable (Prod.fst : Incidence → Trajectory))
    simpa only [V, Set.inter_def, Set.mem_ofPred_eq, Set.mem_preimage, and_assoc] using
      (((hHm (γ b)).inter hApre).inter htime).inter hDset
  refine ⟨⟨b, h, R, A', V⟩,
    ⟨hgain, hcap, hroom, hdeg, hcoeff, hAm, hAsub, hupper⟩,
    hVm, ?_, ?_, hmass⟩
  · exact fun p hp => hp.1
  · exact fun p hp => hp.2

/-- The full old trajectory assignment crossed with its own time block. -/
def packetRegion {C : ℕ} (T : ℕ → ℕ) (lev : Fin C → ℕ) (j : Fin C → ℕ)
    (A : Fin C → Set Trajectory) (b : Fin C) : Set Incidence :=
  A b ×ˢ Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b))
    (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b))

theorem packetRegion_measure {C : ℕ} (ν : Measure Trajectory)
    (T : ℕ → ℕ) (lev : Fin C → ℕ) (j : Fin C → ℕ)
    (A : Fin C → Set Trajectory) (b : Fin C) :
    ν.prod volume (packetRegion T lev j A b) =
      ν (A b) * ENNReal.ofReal (1 / (2 : ℝ) ^ T (lev b)) := by
  rw [packetRegion, Measure.prod_prod, Real.volume_Icc]
  congr 2
  ring

/-- The original incidence floor controls the full packet at every upper gain endpoint. -/
theorem candidate_relative_floor_of_gain_le
    (Nk L : ℝ) (W C : ℕ) (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ)
    (d₁ ρ gain ε hmax : ℝ) (T : ℕ → ℕ) (lev : Fin C → ℕ)
    (γ : Fin C → Fin W) (j : Fin C → ℕ) (A : Fin C → Set Trajectory)
    (H : Fin W → Set Incidence) (a : CandidateDatum C)
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hd₁ : 0 ≤ d₁) (hgain : a.gain ≤ hmax)
    (hcount : CandidateCounted Nk L W C ν B d₁ ρ gain ε T lev γ j A H a) :
    ENNReal.ofReal (Nk ^ (-((d₁ * hmax + ρ * gain) * L) - ε)) *
      (ν (γ a.parent)).prod volume (packetRegion T lev j A a.parent) ≤
        (ν (γ a.parent)).prod volume a.counted := by
  have hexp : -((d₁ * hmax + ρ * gain) * L) - ε ≤
      -((d₁ * a.gain + ρ * gain) * L) - ε := by
    have hg := mul_le_mul_of_nonneg_left hgain hd₁
    nlinarith [mul_le_mul_of_nonneg_right hg hL]
  have hpow := ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hN hexp)
  calc
    _ ≤ ENNReal.ofReal (Nk ^ (-((d₁ * a.gain + ρ * gain) * L) - ε)) *
        (ν (γ a.parent)).prod volume (packetRegion T lev j A a.parent) :=
      mul_le_mul' hpow le_rfl
    _ = ENNReal.ofReal (Nk ^ (-((d₁ * a.gain + ρ * gain) * L) - ε) /
        (2 : ℝ) ^ T (lev a.parent)) * ν (γ a.parent) (A a.parent) := by
      have hfactor : ENNReal.ofReal
          (Nk ^ (-((d₁ * a.gain + ρ * gain) * L) - ε) / (2 : ℝ) ^ T (lev a.parent)) =
          ENNReal.ofReal (Nk ^ (-((d₁ * a.gain + ρ * gain) * L) - ε)) *
            ENNReal.ofReal (1 / (2 : ℝ) ^ T (lev a.parent)) := by
        rw [div_eq_mul_one_div,
          ENNReal.ofReal_mul (Real.rpow_nonneg (le_trans zero_le_one hN) _)]
      rw [packetRegion_measure, hfactor]
      ac_rfl
    _ ≤ _ := hcount.2.2.2

/-- The incidence floor is a relative mass floor for the full old packet. -/
theorem candidate_relative_floor
    (Nk L : ℝ) (W C Mc : ℕ) (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ)
    (d₁ ρ gain ε : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ) (lev : Fin C → ℕ)
    (γ : Fin C → Fin W) (j : Fin C → ℕ) (A : Fin C → Set Trajectory)
    (H : Fin W → Set Incidence) (a : CandidateDatum C)
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hd₁ : 0 ≤ d₁)
    (hgeom : CandidateGeometry Nk L W C Mc B ρ gain ε r T lev γ j A a)
    (hcount : CandidateCounted Nk L W C ν B d₁ ρ gain ε T lev γ j A H a) :
    ENNReal.ofReal (Nk ^ (-((d₁ / 8 + ρ * gain) * L) - ε)) *
      (ν (γ a.parent)).prod volume (packetRegion T lev j A a.parent) ≤
        (ν (γ a.parent)).prod volume a.counted := by
  simpa only [mul_one_div] using candidate_relative_floor_of_gain_le Nk L W C ν B
    d₁ ρ gain ε (1 / 8) T lev γ j A H a hN hL hd₁ hgeom.2.1 hcount

/-- Concrete residual candidates give a finite counted cover, unless the supplied
alternative exit occurs. No graph grouping is used in this selection step. -/
theorem finite_candidate_cover
    (Nk L : ℝ) (W C Mc : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ)
    (d₁ ρ gain ε κ : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ) (lev : Fin C → ℕ)
    (γ : Fin C → Fin W) (j : Fin C → ℕ) (A : Fin C → Set Trajectory)
    (H₀ : Fin W → Set Incidence) (Exit : Prop)
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hd₁ : 0 ≤ d₁) (hω : ∀ w, 0 ≤ ω w)
    (hHm : ∀ w, MeasurableSet (H₀ w))
    (hHfin : ∀ w, (ν w).prod volume (H₀ w) ≠ ∞)
    (hHmass : ENNReal.ofReal κ⁻¹ ≤
      ∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (H₀ w))
    (hUpos : ∀ b, 0 < ((ν (γ b)).prod volume).real (packetRegion T lev j A b))
    (hUfin : ∀ b, (ν (γ b)).prod volume (packetRegion T lev j A b) ≠ ∞)
    (hdiscovery : ∀ H : Fin W → Set Incidence,
      (∀ w, MeasurableSet (H w) ∧ H w ⊆ H₀ w) →
      ENNReal.ofReal (κ⁻¹ / 2) ≤ ∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (H w) →
      Exit ∨ candidate Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H) :
    Exit ∨ ∃ S : Finset (CandidateDatum C),
      (∀ a ∈ S,
        CandidateGeometry Nk L W C Mc B ρ gain ε r T lev γ j A a ∧
        CandidateCounted Nk L W C ν B d₁ ρ gain ε T lev γ j A H₀ a) ∧
      (∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → γ a.parent = γ a'.parent →
        Disjoint a.counted a'.counted) ∧
      ENNReal.ofReal (κ⁻¹ / 2) ≤ ∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume
        (selectedUnion S (fun a => γ a.parent) CandidateDatum.counted w) := by
  classical
  let μ : Fin W → Measure Incidence := fun w => (ν w).prod volume
  let Good : CandidateDatum C → Prop := fun a =>
    CandidateGeometry Nk L W C Mc B ρ gain ε r T lev γ j A a ∧
      CandidateCounted Nk L W C ν B d₁ ρ gain ε T lev γ j A H₀ a
  have hHnonneg : 0 ≤ ∑ w, ω w * (μ w).real (H₀ w) :=
    Finset.sum_nonneg (fun w _ => mul_nonneg (hω w) ENNReal.toReal_nonneg)
  have hHreal : κ⁻¹ ≤ ∑ w, ω w * (μ w).real (H₀ w) := by
    apply (ENNReal.ofReal_le_ofReal_iff hHnonneg).mp
    rw [ofReal_weighted_mass μ ω H₀ hω hHfin]
    exact hHmass
  let θ : ℝ := Nk ^ (-((d₁ / 8 + ρ * gain) * L) - ε)
  have hθ : 0 < θ := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hN) _
  have hGood : ∀ a, Good a → MeasurableSet a.counted ∧
      a.counted ⊆ H₀ (γ a.parent) ∧ a.counted ⊆ packetRegion T lev j A a.parent ∧
      ENNReal.ofReal θ * μ (γ a.parent) (packetRegion T lev j A a.parent) ≤
        μ (γ a.parent) a.counted := by
    intro a ha
    obtain ⟨hg, hc⟩ := ha
    refine ⟨hc.1, hc.2.1, ?_,
      candidate_relative_floor Nk L W C Mc ν B d₁ ρ gain ε r T lev γ j A H₀ a
        hN hL hd₁ hg hc⟩
    intro p hp
    rcases hg with ⟨_, _, _, _, _, _, hAsub, _⟩
    have hpt := hc.2.2.1 p hp
    exact ⟨hAsub hpt.1, hpt.2.1⟩
  have hselect : ∀ H : Fin W → Set Incidence,
      (∀ w, MeasurableSet (H w) ∧ H w ⊆ H₀ w) →
      (∑ w, ω w * (μ w).real (H₀ w)) / 2 ≤ ∑ w, ω w * (μ w).real (H w) →
      Exit ∨ ∃ a, Good a ∧ a.counted ⊆ H (γ a.parent) := by
    intro H hH hmass
    have hHfinite : ∀ w, μ w (H w) ≠ ∞ :=
      fun w => measure_ne_top_of_subset (hH w).2 (hHfin w)
    have hmass' : ENNReal.ofReal (κ⁻¹ / 2) ≤
        ∑ w, ENNReal.ofReal (ω w) * μ w (H w) := by
      rw [← ofReal_weighted_mass μ ω H hω hHfinite]
      exact ENNReal.ofReal_le_ofReal (by linarith [hHreal])
    rcases hdiscovery H hH hmass' with hex | hc
    · exact Or.inl hex
    obtain ⟨a, hg, ha⟩ := candidate_has_counted_data Nk L W C Mc ν B d₁ ρ gain ε
      r T lev γ j A H (fun w => (hH w).1) hc
    exact Or.inr ⟨a, ⟨hg, ha.1, ha.2.1.trans (hH _).2, ha.2.2⟩, ha.2.1⟩
  rcases weighted_greedy_cover μ ω H₀ (packetRegion T lev j A) γ
      CandidateDatum.parent CandidateDatum.counted Good Exit hθ hHm hHfin
      hUpos hUfin hGood hselect with hex | ⟨S, hS, hdisj, hmass⟩
  · exact Or.inl hex
  refine Or.inr ⟨S, hS, hdisj, ?_⟩
  have hsub (w : Fin W) :
      selectedUnion S (fun a => γ a.parent) CandidateDatum.counted w ⊆ H₀ w := by
    intro p hp
    obtain ⟨a, ha, haw, hp⟩ := mem_iUnion₂.mp hp
    have hc := (hS a ha).2
    simpa only [haw] using hc.2.1 hp
  have hfinite (w : Fin W) : μ w
      (selectedUnion S (fun a => γ a.parent) CandidateDatum.counted w) ≠ ∞ :=
    measure_ne_top_of_subset (hsub w) (hHfin w)
  rw [← ofReal_weighted_mass μ ω _ hω hfinite]
  exact ENNReal.ofReal_le_ofReal (by linarith [hHreal])

/-- Every old packet of a saturated path has positive, finite reference mass.
No lower floor is lost to an analytical restriction. -/
theorem path_packetRegion_budget
    (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
    (E : Fin W → Set Incidence) (B : Fin W → ℝ) (f : ℝ → ℝ)
    (κ₁ : ℝ) (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ) (Mp Dp : ℕ) (σ : ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (nw : ℕ → ℝ) (κ : ℝ) (C : ℕ)
    (lev : Fin C → ℕ) (par : Fin C → Fin C) (γ : Fin C → Fin W)
    (j : Fin C → ℕ) (c u : Fin C → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (R : Fin C → MvPolynomial (Fin 4) ℝ) (A : Fin C → Set Trajectory)
    (F : Fin C → Set Incidence)
    (lst : ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C))
    (hN : 1 ≤ Nk) (hν : ∀ w, IsProbabilityMeasure (ν w))
    (hp : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ
      C lev par γ j c u Q R A F lst) :
    (∀ b, 0 < ((ν (γ b)).prod volume).real (packetRegion T lev j A b)) ∧
      (∀ b, (ν (γ b)).prod volume (packetRegion T lev j A b) ≠ ∞) := by
  have (w : Fin W) : IsProbabilityMeasure (ν w) := hν w
  rcases hp with ⟨hκ, hσ, hcount, hend, hlevels, hlists, hdisj, hnodes⟩
  have hfinite (b : Fin C) : (ν (γ b)).prod volume (packetRegion T lev j A b) ≠ ∞ := by
    rw [packetRegion_measure]
    finiteness
  refine ⟨?_, hfinite⟩
  intro b
  rcases (hnodes b).2.2 with ⟨hdet, hcu, hQ, hsize, hdeg, hcoeff, hAm, hFm,
    hfmt, hA, hF, hex⟩
  have hsat : ENNReal.ofReal (Nk ^ (-f (r (lev b))) * |Matrix.det (Q b)| /
      ((2 : ℝ) ^ T (lev b) * κ)) ≤ (ν (γ b)).prod volume (F b) := hex.1
  have hmupos : 0 < (ν (γ b)).prod volume (F b) := by
    apply lt_of_lt_of_le _ hsat
    apply ENNReal.ofReal_pos.mpr
    exact div_pos
      (mul_pos (Real.rpow_pos_of_pos (by linarith) _) (abs_pos.mpr hdet))
      (mul_pos (by positivity) (by linarith))
  have hA0 : ν (γ b) (A b) ≠ 0 := by
    intro hz
    have hsub : F b ⊆ A b ×ˢ Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b))
        (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b)) := by
      intro p hp
      exact ⟨(hF p hp).2.1, (hF p hp).2.2.1⟩
    have hbnd : (ν (γ b)).prod volume (F b) ≤ ν (γ b) (A b) *
        volume (Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b))
          (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b))) :=
      (measure_mono hsub).trans (Measure.prod_prod_le _ _)
    rw [hz, zero_mul] at hbnd
    exact (not_le_of_gt hmupos) hbnd
  have hAfin : ν (γ b) (A b) ≠ ∞ := by finiteness
  have hq : 0 < 1 / (2 : ℝ) ^ T (lev b) := by positivity
  rw [measureReal_def, packetRegion_measure, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hq.le]
  exact mul_pos (ENNReal.toReal_pos hA0 hAfin) hq

/-- The original final-level incidence set in each world. -/
def terminalUnion {W C : ℕ} (m : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W)
    (F : Fin C → Set Incidence) : Fin W → Set Incidence :=
  fun w => {p | ∃ b, lev b = m - 1 ∧ γ b = w ∧ p ∈ F b}

/-- The finite counted-cover conclusion at the exact supplied saturated path. -/
theorem path_candidate_cover
    (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
    (E : Fin W → Set Incidence) (B : Fin W → ℝ) (f : ℝ → ℝ)
    (κ₁ : ℝ) (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ) (Mp Dp : ℕ) (σ : ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (nw : ℕ → ℝ) (κ : ℝ) (C : ℕ)
    (lev : Fin C → ℕ) (par : Fin C → Fin C) (γ : Fin C → Fin W)
    (j : Fin C → ℕ) (c u : Fin C → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (R : Fin C → MvPolynomial (Fin 4) ℝ) (A : Fin C → Set Trajectory)
    (F : Fin C → Set Incidence)
    (lst : ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C))
    (Mc : ℕ) (d₁ ρ gain ε : ℝ) (Exit : Prop)
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hd₁ : 0 ≤ d₁)
    (hω : ∀ w, 0 ≤ ω w) (hν : ∀ w, IsProbabilityMeasure (ν w))
    (hE : ∀ w, E w ⊆ Set.univ ×ˢ Icc (0 : ℝ) 1) (hm : 0 < m)
    (hp : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ
      C lev par γ j c u Q R A F lst)
    (hdiscovery : ∀ H : Fin W → Set Incidence,
      (∀ w, MeasurableSet (H w) ∧ H w ⊆ terminalUnion m lev γ F w) →
      ENNReal.ofReal (κ⁻¹ / 2) ≤ ∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (H w) →
      Exit ∨ candidate Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H) :
    Exit ∨ ∃ S : Finset (CandidateDatum C),
      (∀ a ∈ S,
        CandidateGeometry Nk L W C Mc B ρ gain ε r T lev γ j A a ∧
        CandidateCounted Nk L W C ν B d₁ ρ gain ε T lev γ j A (terminalUnion m lev γ F) a) ∧
      (∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → γ a.parent = γ a'.parent →
        Disjoint a.counted a'.counted) ∧
      ENNReal.ofReal (κ⁻¹ / 2) ≤ ∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume
        (selectedUnion S (fun a => γ a.parent) CandidateDatum.counted w) := by
  classical
  have (w : Fin W) : IsProbabilityMeasure (ν w) := hν w
  obtain ⟨hUpos, hUfin⟩ := path_packetRegion_budget Nk L W ω ν E B f κ₁ m s δ₀
    Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst hN hν hp
  obtain ⟨H₀, hH₀, hmass₀⟩ := path_terminal_residual Nk L W ω ν E B f κ₁ m s δ₀
    Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst hm hp
  rcases hp with ⟨_, _, _, _, _, _, _, hnodes⟩
  have hHfin (w : Fin W) : (ν w).prod volume (H₀ w) ≠ ∞ := by
    have hsub : H₀ w ⊆ Set.univ ×ˢ Icc (0 : ℝ) 1 := by
      intro p hp
      obtain ⟨b, _, hb, hpb⟩ := (hH₀ w).2 hp
      rcases (hnodes b).2.2 with ⟨_, _, _, _, _, _, _, _, _, _, hF, _⟩
      apply hE w
      simpa only [hb] using (hF p hpb).1
    exact measure_ne_top_of_subset hsub (by simp)
  rcases finite_candidate_cover Nk L W C Mc ω ν B d₁ ρ gain ε κ r T lev γ j A
      H₀ Exit hN hL hd₁ hω (fun w => (hH₀ w).1) hHfin hmass₀ hUpos hUfin
      (by
        intro H hH hmass
        apply hdiscovery H _ hmass
        exact fun w => ⟨(hH w).1, (hH w).2.trans (hH₀ w).2⟩) with
    hex | ⟨S, hS, hdisj, hmass⟩
  · exact Or.inl hex
  refine Or.inr ⟨S, ?_, hdisj, hmass⟩
  intro a ha
  obtain ⟨hg, hc⟩ := hS a ha
  exact ⟨hg, hc.1, hc.2.1.trans (hH₀ _).2, hc.2.2⟩

/-- The list of candidates assigned to one old packet has the correct
actual-gain exponent, rather than the worst possible gain exponent. -/
theorem candidate_card_parent_gain_le
    (Nk L : ℝ) (W C Mc : ℕ) (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ)
    (d₁ ρ gain ε hmax : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ) (lev : Fin C → ℕ)
    (γ : Fin C → Fin W) (j : Fin C → ℕ) (A : Fin C → Set Trajectory)
    (H : Fin W → Set Incidence) (S : Finset (CandidateDatum C))
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hd₁ : 0 ≤ d₁)
    (hS : ∀ a ∈ S,
      CandidateGeometry Nk L W C Mc B ρ gain ε r T lev γ j A a ∧
      CandidateCounted Nk L W C ν B d₁ ρ gain ε T lev γ j A H a)
    (hdisj : ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → γ a.parent = γ a'.parent →
      Disjoint a.counted a'.counted)
    (b : Fin C)
    (hUpos : 0 < ((ν (γ b)).prod volume).real (packetRegion T lev j A b))
    (hUfin : (ν (γ b)).prod volume (packetRegion T lev j A b) ≠ ∞) :
    ((S.filter (fun a => a.parent = b ∧ a.gain ≤ hmax)).card : ℝ) ≤
      Nk ^ ((d₁ * hmax + ρ * gain) * L + ε) := by
  classical
  let t := S.filter (fun a => a.parent = b ∧ a.gain ≤ hmax)
  let θ := Nk ^ (-((d₁ * hmax + ρ * gain) * L) - ε)
  have hθ : 0 < θ := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hN) _
  have hV : ∀ a ∈ t, MeasurableSet a.counted ∧ a.counted ⊆ packetRegion T lev j A b := by
    intro a ha
    have has := (Finset.mem_filter.mp ha).1
    have hab := (Finset.mem_filter.mp ha).2.1
    obtain ⟨hg, hc⟩ := hS a has
    refine ⟨hc.1, ?_⟩
    intro p hp
    rcases hg with ⟨_, _, _, _, _, _, hsub, _⟩
    have hpt := hc.2.2.1 p hp
    have hpacket : p ∈ packetRegion T lev j A a.parent := ⟨hsub hpt.1, hpt.2.1⟩
    simpa only [hab] using hpacket
  have hd : (t : Set (CandidateDatum C)).PairwiseDisjoint CandidateDatum.counted := by
    intro a ha a' ha' hne
    exact hdisj a (Finset.mem_filter.mp ha).1 a' (Finset.mem_filter.mp ha').1 hne
      (congrArg γ ((Finset.mem_filter.mp ha).2.1.trans (Finset.mem_filter.mp ha').2.1.symm))
  have hf : ∀ a ∈ t, ENNReal.ofReal θ *
      (ν (γ b)).prod volume (packetRegion T lev j A b) ≤ (ν (γ b)).prod volume a.counted := by
    intro a ha
    have has := (Finset.mem_filter.mp ha).1
    have hab := (Finset.mem_filter.mp ha).2.1
    have hgain := (Finset.mem_filter.mp ha).2.2
    have hh := candidate_relative_floor_of_gain_le Nk L W C ν B d₁ ρ gain ε hmax
      T lev γ j A H a hN hL hd₁ hgain (hS a has).2
    simpa only [hab] using hh
  have hcard := card_le_inv_relative_floor ((ν (γ b)).prod volume)
    (packetRegion T lev j A b) CandidateDatum.counted t hθ hUpos hUfin hV hd hf
  have hinv : θ⁻¹ = Nk ^ ((d₁ * hmax + ρ * gain) * L + ε) := by
    rw [← Real.rpow_neg (le_trans zero_le_one hN)]
    congr 1
    ring
  exact hcard.trans_eq hinv

end Submission.Obl.k4_quadratic_finite_greedy_cover
