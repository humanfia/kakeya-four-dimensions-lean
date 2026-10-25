-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/RoundedCoverage.lean.

import Submission.Obl.k4_quadratic_finite_greedy_cover.LevelCoverage
import Submission.Obl.k4_quadratic_finite_greedy_cover.GainBuffer
import Submission.Obl.k4_quadratic_finite_greedy_cover.PriorityBounds
import Submission.Obl.k4_quadratic_finite_greedy_cover.PriorityFormat

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

open MeasureTheory Set
open scoped ENNReal

/-- The finite rounded candidate certificate reviewed with the o117 splitter.
The type follows x0441's Certificates.lean (7674006); no proof from that file is used. -/
def RoundedCoverage (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (B : Fin W → ℝ)
    (d₁ ρ gain : ℝ) (m : ℕ) (r : ℕ → ℝ) (T : ℕ → ℕ)
    (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (A : Fin C → Set (ℕ × (Fin 6 → ℝ)))
    (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (Mg Dg : ℕ) (ε : ℝ) : Prop :=
  ∃ (i : ℕ) (h : ℝ) (n : ℕ) (old : Fin n → Fin C)
      (R' : Fin n → MvPolynomial (Fin 4) ℝ)
      (A' : Fin n → Set (ℕ × (Fin 6 → ℝ)))
      (V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)),
    i < m ∧ gain ≤ h ∧ h ≤ 1 / 8 ∧ (∃ z : ℕ, h = gain + (z : ℝ) * (ρ * gain)) ∧
    r i + 2 * h * L ≤ L ∧ (n : ℝ) ≤ Nk ^ Mg ∧
    (∀ a, lev (old a) = i ∧ 0 < ν (γ (old a)) (A (old a)) ∧
      (R' a).totalDegree ≤ 2 ∧ (∀ e, |(R' a).coeff e| ≤ Nk ^ Mg) ∧
      MeasurableSet (A' a) ∧ A' a ⊆ A (old a) ∧
      (∀ q, fmt 6 (Nk ^ Mg) Dg {z | (q, z) ∈ A' a}) ∧
      (∀ l ∈ A' a, ∀ t ∈ Set.Icc ((j (old a) : ℝ) / (2 : ℝ) ^ T i) (((j (old a) : ℝ) + 1) / (2 : ℝ) ^ T i),
        |MvPolynomial.eval (x l t) (R' a)| ≤ Nk ^ (4 * ρ * gain * L + 4 * ε) * δ Nk (r i + h * L) ∧
        |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (R' a))| ≤ Nk ^ (4 * ρ * gain * L + 4 * ε) * B (γ (old a)) ∧
        |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (R' a)))| ≤ Nk ^ (4 * ρ * gain * L + 4 * ε) * B (γ (old a)) ^ 2 / δ Nk (r i + h * L)) ∧
      MeasurableSet (V a) ∧ V a ⊆ {p | (∃ b : Fin C, lev b = m - 1 ∧ γ b = γ (old a) ∧ p ∈ F b) ∧
        p.1 ∈ A' a ∧ p.2 ∈ Set.Icc ((j (old a) : ℝ) / (2 : ℝ) ^ T i) (((j (old a) : ℝ) + 1) / (2 : ℝ) ^ T i) ∧
        B (γ (old a)) / Nk ^ (4 * ρ * gain * L + 4 * ε) ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (R' a))|} ∧
      ENNReal.ofReal (Nk ^ (-((d₁ * h + 4 * ρ * gain) * L) - 4 * ε) / (2 : ℝ) ^ T i) * ν (γ (old a)) (A (old a)) ≤
        ((ν (γ (old a))).prod MeasureTheory.volume) (V a)) ∧
    (∀ a a', a ≠ a' → old a = old a' → Disjoint (A' a) (A' a')) ∧
    (∀ b : Fin C, ((Finset.univ.filter (fun a => old a = b)).card : ℝ) ≤ Nk ^ ((d₁ * h + 4 * ρ * gain) * L + 4 * ε)) ∧
    (∀ a a', a ≠ a' → γ (old a) = γ (old a') → Disjoint (V a) (V a')) ∧
    ENNReal.ofReal (Nk ^ (-ε)) ≤ ∑ a, ENNReal.ofReal (ω (γ (old a))) * ((ν (γ (old a))).prod MeasureTheory.volume) (V a)


/-- Assemble the exact rounded finite-array certificate from a selected
priority subfamily, retaining the old full-assignment mass floors. -/
theorem roundedCoverage_of_priority_subfamily
    (Nk L : ℝ) (W C Mc Mp Dp Mg Dg m : ℕ)
    (ν : Fin W → Measure Trajectory) (ω : Fin W → ℝ) (B : Fin W → ℝ)
    (d₁ ρ gain εin ε : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ) (lev : Fin C → ℕ)
    (γ : Fin C → Fin W) (j : Fin C → ℕ) (A : Fin C → Set Trajectory)
    (F : Fin C → Set Incidence) (H₀ : Fin W → Set Incidence)
    (S U : Finset (CandidateDatum C)) (i z : ℕ)
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hd₁ : 0 ≤ d₁) (hd₁' : d₁ ≤ 1)
    (hstep : 0 < ρ * gain) (hεin : 0 ≤ εin) (hεin' : εin ≤ ε)
    (habsorb : 2 ≤ Nk ^ ε) (hK : 2 ≤ Nk ^ (ρ * gain * L + εin))
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hω : ∀ w, 0 ≤ ω w) (hB : ∀ w, 0 < B w)
    (hApos : ∀ b, 0 < (ν (γ b)).real (A b))
    (hAfmt : ∀ b copy, fmt 6 (Nk ^ Mp) Dp {v | (copy, v) ∈ A b})
    (hHsub : ∀ w, H₀ w ⊆ terminalUnion m lev γ F w)
    (hHm : ∀ w, MeasurableSet (terminalUnion m lev γ F w))
    (hHfin : ∀ w, (ν w).prod volume (terminalUnion m lev γ F w) ≠ ∞)
    (hS : ∀ a ∈ S, CandidateGeometry Nk L W C Mc B ρ gain εin r T lev γ j A a ∧
      CandidateCounted Nk L W C ν B d₁ ρ gain εin T lev γ j A H₀ a)
    (hpriority : ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → a.parent = a'.parent →
      Disjoint a.trajectories a'.trajectories)
    (hrep : ∀ a ∈ S, ∃ P : Finset (CandidateDatum C), P ⊆ S ∧
      a.trajectories = candidateEnvelope Nk L W C B ρ gain εin r T lev γ j A a \
        selectedUnion P CandidateDatum.parent
          (candidateEnvelope Nk L W C B ρ gain εin r T lev γ j A) a.parent)
    (hold : ∀ b b', b ≠ b' → lev b = lev b' → γ b = γ b' → j b = j b' →
      Disjoint (A b) (A b'))
    (hi : i < m) (hUS : U ⊆ S) (hUn : U.Nonempty)
    (hUi : ∀ a ∈ U, lev a.parent = i)
    (hUg : ∀ a ∈ U, gain + (z : ℝ) * (ρ * gain) ≤ a.gain ∧
      a.gain ≤ gain + (z : ℝ) * (ρ * gain) + ρ * gain)
    (hDg : max Dp 4 ≤ Dg) (hMc : Mc ≤ Mg) (hScard : (S.card : ℝ) ≤ Nk ^ Mg)
    (hformat : ((S.card : ℝ) + 1) * (Nk ^ Mp + 96) ≤ Nk ^ Mg)
    (hmass : Nk ^ (-ε) ≤ ∑ a ∈ U, ω (γ a.parent) * ((ν (γ a.parent)).prod volume).real
      (countedPacket (terminalUnion m lev γ F (γ a.parent)) a.trajectories a.test
        (B (γ a.parent) / (Nk ^ (ρ * gain * L + εin)) ^ 4) (T i) (j a.parent))) :
    RoundedCoverage Nk L W ω ν B d₁ ρ gain m r T C lev γ j A F Mg Dg ε := by
  classical
  have (w : Fin W) : IsProbabilityMeasure (ν w) := hν w
  let h := gain + (z : ℝ) * (ρ * gain)
  let K := Nk ^ (ρ * gain * L + εin)
  let slack := Nk ^ (4 * ρ * gain * L + 4 * ε)
  let H := terminalUnion m lev γ F
  let V : CandidateDatum C → Set Incidence := fun a =>
    countedPacket (H (γ a.parent)) a.trajectories a.test
      (B (γ a.parent) / K ^ 4) (T i) (j a.parent)
  have hε : 0 ≤ ε := hεin.trans hεin'
  have hNkpos : 0 < Nk := lt_of_lt_of_le zero_lt_one hN
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hKone : 1 ≤ K := by dsimp [K]; linarith
  have hslackpos : 0 < slack := by dsimp [slack]; positivity
  have hbuf : 2 * K * Nk ^ (ρ * gain * L) ≤ slack ∧ K ^ 4 ≤ slack := by
    simpa only [K, slack, mul_assoc] using
      fourfold_gain_buffers Nk (ρ * gain) L εin ε hN hstep.le hL hεin hεin' habsorb
  have hpow4 : K ≤ K ^ 4 := le_self_pow₀ hKone (by norm_num)
  have hcut (w : Fin W) : B w / K ^ 4 ≤ B w / K :=
    div_le_div_of_nonneg_left (hB w).le hKpos hpow4
  have hgainh : gain ≤ h := by
    dsimp [h]
    nlinarith [mul_nonneg (Nat.cast_nonneg z) hstep.le]
  obtain ⟨a₀, ha₀⟩ := hUn
  have hcap : h ≤ 1 / 8 := (hUg a₀ ha₀).1.trans (hS a₀ (hUS ha₀)).1.2.1
  have hroom : r i + 2 * h * L ≤ L := by
    have hh := (hS a₀ (hUS ha₀)).1.2.2.1
    rw [hUi a₀ ha₀] at hh
    nlinarith [mul_le_mul_of_nonneg_right (hUg a₀ ha₀).1 hL]
  have hdisj := priority_fixed_level_disjoint W C U lev γ j A i hUi
    (fun a ha => (hS a (hUS ha)).1.2.2.2.2.2.2.1)
    (fun a ha a' ha' => hpriority a (hUS ha) a' (hUS ha')) hold
  have hVm (a : CandidateDatum C) (ha : a ∈ U) : MeasurableSet (V a) :=
    countedPacket_measurable _ _ (hHm _) (hS a (hUS ha)).1.2.2.2.2.2.1 _ _ _ _
  have hVfin (a : CandidateDatum C) : (ν (γ a.parent)).prod volume (V a) ≠ ∞ :=
    measure_ne_top_of_subset (fun p hp => hp.1) (hHfin _)
  have hgexp : (d₁ * (h + ρ * gain) + ρ * gain) * L + εin ≤
      (d₁ * h + 4 * ρ * gain) * L + 4 * ε := by
    have hh := rounded_gain_exponent d₁ (ρ * gain) (h + ρ * gain) h L εin ε
      hd₁ hd₁' hstep.le hL le_rfl (by linarith)
    simpa only [mul_assoc] using hh
  have hpoint (a : CandidateDatum C) (ha : a ∈ U) :
      lev a.parent = i ∧ 0 < ν (γ a.parent) (A a.parent) ∧
      a.test.totalDegree ≤ 2 ∧ (∀ e, |a.test.coeff e| ≤ Nk ^ Mg) ∧
      MeasurableSet a.trajectories ∧ a.trajectories ⊆ A a.parent ∧
      (∀ q, fmt 6 (Nk ^ Mg) Dg {v | (q, v) ∈ a.trajectories}) ∧
      (∀ l ∈ a.trajectories, ∀ t ∈ Icc ((j a.parent : ℝ) / (2 : ℝ) ^ T i)
          (((j a.parent : ℝ) + 1) / (2 : ℝ) ^ T i),
        |MvPolynomial.eval (x l t) a.test| ≤ slack * δ Nk (r i + h * L) ∧
        |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) a.test)| ≤ slack * B (γ a.parent) ∧
        |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4)
          (MvPolynomial.pderiv (3 : Fin 4) a.test))| ≤ slack * B (γ a.parent) ^ 2 / δ Nk (r i + h * L)) ∧
      MeasurableSet (V a) ∧ V a ⊆ {p | p ∈ H (γ a.parent) ∧ p.1 ∈ a.trajectories ∧
        p.2 ∈ Icc ((j a.parent : ℝ) / (2 : ℝ) ^ T i) (((j a.parent : ℝ) + 1) / (2 : ℝ) ^ T i) ∧
        B (γ a.parent) / slack ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) a.test)|} ∧
      ENNReal.ofReal (Nk ^ (-((d₁ * h + 4 * ρ * gain) * L) - 4 * ε) / (2 : ℝ) ^ T i) *
        ν (γ a.parent) (A a.parent) ≤ (ν (γ a.parent)).prod volume (V a) := by
    have hg := (hS a (hUS ha)).1
    have hcert := (hS a (hUS ha)).2
    obtain ⟨hga, hgc, hgr, hdeg, hcoeff, hAm, hAsub, hupper⟩ := hg
    refine ⟨hUi a ha, (ENNReal.toReal_pos_iff.mp (hApos a.parent)).1, hdeg,
      (fun e => (hcoeff e).trans (pow_le_pow_right₀ hN hMc)), hAm, hAsub, ?_, ?_, hVm a ha, ?_, ?_⟩
    · intro q
      obtain ⟨P, hP, hPa⟩ := hrep a (hUS ha)
      have hf := priority_assignment_format Nk L W C B ρ gain εin r T lev γ j A S
        (Nk ^ Mp) Dp (by positivity) hAfmt
        (fun a ha => (hS a ha).1.2.2.2.1) a (hUS ha) P hP hPa q
      exact Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono hf hformat hDg
    · have hh := rounded_candidate_upper Nk L W C Mc B ρ gain εin r T lev γ j A a
        h (ρ * gain) slack hN hL hstep.le (hB _).le (hUg a ha).1 (hUg a ha).2
        hbuf.1 (hS a (hUS ha)).1
      simpa only [hUi a ha] using hh
    · intro p hp
      refine ⟨hp.1, hp.2.1, ⟨hp.2.2.1.1, hp.2.2.1.2.le⟩, ?_⟩
      exact (div_le_div_of_nonneg_left (hB _).le (pow_pos hKpos _) hbuf.2).trans hp.2.2.2
    · have hf := candidate_countedPacket_floor_of_gain_le Nk L W C ν B d₁ ρ gain εin
        (h + ρ * gain) (B (γ a.parent) / K ^ 4) T lev γ j A H₀ H a
        hN hL hd₁ (hUg a ha).2 (hHsub _) (hcut _) hcert
      have hp : Nk ^ (-((d₁ * h + 4 * ρ * gain) * L) - 4 * ε) ≤
          Nk ^ (-((d₁ * (h + ρ * gain) + ρ * gain) * L) - εin) :=
        Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      have hleft := mul_le_mul' (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right hp (by positivity : 0 ≤ (2 : ℝ) ^ T i)))
        (le_rfl : ν (γ a.parent) (A a.parent) ≤ ν (γ a.parent) (A a.parent))
      exact hleft.trans (by simpa only [hUi a ha] using hf)
  have hparent (b : Fin C) : ((U.filter (fun a => a.parent = b)).card : ℝ) ≤
      Nk ^ ((d₁ * h + 4 * ρ * gain) * L + 4 * ε) := by
    have hsub : U.filter (fun a => a.parent = b) ⊆
        S.filter (fun a => a.parent = b ∧ a.gain ≤ h + ρ * gain) := by
      intro a ha
      obtain ⟨ha, hb⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨hUS ha, hb, (hUg a ha).2⟩
    have hh := priority_parent_card_gain_le Nk L W C Mc ν B d₁ ρ gain εin (h + ρ * gain)
      r T lev γ j A H₀ S hN hL hd₁ hS hpriority b (hApos b) (by finiteness)
    exact (show ((U.filter (fun a => a.parent = b)).card : ℝ) ≤
      ((S.filter (fun a => a.parent = b ∧ a.gain ≤ h + ρ * gain)).card : ℝ) from
        by exact_mod_cast Finset.card_le_card hsub).trans
      (hh.trans (Real.rpow_le_rpow_of_exponent_le hN hgexp))
  let n := Fintype.card U
  let e : Fin n ≃ U := (Fintype.equivFin U).symm
  let datum : Fin n → CandidateDatum C := fun a => (e a).val
  have hdmem (a : Fin n) : datum a ∈ U := (e a).property
  have hdinj : Function.Injective datum := fun a a' hh => e.injective (Subtype.ext hh)
  have hsum {M : Type} [AddCommMonoid M] (f : CandidateDatum C → M) :
      (∑ a : Fin n, f (datum a)) = ∑ a ∈ U, f a :=
    (e.sum_comp (fun a : U => f a)).trans (Finset.sum_coe_sort U f)
  refine ⟨i, h, n, (fun a => (datum a).parent), (fun a => (datum a).test),
    (fun a => (datum a).trajectories), (fun a => V (datum a)),
    hi, hgainh, hcap, ⟨z, rfl⟩, hroom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hcU : (U.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_le_card hUS
    simpa only [n, Fintype.card_coe] using hcU.trans hScard
  · exact fun a => hpoint (datum a) (hdmem a)
  · intro a a' hne hp
    exact hpriority _ (hUS (hdmem a)) _ (hUS (hdmem a'))
      (fun hh => hne (hdinj hh)) hp
  · intro b
    have heq : (Finset.univ.filter (fun a : Fin n => (datum a).parent = b)).card =
        (U.filter (fun a => a.parent = b)).card := by
      simp only [Finset.card_filter]
      exact hsum (M := ℕ) (fun a => if a.parent = b then (1 : ℕ) else 0)
    simpa only [heq] using hparent b
  · intro a a' hne hw
    apply countedPacket_disjoint CandidateDatum.trajectories CandidateDatum.test
      (fun a => B (γ a.parent) / K ^ 4) (fun a => j a.parent) (T i)
      (fun a => H (γ a.parent)) (datum a) (datum a')
    exact fun hj => hdisj _ (hdmem a) _ (hdmem a') (fun hh => hne (hdinj hh)) hw hj
  · have hmreal : Nk ^ (-ε) ≤ ∑ a : Fin n, ω (γ (datum a).parent) *
        ((ν (γ (datum a).parent)).prod volume).real (V (datum a)) := by
      rw [hsum (M := ℝ) (fun a => ω (γ a.parent) *
        ((ν (γ a.parent)).prod volume).real (V a))]
      exact hmass
    have hh := ENNReal.ofReal_le_ofReal hmreal
    rw [ofReal_weighted_mass (fun a : Fin n => (ν (γ (datum a).parent)).prod volume)
      (fun a => ω (γ (datum a).parent)) (fun a => V (datum a))
      (fun a => hω _) (fun a => hVfin _)] at hh
    exact hh

end Submission.Obl.k4_quadratic_finite_greedy_cover
