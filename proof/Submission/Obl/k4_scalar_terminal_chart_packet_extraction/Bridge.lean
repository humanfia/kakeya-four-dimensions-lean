import Mathlib
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.Asymptotic

/-!
# The frozen hypotheses and the conversion

The frozen exact sequence (restricted product laws of tagged priors and time, coefficient
bounds, exact observation densities, typical profiles and the angular cap) supplies every
hypothesis of `packets_of_trueSystems` except the existence of true terminal systems.
Hence the frozen conclusion follows from true terminal systems of every horizon and every
slack exponent at arbitrarily late samples: the version-1 zero horizon `H(E) = 0` of the
paper's Corollary 6.9, in the chart form of Definition 2.8.
-/

namespace Submission.Obl.k4_scalar_terminal_chart_packet_extraction

open MeasureTheory Set Filter
open scoped ENNReal

/-- The restricted incidence law of the frozen statement. -/
noncomputable def incLaw (ν : Measure Coeff) (E : Set (Coeff × ℝ)) : Measure (Coeff × ℝ) :=
  (ν.prod volume).restrict E

lemma incLaw_coef {ν : Measure Coeff} {E : Set (Coeff × ℝ)} {K : ℝ}
    (hb : ∀ᵐ l ∂ν, ∀ e, |l.2 e| ≤ K) : incLaw ν E {p | ∃ e, K < |p.1.2 e|} = 0 := by
  have hν : ν {l : Coeff | ∃ e, K < |l.2 e|} = 0 := by
    rw [ae_iff] at hb
    refine measure_mono_null ?_ hb
    intro l hl
    simp only [Set.mem_ofPred_eq, not_forall, not_le] at hl ⊢
    exact hl
  have h0 : (ν.prod (volume : Measure ℝ)) ({l : Coeff | ∃ e, K < |l.2 e|} ×ˢ (univ : Set ℝ)) =
      0 := by
    rw [Measure.prod_prod, hν, zero_mul]
  refine le_antisymm ?_ bot_le
  calc incLaw ν E {p | ∃ e, K < |p.1.2 e|} ≤
      (ν.prod volume) {p : Coeff × ℝ | ∃ e, K < |p.1.2 e|} := Measure.restrict_le_self _
    _ ≤ (ν.prod volume) ({l : Coeff | ∃ e, K < |l.2 e|} ×ˢ univ) :=
        measure_mono (fun p hp => ⟨hp, trivial⟩)
    _ = 0 := h0

lemma incLaw_point (ν : Measure Coeff) (E : Set (Coeff × ℝ)) (t : ℝ) :
    incLaw ν E (univ ×ˢ {t}) = 0 := by
  have h0 : (ν.prod volume) (univ ×ˢ {t}) = 0 := by
    rw [Measure.prod_prod, Real.volume_singleton, mul_zero]
  exact measure_mono_null le_rfl
    (le_antisymm ((Measure.restrict_le_self (univ ×ˢ {t})).trans h0.le) bot_le)

lemma incLaw_univ_le {ν : Measure Coeff} [IsProbabilityMeasure ν] {E : Set (Coeff × ℝ)}
    (hE : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) : incLaw ν E univ ≤ 1 := by
  unfold incLaw
  rw [Measure.restrict_apply_univ]
  calc (ν.prod volume) E ≤ (ν.prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := measure_mono hE
    _ = 1 := by rw [Measure.prod_prod, measure_univ, Real.volume_Icc]; simp

/-- **The frozen conclusion from true terminal systems.** The hypotheses are those of the
frozen statement that the conversion uses (with the incidence laws `incLaw (ν k γ) (E k γ)`
and the profile value `fL = f L`); the additional hypothesis `hsys` is the version-1 zero
horizon in chart form. -/
theorem frozen_of_trueSystems
    (N K : ℕ → ℝ) (hN2 : ∀ k, 2 ≤ N k) (hNtop : Tendsto N atTop atTop)
    (hK1 : ∀ k, 1 ≤ K k) (hKsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    {L S U : ℝ} (hL : 0 < L) (hS : 0 < S) (hU : 0 < U)
    (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → Measure Coeff)
    (E : (k : ℕ) → Fin (W k) → Set (Coeff × ℝ))
    (g : (k : ℕ) → Fin (W k) → ℝ → (Fin 2 → ℝ) × ℤ → ℝ≥0∞)
    (G : (k : ℕ) → Fin (W k) → ℝ → ((Fin 2 → ℝ) × ℤ) × ℤ → ℝ≥0∞) (fL : ℝ)
    (hprob : ∀ k γ, IsProbabilityMeasure (ν k γ))
    (hbd : ∀ k γ, ∀ᵐ l ∂ν k γ, ∀ e, |l.2 e| ≤ K k)
    (hEsub : ∀ k γ, E k γ ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hg : ∀ k γ, Measurable (g k γ L) ∧ Measure.map (obsL (N k ^ (-L)))
      (incLaw (ν k γ) (E k γ)) = (volume.prod Measure.count).withDensity (g k γ L))
    (hG : ∀ k γ u, 0 < u → u ≤ U → Measurable (G k γ u) ∧
      Measure.map (obsG (N k ^ (-L)) (N k ^ (-u))) (incLaw (ν k γ) (E k γ)) =
        ((volume.prod Measure.count).prod Measure.count).withDensity (G k γ u))
    (htyp : ∀ τ : ℝ, 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      (∑ γ, ENNReal.ofReal (ω k γ) * incLaw (ν k γ) (E k γ)
        {p | g k γ L (obsL (N k ^ (-L)) p) < ENNReal.ofReal (N k ^ (-fL - τ)) ∨
          ENNReal.ofReal (N k ^ (-fL + τ)) < g k γ L (obsL (N k ^ (-L)) p)}) ≤
        ENNReal.ofReal (N k ^ (-c)))
    (hang : ∀ u τ : ℝ, 0 < u → u ≤ U → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      (∑ γ, ENNReal.ofReal (ω k γ) * incLaw (ν k γ) (E k γ)
        {p | ENNReal.ofReal (N k ^ (-fL - S * u + τ)) <
          G k γ u (obsG (N k ^ (-L)) (N k ^ (-u)) p)}) ≤ ENNReal.ofReal (N k ^ (-c)))
    (hsys : ∀ h κ : ℝ, 0 < h → 0 < κ → ∃ᶠ k in atTop,
      HasTrueSystem (N k) (W k) (ω k) (fun γ => incLaw (ν k γ) (E k γ)) L fL h (N k ^ κ)) :
    ∀ h ε : ℝ, 0 < h → 0 < ε → ∃ᶠ k in atTop,
      HasPackets (N k) (W k) (ω k) (fun γ => incLaw (ν k γ) (E k γ)) L fL h ε := by
  refine packets_of_trueSystems N K hN2 hNtop hK1 hKsub hL.le hS hU W ω
    (fun k γ => incLaw (ν k γ) (E k γ)) (fun k γ => incLaw_coef (hbd k γ))
    (fun k γ t => incLaw_point _ _ t)
    (fun k γ => by
      have := hprob k γ
      exact ne_top_of_le_ne_top ENNReal.one_ne_top (incLaw_univ_le (hEsub k γ)))
    (fun k γ => g k γ L) hg G hG ?_ hang hsys
  intro τ hτ
  obtain ⟨c, hc, hev⟩ := htyp τ hτ
  refine ⟨c, hc, hev.mono fun k hk => le_trans ?_ hk⟩
  gcongr with γ
  exact fun hp => Or.inr hp

end Submission.Obl.k4_scalar_terminal_chart_packet_extraction
