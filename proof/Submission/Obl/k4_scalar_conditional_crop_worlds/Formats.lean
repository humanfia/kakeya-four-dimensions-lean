import Submission.Obl.k4_scalar_conditional_crop_worlds.Definitions

open MeasureTheory Set

namespace Submission.Obl.k4_scalar_conditional_crop_worlds

noncomputable section

/-- The finite density representation required of a single world's prior. -/
def PriorData (R : ℝ) (D : ℕ) (ν : Measure Line) : Prop :=
  ∃ n : ℕ, (n : ℝ) ≤ R ∧ ∃ (h : Fin n → ℝ) (i : Fin n → ℕ) (B : Fin n → Set Coeff),
    (∀ j, 0 ≤ h j ∧ h j ≤ R ∧ (i j : ℝ) ≤ R ∧ Format 5 R D (B j) ∧
      ∀ b ∈ B j, ∀ e, |b e| ≤ R) ∧
    ν = ∑ j, ENNReal.ofReal (h j) • Measure.map (fun b => (i j, b)) (volume.restrict (B j))

/-- The finite sign representation and label bound required of a single world's event. -/
def EventData (R : ℝ) (D : ℕ) (E : Set State) : Prop :=
  MeasurableSet E ∧ E ⊆ univ ×ˢ Icc (0 : ℝ) 1 ∧
    (∀ p ∈ E, (p.1.1 : ℝ) ≤ R) ∧
    ∀ i : ℕ, Format 6 R D {b : Fin 6 → ℝ | ((i, fun e : Fin 5 => b e.castSucc), b 5) ∈ E}

/-- The single-world conjunct of the frozen world format. -/
def WorldData (R : ℝ) (D : ℕ) (K : ℝ) (ν : Measure Line) (E : Set State) : Prop :=
  IsProbabilityMeasure ν ∧ PriorData R D ν ∧ (∀ᵐ l ∂ν, ∀ e, |l.2 e| ≤ K) ∧ EventData R D E

lemma Format.mono {n D D' : ℕ} {R R' : ℝ} {S : Set (Fin n → ℝ)}
    (h : Format n R D S) (hR : R ≤ R') (hD : D ≤ D') : Format n R' D' S := by
  obtain ⟨k, hk, p, hp, T, hT⟩ := h
  exact ⟨k, hk.trans hR, p, fun j => ⟨(hp j).1.trans hD, fun b => ((hp j).2 b).trans hR⟩, T, hT⟩

lemma PriorData.mono {R R' : ℝ} {D D' : ℕ} {ν : Measure Line}
    (h : PriorData R D ν) (hR : R ≤ R') (hD : D ≤ D') : PriorData R' D' ν := by
  obtain ⟨n, hn, c, i, B, hB, hν⟩ := h
  refine ⟨n, hn.trans hR, c, i, B, fun j => ?_, hν⟩
  obtain ⟨hc0, hc, hi, hF, hb⟩ := hB j
  exact ⟨hc0, hc.trans hR, hi.trans hR, hF.mono hR hD, fun b hbB e => (hb b hbB e).trans hR⟩

lemma EventData.mono {R R' : ℝ} {D D' : ℕ} {E : Set State}
    (h : EventData R D E) (hR : R ≤ R') (hD : D ≤ D') : EventData R' D' E := by
  obtain ⟨hm, hs, hi, hF⟩ := h
  exact ⟨hm, hs, fun p hp => (hi p hp).trans hR, fun i => (hF i).mono hR hD⟩

lemma WorldData.mono {R R' K K' : ℝ} {D D' : ℕ} {ν : Measure Line} {E : Set State}
    (h : WorldData R D K ν E) (hR : R ≤ R') (hD : D ≤ D') (hK : K ≤ K') :
    WorldData R' D' K' ν E := by
  obtain ⟨hpr, hP, hb, hE⟩ := h
  exact ⟨hpr, hP.mono hR hD, hb.mono (fun l hl e => (hl e).trans hK), hE.mono hR hD⟩

lemma worldFormat_of_data (N K : ℕ → ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → Measure Line)
    (E : (k : ℕ) → Fin (W k) → Set State) (M D : ℕ) (hM : 1 ≤ M) (hD : 1 ≤ D)
    (hcount : ∀ k, (W k : ℝ) ≤ N k ^ (M : ℝ))
    (hω0 : ∀ k γ, 0 ≤ ω k γ) (hω1 : ∀ k, ∑ γ, ω k γ = 1)
    (hworld : ∀ k γ, WorldData (N k ^ (M : ℝ)) D (K k) (ν k γ) (E k γ))
    (hmass : ∀ k, ENNReal.ofReal ((K k)⁻¹) ≤
      ∑ γ, ENNReal.ofReal (ω k γ) * selected (ν k γ) (E k γ) univ) :
    WorldFormat N K W ω ν E := by
  exact ⟨M, D, hM, hD, fun k => ⟨hcount k, hω0 k, hω1 k, hworld k, hmass k⟩⟩

end

end Submission.Obl.k4_scalar_conditional_crop_worlds
