/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/TimeMarginalFloor.lean`. Original attributions are retained below. -/
/- Adapted from this LOT tree, o202, session x0698, commit aacc14fa,
   `Submission/Obl/k4_horizontal_subcritical_rate_candidates/TimeMarginalFloor.lean`. Original imports of accepted libraries are retained. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.SharedTimePolynomial

/-! Produce the time-marginal floor used in the shared-polynomial selection. -/

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open MeasureTheory Set

/-- A Hahn set retains half the mass while dominating half the prescribed
mass times a reference measure of total mass at most one. -/
lemma exists_half_mass_floor {X : Type*} [MeasurableSpace X]
    (σ γ : Measure X) [IsFiniteMeasure σ] [IsFiniteMeasure γ]
    {m : ℝ} (hm : 0 ≤ m) (hγ : γ univ ≤ 1)
    (hmass : ENNReal.ofReal m ≤ σ univ) :
    ∃ T : Set X, MeasurableSet T ∧ ENNReal.ofReal (m / 2) ≤ σ T ∧
      ∀ U : Set X, MeasurableSet U → U ⊆ T →
        ENNReal.ofReal (m / 2) * γ U ≤ σ U := by
  exact Submission.Lib.K4TimeMarginalRestoration.exists_half_mass_floor σ γ hm hγ hmass

/-- The paired event itself supplies a substantial set of times on which
every time restriction has a uniform original-law lower mass bound. -/
lemma exists_paired_time_floor {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (ρ : Measure (α × ℝ))
    {C m : ℝ} (hm : 0 ≤ m)
    (hdom : ρ ≤ ENNReal.ofReal C • (ν.prod volume))
    {E : Set (α × ℝ)} (_hE : MeasurableSet E)
    (hmass : ENNReal.ofReal m ≤ ρ E) (hsub : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    ∃ T₀ : Set ℝ, MeasurableSet T₀ ∧ T₀ ⊆ Icc (0 : ℝ) 1 ∧
      ENNReal.ofReal (m / 2) ≤ ρ (E ∩ (univ ×ˢ T₀)) ∧
      ∀ T : Set ℝ, MeasurableSet T → T ⊆ T₀ →
        ENNReal.ofReal (m / 2) * volume T ≤ ρ (E ∩ (univ ×ˢ T)) := by
  exact Submission.Lib.K4TimeMarginalRestoration.exists_paired_time_floor
    ν ρ hm hdom _hE hmass hsub

/-- Shared-polynomial restoration from the paired mass and domination alone;
the lower time-marginal density is obtained by a Hahn decomposition. -/
lemma exists_shared_time_polynomial_of_mass {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (ρ : Measure (α × ℝ))
    (b : α → Fin 3 → ℝ) (G : ℝ → ℝ)
    {C m K δ : ℝ} (hC : 0 < C) (hm : 0 < m) (hmC : m ≤ C)
    (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hdom : ρ ≤ ENNReal.ofReal C • (ν.prod volume))
    {E : Set (α × ℝ)} (hE : MeasurableSet E)
    (hmass : ENNReal.ofReal m ≤ ρ E) (hsub : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hG : ∀ p ∈ E, |G p.2| ≤ K)
    (hfit : ∀ p ∈ E, |(quadraticTimePolynomial (b p.1)).eval p.2 - G p.2| ≤ δ) :
    ∃ l : α, (∀ i, |b l i| ≤ 17 * (96 * C / m) ^ 2 * (K + δ)) ∧
      ENNReal.ofReal (m ^ 2 / (8 * C)) ≤
        ρ {p | p ∈ E ∧ |(quadraticTimePolynomial (b l)).eval p.2 - G p.2| ≤ δ} := by
  let G' : ℝ → ℝ := fun t => max (-K) (min K (G t))
  have hG' (t : ℝ) : |G' t| ≤ K := by
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hG_eq (p : α × ℝ) (hp : p ∈ E) : G' p.2 = G p.2 := by
    have hb := abs_le.mp (hG p hp)
    exact (congrArg (max (-K)) (min_eq_right hb.2)).trans (max_eq_right hb.1)
  obtain ⟨T₀, hT₀, hTI, hmassT, hfloor⟩ :=
    exists_paired_time_floor ν ρ hm.le hdom hE hmass hsub
  let E' := E ∩ (univ ×ˢ T₀)
  have hE' : MeasurableSet E' := hE.inter (MeasurableSet.univ.prod hT₀)
  have hsub' : E' ⊆ univ ×ˢ (T₀ ∩ Icc (0 : ℝ) 1) := by
    intro p hp
    exact ⟨mem_univ _, hp.2.2, (hsub hp.1).2⟩
  have hfloor' (T : Set ℝ) (hT : MeasurableSet T) (hTT : T ⊆ T₀) :
      ENNReal.ofReal (m / 2) * volume T ≤ ρ (E' ∩ (univ ×ˢ T)) := by
    have heq : E' ∩ (univ ×ˢ T) = E ∩ (univ ×ˢ T) := by
      ext p
      constructor
      · exact fun hp => ⟨hp.1.1, hp.2⟩
      · exact fun hp => ⟨⟨hp.1, mem_univ _, hTT hp.2.2⟩, hp.2⟩
    rw [heq]
    exact hfloor T hT hTT
  obtain ⟨l, hcoeff, hmassl⟩ := exists_shared_time_polynomial (m := m / 2) (c := m / 2) ν ρ b G' hC
    (half_pos hm) (by linarith) (by positivity) hK hδ hdom hE' hmassT hsub'
    hfloor' (fun t _ => hG' t) (fun p hp => by
      simpa only [hG_eq p hp.1] using hfit p hp.1)
  have hratio : (48 : ℝ) * C / (m / 2) = 96 * C / m := by ring
  have hmassEq : (m / 2) * (m / 2) / (2 * C) = m ^ 2 / (8 * C) := by ring
  refine ⟨l, ?_, ?_⟩
  · intro i
    simpa only [hratio] using hcoeff i
  · rw [← hmassEq]
    refine hmassl.trans (measure_mono ?_)
    intro p hp
    exact ⟨hp.1.1, by simpa only [hG_eq p hp.1.1] using hp.2⟩

end Submission.Obl.k4_subcritical_corrected_scalar_charts
