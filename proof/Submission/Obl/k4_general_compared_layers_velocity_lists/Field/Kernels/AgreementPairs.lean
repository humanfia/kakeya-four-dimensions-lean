-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Kernels.AgreementPairs; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254 (k4_general_parent_wide_layer_candidates), session x0900:
convenience forms of `measurable_consensus_of_pair_mass`, which is ported in
`PairConsensus.lean` from this LOT tree's obligation o247, branch x0870 (session x0870's work). -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Kernels.PairConsensus

/-!
# Consensus from pair-disagreement mass, in the forms used downstream

Let `θ` be a finite measure on `Ω`, `state : Ω → Q` a finite state and `entry : Ω → ι` a finite
entry, each with measurable fibers, and `R : Q → ι → ι → Prop` a relation. The conditional
redraw `statePair θ state` draws two incidences independently inside one state. If the pairs
whose entries disagree, `{p | ¬R (state p.1) (entry p.1) (entry p.2)}`, have mass `D`, there
are a center entry per state and a measurable `H` on which every incidence agrees with the
center of its state, which keeps in every state either nothing or at least half of its mass,
and loses `θ Hᶜ ≤ 2 D`.

* `consensus_of_pair_mass_real`: `measurable_consensus_of_pair_mass` with measurable fibers
  only (no measurable structure on `Q` or `ι` is needed);
* `consensus_of_pair_mass`: the same in extended reals;
* `consensus_of_pair_mass_le`: for any bound `D ≤ ε`, `θ univ ≤ θ H + 2 ε` and `θ Hᶜ ≤ 2 ε`;
* conversions: `statePair_ne_top`, `ofReal_statePair_real`, `half_real_iff` (the half-state
  alternative in real and in extended-real units), `measure_compl_le_of_univ_le`,
  `measureReal_compl_le_of_univ_le` and `restrict_half_states` (the half-state alternative for
  `θ.restrict H`, the form `half_state_palette` and `half_state_palette_ennreal` take).
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists.Kernels

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-! ### Conversions -/

/-- The conditional redraw of a finite measure gives every set finite mass. -/
theorem statePair_ne_top {Ω Q : Type*} [MeasurableSpace Ω] [Fintype Q]
    (θ : Measure Ω) [IsFiniteMeasure θ] (state : Ω → Q)
    (hs : ∀ q, MeasurableSet (state ⁻¹' {q})) (S : Set (Ω × Ω)) :
    statePair θ state S ≠ ∞ :=
  haveI := statePair_finite θ state hs
  measure_ne_top _ S

/-- The real pair mass of the conditional redraw recovers its extended-real mass. -/
theorem ofReal_statePair_real {Ω Q : Type*} [MeasurableSpace Ω] [Fintype Q]
    (θ : Measure Ω) [IsFiniteMeasure θ] (state : Ω → Q)
    (hs : ∀ q, MeasurableSet (state ⁻¹' {q})) (S : Set (Ω × Ω)) :
    ENNReal.ofReal ((statePair θ state).real S) = statePair θ state S :=
  ENNReal.ofReal_toReal (statePair_ne_top θ state hs S)

/-- The half-state alternative ("nothing, or at least half") in real and in extended-real
units, for a finite measure. -/
theorem half_real_iff {Ω : Type*} [MeasurableSpace Ω] (θ : Measure Ω) [IsFiniteMeasure θ]
    (A S : Set Ω) :
    (θ.real A = 0 ∨ θ.real S / 2 ≤ θ.real A) ↔ (θ A = 0 ∨ θ S ≤ 2 * θ A) := by
  have hA : θ A ≠ ∞ := measure_ne_top θ A
  have h2A : 2 * θ A ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top hA
  have hle : θ.real S / 2 ≤ θ.real A ↔ θ S ≤ 2 * θ A := by
    rw [← ENNReal.toReal_le_toReal (measure_ne_top θ S) h2A, ENNReal.toReal_mul,
      ENNReal.toReal_ofNat, ← measureReal_def, ← measureReal_def]
    constructor <;> intro h <;> linarith
  rw [measureReal_eq_zero_iff hA, hle]

/-- A total-mass inequality `θ univ ≤ θ H + ε` bounds the mass lost outside `H`. -/
theorem measure_compl_le_of_univ_le {Ω : Type*} [MeasurableSpace Ω] (θ : Measure Ω)
    [IsFiniteMeasure θ] {H : Set Ω} (hH : MeasurableSet H) {ε : ℝ≥0∞}
    (h : θ univ ≤ θ H + ε) : θ Hᶜ ≤ ε := by
  have h' : θ H + θ Hᶜ ≤ θ H + ε := by rwa [measure_add_measure_compl hH]
  exact (ENNReal.add_le_add_iff_left (measure_ne_top θ H)).mp h'

/-- The real form of `measure_compl_le_of_univ_le`. -/
theorem measureReal_compl_le_of_univ_le {Ω : Type*} [MeasurableSpace Ω] (θ : Measure Ω)
    [IsFiniteMeasure θ] {H : Set Ω} (hH : MeasurableSet H) {ε : ℝ}
    (h : θ.real univ ≤ θ.real H + ε) : θ.real Hᶜ ≤ ε := by
  rw [measureReal_compl hH]
  linarith

/-- The half-state alternative of a consensus set `H`, restated for the restricted measure
`θ.restrict H` (which is `≤ θ` by `Measure.restrict_le_self`): the form of the hypothesis
`hhalf` of `half_state_palette` and `half_state_palette_ennreal`. -/
theorem restrict_half_states {Ω Q : Type*} [MeasurableSpace Ω] (θ : Measure Ω)
    (state : Ω → Q) {H : Set Ω} (hH : MeasurableSet H)
    (hhalf : ∀ q, θ.real (H ∩ state ⁻¹' {q}) = 0 ∨
      θ.real (state ⁻¹' {q}) / 2 ≤ θ.real (H ∩ state ⁻¹' {q})) :
    ∀ q, (θ.restrict H).real (state ⁻¹' {q}) = 0 ∨
      θ.real (state ⁻¹' {q}) / 2 ≤ (θ.restrict H).real (state ⁻¹' {q}) := by
  intro q
  rw [measureReal_restrict_apply' hH, inter_comm]
  exact hhalf q

/-! ### Consensus -/

/-- **Consensus from pair-disagreement mass** (`measurable_consensus_of_pair_mass`), with
measurable fibers of `state` and `entry` only. -/
theorem consensus_of_pair_mass_real {Ω Q ι : Type*} [MeasurableSpace Ω]
    [Fintype Q] [Fintype ι] [Nonempty ι]
    (θ : Measure Ω) [IsFiniteMeasure θ] (state : Ω → Q) (entry : Ω → ι)
    (hs : ∀ q, MeasurableSet (state ⁻¹' {q})) (hi : ∀ i, MeasurableSet (entry ⁻¹' {i}))
    (R : Q → ι → ι → Prop) :
    ∃ (center : Q → ι) (H : Set Ω), MeasurableSet H ∧
      (∀ ω ∈ H, R (state ω) (entry ω) (center (state ω))) ∧
      (∀ q, θ.real (H ∩ state ⁻¹' {q}) = 0 ∨
        θ.real (state ⁻¹' {q}) / 2 ≤ θ.real (H ∩ state ⁻¹' {q})) ∧
      θ.real univ ≤ θ.real H +
        2 * (statePair θ state).real {p | ¬R (state p.1) (entry p.1) (entry p.2)} := by
  let : MeasurableSpace Q := ⊤
  let : MeasurableSpace ι := ⊤
  have : MeasurableSingletonClass Q := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have : MeasurableSingletonClass ι := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  exact measurable_consensus_of_pair_mass θ state entry (measurable_to_countable' hs)
    (measurable_to_countable' hi) R

/-- **Consensus from pair-disagreement mass**, extended-real form: a center entry per state
and a measurable `H` on which every incidence agrees with the center of its state, keeping in
every state nothing or at least half of its mass, with
`θ univ ≤ θ H + 2 · statePair θ state {disagreeing pairs}`. -/
theorem consensus_of_pair_mass {Ω Q ι : Type*} [MeasurableSpace Ω]
    [Fintype Q] [Fintype ι] [Nonempty ι]
    (θ : Measure Ω) [IsFiniteMeasure θ] (state : Ω → Q) (entry : Ω → ι)
    (hs : ∀ q, MeasurableSet (state ⁻¹' {q})) (hi : ∀ i, MeasurableSet (entry ⁻¹' {i}))
    (R : Q → ι → ι → Prop) :
    ∃ (center : Q → ι) (H : Set Ω), MeasurableSet H ∧
      (∀ ω ∈ H, R (state ω) (entry ω) (center (state ω))) ∧
      (∀ q, θ (H ∩ state ⁻¹' {q}) = 0 ∨ θ (state ⁻¹' {q}) ≤ 2 * θ (H ∩ state ⁻¹' {q})) ∧
      θ univ ≤ θ H + 2 * statePair θ state {p | ¬R (state p.1) (entry p.1) (entry p.2)} := by
  obtain ⟨center, H, hH, hR, hhalf, hmass⟩ :=
    consensus_of_pair_mass_real θ state entry hs hi R
  refine ⟨center, H, hH, hR, fun q => (half_real_iff θ _ _).mp (hhalf q), ?_⟩
  have hD := statePair_ne_top θ state hs {p | ¬R (state p.1) (entry p.1) (entry p.2)}
  have h2D : 2 * statePair θ state {p | ¬R (state p.1) (entry p.1) (entry p.2)} ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top hD
  rw [← ENNReal.toReal_le_toReal (measure_ne_top θ univ)
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top θ H, h2D⟩),
    ENNReal.toReal_add (measure_ne_top θ H) h2D, ENNReal.toReal_mul, ENNReal.toReal_ofNat]
  exact hmass

/-- **Consensus from pair-disagreement mass**, with any extended-real bound `ε` of the mass of
the disagreeing pairs: the consensus set loses `θ Hᶜ ≤ 2 ε`. -/
theorem consensus_of_pair_mass_le {Ω Q ι : Type*} [MeasurableSpace Ω]
    [Fintype Q] [Fintype ι] [Nonempty ι]
    (θ : Measure Ω) [IsFiniteMeasure θ] (state : Ω → Q) (entry : Ω → ι)
    (hs : ∀ q, MeasurableSet (state ⁻¹' {q})) (hi : ∀ i, MeasurableSet (entry ⁻¹' {i}))
    (R : Q → ι → ι → Prop) (ε : ℝ≥0∞)
    (hε : statePair θ state {p | ¬R (state p.1) (entry p.1) (entry p.2)} ≤ ε) :
    ∃ (center : Q → ι) (H : Set Ω), MeasurableSet H ∧
      (∀ ω ∈ H, R (state ω) (entry ω) (center (state ω))) ∧
      (∀ q, θ (H ∩ state ⁻¹' {q}) = 0 ∨ θ (state ⁻¹' {q}) ≤ 2 * θ (H ∩ state ⁻¹' {q})) ∧
      θ univ ≤ θ H + 2 * ε ∧ θ Hᶜ ≤ 2 * ε := by
  obtain ⟨center, H, hH, hR, hhalf, hmass⟩ := consensus_of_pair_mass θ state entry hs hi R
  have h : θ univ ≤ θ H + 2 * ε := hmass.trans (by gcongr)
  exact ⟨center, H, hH, hR, hhalf, h, measure_compl_le_of_univ_le θ hH h⟩

/-- **Consensus from pair-disagreement mass**, with a real bound `ε` of the real mass of the
disagreeing pairs; the half-state alternative is also given for `θ.restrict H`, ready for
`half_state_palette`. -/
theorem consensus_of_pair_mass_real_le {Ω Q ι : Type*} [MeasurableSpace Ω]
    [Fintype Q] [Fintype ι] [Nonempty ι]
    (θ : Measure Ω) [IsFiniteMeasure θ] (state : Ω → Q) (entry : Ω → ι)
    (hs : ∀ q, MeasurableSet (state ⁻¹' {q})) (hi : ∀ i, MeasurableSet (entry ⁻¹' {i}))
    (R : Q → ι → ι → Prop) (ε : ℝ)
    (hε : (statePair θ state).real {p | ¬R (state p.1) (entry p.1) (entry p.2)} ≤ ε) :
    ∃ (center : Q → ι) (H : Set Ω), MeasurableSet H ∧
      (∀ ω ∈ H, R (state ω) (entry ω) (center (state ω))) ∧
      (∀ q, θ.real (H ∩ state ⁻¹' {q}) = 0 ∨
        θ.real (state ⁻¹' {q}) / 2 ≤ θ.real (H ∩ state ⁻¹' {q})) ∧
      (∀ q, (θ.restrict H).real (state ⁻¹' {q}) = 0 ∨
        θ.real (state ⁻¹' {q}) / 2 ≤ (θ.restrict H).real (state ⁻¹' {q})) ∧
      θ.real univ ≤ θ.real H + 2 * ε ∧ θ.real Hᶜ ≤ 2 * ε := by
  obtain ⟨center, H, hH, hR, hhalf, hmass⟩ :=
    consensus_of_pair_mass_real θ state entry hs hi R
  have h : θ.real univ ≤ θ.real H + 2 * ε := by linarith
  exact ⟨center, H, hH, hR, hhalf, restrict_half_states θ state hH hhalf, h,
    measureReal_compl_le_of_univ_le θ hH h⟩

end

end Submission.Obl.k4_general_compared_layers_velocity_lists.Kernels
