import Submission.Obl.k4_horizontal_strict_parameter_step.InstantaneousCaps
import Submission.Obl.k4_horizontal_strict_parameter_step.ChartPrior

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d50c59d5b1367f287a76eef33f4c400a8e312ee2,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/DurationPreparation.lean`.
The namespace and internal imports are changed to o272. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4Homogenization

/-- Pruning short line/time-window pairs keeps an explicit earlier indicator law
as the witness for every duration floor. Later restrictions need not preserve duration. -/
theorem prepare_duration_witnesses {α T J : Type*} [MeasurableSpace α]
    [MeasurableSpace T] [Fintype J] (ν : Measure α) [IsProbabilityMeasure ν]
    (τ : Measure T) [SFinite τ] {E : Set (α × T)} (hE : MeasurableSet E)
    (I : J → Set T) (hI : ∀ j, MeasurableSet (I j))
    (hsum : ∑ j, τ (I j) ≤ 1) (η : ENNReal) :
    ∃ E' : Set (α × T), MeasurableSet E' ∧ E' ⊆ E ∧
      (ν.prod τ) (E \ E') ≤ η ∧
      ∀ p ∈ E', ∀ j, p.2 ∈ I j →
        η * τ (I j) ≤ incidenceDuration τ (E.indicator 1) (I j) p.1 := by
  classical
  have hG : Measurable (E.indicator (1 : α × T → ENNReal)) :=
    measurable_const.indicator hE
  let bad : Set (α × T) := ⋃ j,
    (durationRetained τ (E.indicator 1) (I j) (η * τ (I j)))ᶜ ×ˢ I j
  have hbad : MeasurableSet bad := MeasurableSet.iUnion fun j =>
    (measurableSet_durationRetained τ hG (I j) (η * τ (I j))).compl.prod (hI j)
  refine ⟨E \ bad, hE.diff hbad, sdiff_subset, ?_, ?_⟩
  · have hbound := duration_probability_omission_mass_le ν τ hG I hI hsum η
    rw [withDensity_indicator_one hE, Measure.restrict_apply hbad] at hbound
    apply le_trans (measure_mono ?_) hbound
    intro p hp
    have hb : p ∈ bad := by
      by_contra hn
      exact hp.2 ⟨hp.1, hn⟩
    exact ⟨hb, hp.1⟩
  · rintro p ⟨hpE, hpbad⟩ j hpI
    by_contra h
    apply hpbad
    exact mem_iUnion.2 ⟨j, h, hpI⟩

/-- The density and duration preparations together retain dense weighted mass
and dense indicator mass. All duration witnesses remain in the earlier event `E₀`,
and all instantaneous tests use the unchanged probability prior `ν`. -/
theorem prepare_weighted_duration {α T J : Type*} [MeasurableSpace α]
    [MeasurableSpace T] [Fintype J] (ν : Measure α) [IsProbabilityMeasure ν]
    (τ : Measure T) [IsProbabilityMeasure τ] (lam : Measure (α × T))
    {δ K η : ℝ} (hδ : 0 < δ) (hK : 0 < K) (hη : 0 ≤ η)
    (hloss : K * η ≤ δ / 4) (hle : lam ≤ ENNReal.ofReal K • ν.prod τ)
    (hmass : ENNReal.ofReal δ ≤ lam univ)
    (I : J → Set T) (hI : ∀ j, MeasurableSet (I j))
    (hsum : ∑ j, τ (I j) ≤ 1) :
    ∃ E₀ E : Set (α × T), MeasurableSet E₀ ∧ MeasurableSet E ∧ E ⊆ E₀ ∧
      (ν.prod τ) (E₀ \ E) ≤ ENNReal.ofReal η ∧
      ENNReal.ofReal (δ / 4) ≤ lam E ∧
      ENNReal.ofReal (δ / (4 * K)) ≤ (ν.prod τ) E ∧
      ENNReal.ofReal (δ / 2) • (ν.prod τ).restrict E₀ ≤ lam ∧
      lam.restrict E₀ ≤ ENNReal.ofReal K • (ν.prod τ).restrict E₀ ∧
      ∀ p ∈ E, ∀ j, p.2 ∈ I j →
        ENNReal.ofReal η * τ (I j) ≤ incidenceDuration τ (E₀.indicator 1) (I j) p.1 := by
  obtain ⟨E₀, hE₀, -, hlarge₀, -, hlower, hupper⟩ :=
    chart_indicator_cutoff (ν.prod τ) lam hδ hK hle hmass
  obtain ⟨E, hE, hsub, homit, hdur⟩ :=
    prepare_duration_witnesses ν τ hE₀ I hI hsum (ENNReal.ofReal η)
  have hupperS (S : Set (α × T)) (hS : S ⊆ E₀) :
      lam S ≤ ENNReal.ofReal K * (ν.prod τ) S := by
    have hb := hupper S
    rw [Measure.restrict_eq_self lam hS, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_eq_self (ν.prod τ) hS] at hb
    exact hb
  have hsmall : lam (E₀ \ E) ≤ ENNReal.ofReal (δ / 4) := by
    calc
      _ ≤ ENNReal.ofReal K * (ν.prod τ) (E₀ \ E) := hupperS _ sdiff_subset
      _ ≤ ENNReal.ofReal K * ENNReal.ofReal η := mul_le_mul_right homit _
      _ = ENNReal.ofReal (K * η) := (ENNReal.ofReal_mul hK.le).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hloss
  have hlarge : ENNReal.ofReal (δ / 4) ≤ lam E := by
    apply ENNReal.le_of_add_le_add_right (a := ENNReal.ofReal (δ / 4)) ENNReal.ofReal_ne_top
    calc
      _ = ENNReal.ofReal (δ / 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      _ ≤ lam E₀ := hlarge₀
      _ ≤ lam E + lam (E₀ \ E) := by
        simpa only [inter_eq_right.mpr hsub] using measure_le_inter_add_sdiff lam E₀ E
      _ ≤ _ := add_le_add le_rfl hsmall
  have hprior : ENNReal.ofReal (δ / (4 * K)) ≤ (ν.prod τ) E := by
    rw [show δ / (4 * K) = (δ / 4) / K by ring,
      ENNReal.ofReal_div_of_pos hK,
      ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hK)) ENNReal.ofReal_ne_top]
    exact hlarge.trans ((hupperS E hsub).trans_eq (mul_comm _ _))
  exact ⟨E₀, E, hE₀, hE, hsub, homit, hlarge, hprior,
    hlower.trans Measure.restrict_le_self, hupper, hdur⟩

end Submission.Obl.k4_horizontal_strict_parameter_step
