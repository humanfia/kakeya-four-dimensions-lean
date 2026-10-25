import Submission.Obl.k4_horizontal_strict_parameter_step.DurationPreparation
import Submission.Obl.k4_horizontal_strict_parameter_step.ChartPrior

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d50c59d5b1367f287a76eef33f4c400a8e312ee2,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/ChartDuration.lean`.
The namespace and internal imports are changed to o272. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4Homogenization

noncomputable section

/-- Density preparation can retain a specified original discovery event
pointwise, while preserving the same original reference probability. -/
theorem chart_indicator_cutoff_in_support {X : Type*} [MeasurableSpace X]
    (ν lam : Measure X) [IsProbabilityMeasure ν]
    (S : Set X) (hS : MeasurableSet S) (hsupp : ∀ᵐ p ∂lam, p ∈ S)
    {δ K : ℝ} (hδ : 0 < δ) (hK : 0 < K)
    (hdom : lam ≤ ENNReal.ofReal K • ν) (hmass : ENNReal.ofReal δ ≤ lam univ) :
    ∃ E : Set X, MeasurableSet E ∧ E ⊆ S ∧
      ENNReal.ofReal (δ / 2) ≤ lam E ∧
      ENNReal.ofReal (δ / (2 * K)) ≤ ν E ∧
      ENNReal.ofReal (δ / 2) • ν.restrict E ≤ lam := by
  obtain ⟨E, hE, -, hmassE, hprior, hlower, -⟩ :=
    chart_indicator_cutoff ν lam hδ hK hdom hmass
  have hlam : lam (E ∩ S) = lam E := by
    apply measure_congr
    filter_upwards [hsupp] with p hp
    simp only [mem_inter_iff, hp, and_true]
  have hzero : ν (Sᶜ ∩ E) = 0 := by
    have hh := hlower Sᶜ
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hS.compl,
      Measure.restrict_apply hS.compl] at hh
    have hlamzero : lam (Sᶜ ∩ E) = 0 :=
      measure_mono_null inter_subset_left (ae_iff.mp hsupp)
    rw [hlamzero] at hh
    exact (mul_eq_zero.mp (le_antisymm hh bot_le)).resolve_left
      (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hν : ν (E ∩ S) = ν E := by
    apply measure_congr
    have hgood : ∀ᵐ p ∂ν, p ∉ Sᶜ ∩ E := by
      apply ae_iff.mpr
      rw [show {p : X | ¬p ∉ Sᶜ ∩ E} = Sᶜ ∩ E by ext p; simp]
      exact hzero
    filter_upwards [hgood] with p hp
    apply propext
    constructor
    · exact fun he => he.1
    · intro he
      exact ⟨he, by by_contra hn; exact hp ⟨hn, he⟩⟩
  refine ⟨E ∩ S, hE.inter hS, inter_subset_right, hmassE.trans_eq hlam.symm,
    hprior.trans_eq hν.symm, ?_⟩
  exact (smul_le_smul_left (ENNReal.ofReal (δ / 2))
    (Measure.restrict_mono_set ν inter_subset_left)).trans
    (hlower.trans Measure.restrict_le_self)

/-- The original chart prior and its discovered event supply a dense indicator
with earlier duration witnesses in actual Lebesgue time. Every retained point
stays in the discovery event, including its finite child coverage certificates. -/
theorem prepare_chart_duration {α J : Type*} [MeasurableSpace α] [Fintype J]
    (ν : Measure α) [IsProbabilityMeasure ν] (lam : Measure (α × ℝ))
    (S : Set (α × ℝ)) (hS : MeasurableSet S) (hSunit : S ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hsupp : ∀ᵐ p ∂lam, p ∈ S)
    {δ K η : ℝ} (hδ : 0 < δ) (hK : 0 < K) (hη : 0 ≤ η)
    (hloss : K * η ≤ δ / 4)
    (hdom : lam ≤ ENNReal.ofReal K • ν.prod (volume.restrict (Icc (0 : ℝ) 1)))
    (hmass : ENNReal.ofReal δ ≤ lam univ)
    (I : J → Set ℝ) (hI : ∀ j, MeasurableSet (I j)) (hsum : ∑ j, volume (I j) ≤ 1) :
    ∃ E₀ E : Set (α × ℝ), MeasurableSet E₀ ∧ MeasurableSet E ∧
      E ⊆ E₀ ∧ E₀ ⊆ S ∧
      ENNReal.ofReal (δ / 4) ≤ lam E ∧
      ENNReal.ofReal (δ / (4 * K)) ≤ (ν.prod volume) E ∧
      ENNReal.ofReal (δ / 2) • (ν.prod volume).restrict E₀ ≤ lam ∧
      ∀ p ∈ E, ∀ j, p.2 ∈ I j →
        ENNReal.ofReal η * volume (I j) ≤
          incidenceDuration volume (E₀.indicator 1) (I j) p.1 := by
  let τ := volume.restrict (Icc (0 : ℝ) 1)
  have hτ : IsProbabilityMeasure τ := by
    constructor
    simp [τ, Real.volume_Icc]
  letI := hτ
  obtain ⟨E₀, hE₀, hE₀S, hmass₀, -, hlower⟩ :=
    chart_indicator_cutoff_in_support (ν.prod τ) lam S hS hsupp hδ hK hdom hmass
  have href : ν.prod τ = (ν.prod volume).restrict (univ ×ˢ Icc (0 : ℝ) 1) := by
    simpa only [Measure.restrict_univ] using
      (Measure.prod_restrict (μ := ν) (ν := (volume : Measure ℝ)) univ (Icc (0 : ℝ) 1))
  have href₀ : (ν.prod τ).restrict E₀ = (ν.prod volume).restrict E₀ := by
    rw [href]
    exact Measure.restrict_restrict_of_subset (hE₀S.trans hSunit)
  rw [href₀] at hlower
  obtain ⟨E, hE, hsub, homit, hdur⟩ :=
    prepare_duration_witnesses ν volume hE₀ I hI hsum (ENNReal.ofReal η)
  have hdom' : lam ≤ ENNReal.ofReal K • ν.prod volume := by
    rw [href] at hdom
    exact hdom.trans (smul_le_smul_left (ENNReal.ofReal K) Measure.restrict_le_self)
  have hsmall : lam (E₀ \ E) ≤ ENNReal.ofReal (δ / 4) := by
    calc
      _ ≤ ENNReal.ofReal K * (ν.prod volume) (E₀ \ E) := hdom' _
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
      _ ≤ lam E₀ := hmass₀
      _ ≤ lam E + lam (E₀ \ E) := by
        simpa only [inter_eq_right.mpr hsub] using measure_le_inter_add_sdiff lam E₀ E
      _ ≤ _ := add_le_add le_rfl hsmall
  have hprior : ENNReal.ofReal (δ / (4 * K)) ≤ (ν.prod volume) E := by
    rw [show δ / (4 * K) = (δ / 4) / K by ring,
      ENNReal.ofReal_div_of_pos hK,
      ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hK)) ENNReal.ofReal_ne_top]
    exact hlarge.trans ((hdom' E).trans_eq (mul_comm _ _))
  exact ⟨E₀, E, hE₀, hE, hsub, hE₀S, hlarge, hprior, hlower, hdur⟩

end

end Submission.Obl.k4_horizontal_strict_parameter_step
