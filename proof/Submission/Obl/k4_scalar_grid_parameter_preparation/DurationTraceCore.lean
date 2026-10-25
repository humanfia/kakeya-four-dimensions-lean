/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/DurationTraceCore.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.RetainedTraceCap

/-! One common duration mask supplies every coarser fixed-time trace ceiling. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open Submission.Lib.K4Homogenization (durationRetained)
open scoped Classical BigOperators ENNReal

def fineTimeWindow (δ : ℝ) (j : Fin (⌈1 / δ⌉₊ + 1)) : Set ℝ :=
  Set.Icc ((j.val : ℝ) * δ) ((j.val : ℝ) * δ + δ)

theorem measurableSet_fineTimeWindow (δ : ℝ) (j : Fin (⌈1 / δ⌉₊ + 1)) :
    MeasurableSet (fineTimeWindow δ j) := measurableSet_Icc

theorem volume_fineTimeWindow (δ : ℝ) (j : Fin (⌈1 / δ⌉₊ + 1)) :
    volume (fineTimeWindow δ j) = ENNReal.ofReal δ := by
  rw [fineTimeWindow, Real.volume_Icc]
  congr 1
  ring

theorem fineTimeWindow_volume_sum_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∑ j : Fin (⌈1 / δ⌉₊ + 1), volume (fineTimeWindow δ j)) ≤ ENNReal.ofReal 3 := by
  simp only [volume_fineTimeWindow, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hc := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (by positivity : 0 ≤ 1 / δ)) hδ
  have he : (1 / δ + 1) * δ = 1 + δ := by field_simp
  rw [he] at hc
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  linarith

theorem exists_fineTimeWindow_of_mem_unit {δ t : ℝ} (hδ : 0 < δ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : ∃ j, t ∈ fineTimeWindow δ j := by
  have hj : ⌊t / δ⌋₊ ≤ ⌈1 / δ⌉₊ :=
    (Nat.floor_mono (div_le_div_of_nonneg_right ht.2 hδ.le)).trans (Nat.floor_le_ceil _)
  have hlo := (le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg ht.1 hδ.le))
  have hhi := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one (t / δ))
  refine ⟨⟨⌊t / δ⌋₊, Nat.lt_succ_iff.mpr hj⟩, hlo, ?_⟩
  change t ≤ (⌊t / δ⌋₊ : ℝ) * δ + δ
  nlinarith

/-- A single finite family of fine time windows gives a measurable core with
small loss of ORIGINAL incidence mass and a duration floor in every window
containing a retained point. This mask is independent of all later queries. -/
theorem exists_duration_trace_core {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [SFinite ν] (G : α × ℝ → ℝ≥0∞) (hG : Measurable G)
    (E₀ : Set (α × ℝ)) (hE₀ : MeasurableSet E₀)
    (hsupport : (ν.prod volume).withDensity G E₀ᶜ = 0)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) :
    ∃ E : Set (α × ℝ), MeasurableSet E ∧ E ⊆ E₀ ∧
      (ν.prod volume).withDensity G Eᶜ ≤ ENNReal.ofReal (3 * ε) * ν Set.univ ∧
      ∀ j : Fin (⌈1 / δ⌉₊ + 1), ∀ p ∈ E, p.2 ∈ fineTimeWindow δ j →
        p.1 ∈ durationRetained volume G (fineTimeWindow δ j) (ENNReal.ofReal (ε * δ)) := by
  let F : Set (α × ℝ) := ⋃ j : Fin (⌈1 / δ⌉₊ + 1),
    (durationRetained volume G (fineTimeWindow δ j)
      (ENNReal.ofReal ε * volume (fineTimeWindow δ j)))ᶜ ×ˢ fineTimeWindow δ j
  have hFm : MeasurableSet F := MeasurableSet.iUnion fun j =>
    (Submission.Lib.K4Homogenization.measurableSet_durationRetained volume hG _ _).compl.prod
      (measurableSet_fineTimeWindow δ j)
  have hFmass : (ν.prod volume).withDensity G F ≤ ENNReal.ofReal (3 * ε) * ν Set.univ := by
    calc
      _ ≤ (ENNReal.ofReal ε * ∑ j : Fin (⌈1 / δ⌉₊ + 1), volume (fineTimeWindow δ j)) * ν Set.univ :=
        Submission.Lib.K4Homogenization.duration_family_omission_mass_le
          ν volume hG (fineTimeWindow δ) (measurableSet_fineTimeWindow δ) (ENNReal.ofReal ε)
      _ ≤ (ENNReal.ofReal ε * ENNReal.ofReal 3) * ν Set.univ :=
        mul_le_mul (mul_le_mul le_rfl (fineTimeWindow_volume_sum_le hδ hδ1) bot_le bot_le)
          le_rfl bot_le bot_le
      _ = _ := by rw [← ENNReal.ofReal_mul hε]; congr 2; ring
  let E := E₀ \ F
  have hcomp : Eᶜ = E₀ᶜ ∪ F := by
    ext p
    simp only [E, Set.mem_compl_iff, Set.mem_sdiff, Set.mem_union]
    tauto
  refine ⟨E, hE₀.diff hFm, Set.sdiff_subset, ?_, ?_⟩
  · calc
      _ = (ν.prod volume).withDensity G (E₀ᶜ ∪ F) := congrArg _ hcomp
      _ ≤ (ν.prod volume).withDensity G E₀ᶜ + (ν.prod volume).withDensity G F := measure_union_le _ _
      _ = (ν.prod volume).withDensity G F := by rw [hsupport, zero_add]
      _ ≤ _ := hFmass
  · intro j p hp ht
    by_contra hret
    apply hp.2
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_, ht⟩
    change p.1 ∉ durationRetained volume G (fineTimeWindow δ j)
      (ENNReal.ofReal ε * volume (fineTimeWindow δ j))
    rw [volume_fineTimeWindow, ← ENNReal.ofReal_mul hε]
    exact hret

/-- One common retained core gives all coarser scalar snapshot caps at once.
Only the original law, its original prior, and its exact palette event occur in
the estimate. In particular no union over queried spatial scales is needed. -/
theorem exists_uniform_scalar_trace_core {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [SFinite ν] (G : α × ℝ → ℝ≥0∞) (hG : Measurable G)
    (a : α → Fin 5 → ℝ) (ha : Measurable a)
    (E₀ : Set (α × ℝ)) (hE₀ : MeasurableSet E₀)
    (hsupport : (ν.prod volume).withDensity G E₀ᶜ = 0)
    (H δ ε : ℝ) (hH : 1 ≤ H) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε)
    (hcoeff : ∀ p ∈ E₀, ∀ e, |a p.1 e| ≤ H) :
    ∃ E : Set (α × ℝ), MeasurableSet E ∧ E ⊆ E₀ ∧
      (ν.prod volume).withDensity G Eᶜ ≤ ENNReal.ofReal (3 * ε) * ν Set.univ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ (ξ ζ U B : ℝ) (P : Set ℝ) (p : ℝ≥0∞) (qY qX : ℤ),
        δ ≤ ξ → 0 < ζ → 5 * H * δ ≤ ζ → 0 ≤ U → 0 ≤ B → MeasurableSet P →
        (∀ i j b : ℤ, (ν.prod volume).withDensity G
          {ω | (⌊ω.2 / δ⌋ : ℤ) = i ∧ (⌊(a ω.1 0 + ω.2 * a ω.1 1) / δ⌋ : ℤ) = j ∧
            (⌊(a ω.1 2 + ω.2 * a ω.1 3 + ω.2 ^ 2 * a ω.1 4) / ζ⌋ : ℤ) = b ∧ a ω.1 1 ∈ P} ≤
              ENNReal.ofReal (U * δ ^ 2 * B) * p) →
        ν {l | (l, t) ∈ E ∧ a l 0 + t * a l 1 ∈ scalarVelocityBin ξ qY ∧
          a l 2 + t * a l 3 + t ^ 2 * a l 4 ∈ scalarVelocityBin ζ qX ∧ a l 1 ∈ P} ≤
          ENNReal.ofReal (256 * H * U * ξ * B / ε) * p := by
  obtain ⟨E, hEm, hEE₀, hmass, hretain⟩ :=
    exists_duration_trace_core ν G hG E₀ hE₀ hsupport hδ hδ1 hε.le
  refine ⟨E, hEm, hEE₀, hmass, ?_⟩
  intro t ht ξ ζ U B P p qY qX hξ hζ hsmall hU hB hP hcap
  obtain ⟨j, htj⟩ := exists_fineTimeWindow_of_mem_unit hδ ht
  let C : Set α := {l | (l, t) ∈ E₀ ∧ a l 0 + t * a l 1 ∈ scalarVelocityBin ξ qY ∧
    a l 2 + t * a l 3 + t ^ 2 * a l 4 ∈ scalarVelocityBin ζ qX ∧ a l 1 ∈ P}
  have hYm : Measurable fun l => a l 0 + t * a l 1 := by fun_prop
  have hXm : Measurable fun l => a l 2 + t * a l 3 + t ^ 2 * a l 4 := by fun_prop
  have hVm : Measurable fun l => a l 1 := (measurable_pi_apply 1).comp ha
  have hC : MeasurableSet C :=
    (hE₀.preimage (measurable_id.prodMk measurable_const)).inter
      (((measurableSet_scalarVelocityBin ξ qY).preimage hYm).inter
        (((measurableSet_scalarVelocityBin ζ qX).preimage hXm).inter (hP.preimage hVm)))
  have hsub : {l | (l, t) ∈ E ∧ a l 0 + t * a l 1 ∈ scalarVelocityBin ξ qY ∧
      a l 2 + t * a l 3 + t ^ 2 * a l 4 ∈ scalarVelocityBin ζ qX ∧ a l 1 ∈ P} ⊆
      durationRetained volume G (fineTimeWindow δ j) (ENNReal.ofReal (ε * δ)) ∩ C := by
    rintro l ⟨hl, hY, hX, hV⟩
    exact ⟨hretain j (l, t) hl htj, hEE₀ hl, hY, hX, hV⟩
  apply (measure_mono hsub).trans
  exact retained_scalar_trace_prior_cap ν G hG a C hC (fineTimeWindow δ j)
    (measurableSet_fineTimeWindow δ j) P p t ((j.val : ℝ) * δ) ξ ζ δ H U B ε qY qX
    hδ hδ1 hξ hζ hH hU hB hε hsmall ht htj Set.Subset.rfl
    (fun l hl => hcoeff (l, t) hl.1) (fun l hl => hl.2.1)
    (fun l hl => hl.2.2.1) (fun l hl => hl.2.2.2) hcap

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
