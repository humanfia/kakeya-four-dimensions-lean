-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o107, session x0735, commit cc2492748f08.
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/ContinuousLikelihoodPreparation.lean.
import Submission.Obl.k4_finite_affine_parent_sources.SubpowerLikelihood
import Submission.Obl.k4_finite_affine_parent_sources.FiniteCodeTransport

/-! The finite likelihood deletion pulls back to the original continuous
incidence law. All subsequent submeasures keep the same joint caps against
the original history masses and the original parent palettes. -/

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

open Finset Set MeasureTheory
open scoped ENNReal
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

/-- Code masses of a submeasure of a retained event are dominated by the
literal restriction of the original finite table. -/
theorem finite_code_weights_le_restriction
    {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (μ : Measure Y) [IsFiniteMeasure μ] (code : Y → Fin n) (hcode : Measurable code)
    (S : Finset (Fin n)) (ρ : Measure Y)
    (hρ : ρ ≤ μ.restrict {y | code y ∈ S}) :
    ∀ i, ρ.real (code ⁻¹' {i}) ≤ if i ∈ S then μ.real (code ⁻¹' {i}) else 0 := by
  intro i
  have hm : MeasurableSet (code ⁻¹' {i}) := hcode (measurableSet_singleton i)
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi]
    exact ENNReal.toReal_mono (measure_ne_top μ _) ((hρ.trans Measure.restrict_le_self) _)
  · rw [ite_eq_right hi]
    have hdisj : code ⁻¹' {i} ∩ {y | code y ∈ S} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro y ⟨hy, hyS⟩
      have hci : code y = i := hy
      exact hi (hci ▸ hyS)
    have hz : ρ (code ⁻¹' {i}) = 0 := by
      apply le_antisymm _ bot_le
      calc
        _ ≤ μ.restrict {y | code y ∈ S} (code ⁻¹' {i}) := hρ _
        _ = 0 := by rw [Measure.restrict_apply hm, hdisj, measure_empty]
    simp only [measureReal_def, hz, ENNReal.toReal_zero, le_refl]

/-- A measurable deletion for the original probability law, with no change
of law in any reference denominator. The same numerator ceiling holds for
every later continuous submeasure. -/
theorem original_balanced_likelihood
    {Y H Z : Type*} [MeasurableSpace Y] [Fintype H] [DecidableEq H]
    [Fintype Z] [DecidableEq Z] {n : ℕ}
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (code : Y → Fin n) (hcode : Measurable code)
    (coarse fine : Fin n → H) (parent : H → H) (palette : Fin n → Z)
    (hrefine : ∀ i, coarse i = parent (fine i))
    (N B : ℝ) (hN : 1 < N) (hB : 0 < B)
    (hinfo : negCondEnt (fun i => μ.real (code ⁻¹' {i})) palette fine -
      negCondEnt (fun i => μ.real (code ⁻¹' {i})) palette coarse + 1 ≤ B) :
    ∃ E : Set Y, MeasurableSet E ∧
      1 - Real.sqrt (B / Real.log N) ≤ μ.real E ∧
      ∀ ρ : Measure Y, ρ ≤ μ.restrict E → ∀ h z,
        ρ.real {y | (fine (code y), palette (code y)) = (h, z)} ≤
          N ^ Real.sqrt (B / Real.log N) * μ.real {y | fine (code y) = h} *
            (μ.real {y | (coarse (code y), palette (code y)) = (parent h, z)} /
              μ.real {y | coarse (code y) = parent h}) := by
  let P : Fin n → ℝ := fun i => μ.real (code ⁻¹' {i})
  have hP : ∀ i, 0 ≤ P i := fun _ => ENNReal.toReal_nonneg
  have hP1 : ∑ i, P i = 1 :=
    Submission.Obl.k4_matching_cofinal_palette_selection.sum_atomMass_eq_one μ code hcode
  obtain ⟨S, hmass, hcap⟩ := finite_balanced_likelihood P hP hP1
    coarse fine parent palette hrefine N B hN hB hinfo
  let E : Set Y := {y | code y ∈ S}
  have hE : MeasurableSet E := hcode (S.finite_toSet.measurableSet)
  refine ⟨E, hE, ?_, ?_⟩
  · have hs := Submission.Obl.k4_matching_cofinal_palette_selection.sum_atomMass μ code hcode S
    exact hmass.trans_eq hs
  · intro ρ hρ h z
    have : IsFiniteMeasure ρ := isFiniteMeasure_of_le μ (hρ.trans Measure.restrict_le_self)
    have h := hcap (fun i => ρ.real (code ⁻¹' {i}))
      (finite_code_weights_le_restriction μ code hcode S ρ hρ) h z
    unfold historyPalette at h
    rw [finite_code_fiber_mass ρ code hcode, finite_code_fiber_mass μ code hcode,
      finite_code_fiber_mass μ code hcode, finite_code_fiber_mass μ code hcode] at h
    exact h

/-- One original probability law supplies both the low-information window
and its balanced likelihood deletion. The entire entropy budget comes from
the small velocity alphabet inside the initial history fibers. -/
theorem original_balanced_likelihood_window
    {Y H Z : Type*} [MeasurableSpace Y] [Fintype H] [DecidableEq H]
    [Fintype Z] [DecidableEq Z] {n M m : ℕ}
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (code : Y → Fin n) (hcode : Measurable code)
    (history : ℕ → Fin n → H) (parent : ℕ → H → H) (palette : Fin n → Z)
    (hrefine : ∀ i e, history i e = parent i (history (i + 1) e))
    (hM : 1 ≤ M) (hm : 0 < m)
    (hcard : ∀ e,
      ((Finset.univ.filter (fun e' => 0 < μ.real (code ⁻¹' {e'}) ∧
        history 0 e' = history 0 e)).image palette).card ≤ M)
    (N : ℝ) (hN : 1 < N) :
    ∃ i < m, ∃ E : Set Y, MeasurableSet E ∧
      1 - Real.sqrt ((Real.log M / m + 1) / Real.log N) ≤ μ.real E ∧
      ∀ ρ : Measure Y, ρ ≤ μ.restrict E → ∀ h z,
        ρ.real {y | (history (i + 1) (code y), palette (code y)) = (h, z)} ≤
          N ^ Real.sqrt ((Real.log M / m + 1) / Real.log N) *
            μ.real {y | history (i + 1) (code y) = h} *
            (μ.real {y | (history i (code y), palette (code y)) = (parent i h, z)} /
              μ.real {y | history i (code y) = parent i h}) := by
  let P : Fin n → ℝ := fun e => μ.real (code ⁻¹' {e})
  have hP : ∀ e, 0 ≤ P e := fun _ => ENNReal.toReal_nonneg
  have hP1 : ∑ e, P e = 1 :=
    Submission.Obl.k4_matching_cofinal_palette_selection.sum_atomMass_eq_one μ code hcode
  obtain ⟨i, hi, hinfo⟩ := entropy_window P hP palette history hm
  have hbudget : negCondEnt P palette (history (i + 1)) -
      negCondEnt P palette (history i) + 1 ≤ Real.log M / m + 1 := by
    have hc := div_le_div_of_nonneg_right
      (finite_entropy_card_upper P hP hP1 (history 0) palette hM hcard)
      (by positivity : (0 : ℝ) ≤ m)
    linarith only [hinfo, hc]
  have hlog : 0 ≤ Real.log (M : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hM)
  have hB : 0 < Real.log M / m + 1 := by positivity
  obtain ⟨E, hE, hmass, hcap⟩ := original_balanced_likelihood μ code hcode
    (history i) (history (i + 1)) (parent i) palette (hrefine i)
    N (Real.log M / m + 1) hN hB hbudget
  exact ⟨i, hi, E, hE, hmass, hcap⟩

end

end Submission.Obl.k4_finite_affine_parent_sources
