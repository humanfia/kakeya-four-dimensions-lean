import Submission.Obl.k4_finite_positive_prepared_models.Stages
import Submission.Obl.k4_finite_positive_prepared_models.FineGrid

namespace Submission.Obl.k4_finite_positive_prepared_models

open MeasureTheory MvPolynomial

noncomputable section

/-- The first two stages have no nonempty tested range. -/
def initialStage (n : ℕ) : EStage (ℕ × (Fin 6 → ℝ)) where
  N := (n : ℝ) + 2
  K := 1
  ν := Measure.dirac (0, 0)
  μ := ((Measure.dirac (0, (0 : Fin 6 → ℝ))).prod volume).restrict (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)
  ρ := ((Measure.dirac (0, (0 : Fin 6 → ℝ))).prod volume).restrict (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)
  π := Measure.dirac 0
  b := fun _ => 0
  P := X (3 : Fin 4)
  T := fun _ => 0
  nl := fun _ => 0
  j := fun _ i => Fin.elim0 i
  A := fun _ i => Fin.elim0 i
  B := fun _ i => Fin.elim0 i
  c := fun _ i => Fin.elim0 i
  F := fun _ i => Fin.elim0 i

theorem initialStage_eh1 (n : ℕ) : EH1 (initialStage n) := by
  refine ⟨measurable_const,
    by change IsProbabilityMeasure (Measure.dirac (0, (0 : Fin 6 → ℝ))); infer_instance,
    by change IsProbabilityMeasure (Measure.dirac (0 : ℝ)); infer_instance,
    ?_, le_rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [initialStage, ENNReal.ofReal_one, one_smul] using
      (Measure.restrict_le_self :
        ((Measure.dirac (0, (0 : Fin 6 → ℝ))).prod volume).restrict (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) ≤
          (Measure.dirac (0, (0 : Fin 6 → ℝ))).prod volume)
  · change (((Measure.dirac (0, (0 : Fin 6 → ℝ))).prod volume).restrict
      (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)) (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0
    rw [Measure.restrict_apply (MeasurableSet.univ.prod measurableSet_Icc).compl]
    simp
  · change ENNReal.ofReal ((1 : ℝ)⁻¹) ≤
      (((Measure.dirac (0, (0 : Fin 6 → ℝ))).prod volume).restrict
        (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)) Set.univ
    simp [Measure.prod_prod]
  · simp [initialStage]
  · exact Filter.Eventually.of_forall fun _ => by simp [initialStage]
  · exact Filter.Eventually.of_forall fun _ => by simp [initialStage, exS, pderiv_X]

theorem initialStage_good (d κ ℓ S : ℝ) (n : ℕ) (hn : n ≤ 1) :
    StageGood d κ ℓ S n (initialStage n) := by
  refine ⟨le_rfl, ⟨le_rfl, ?_⟩, initialStage_eh1 n, ?_⟩
  · change 1 ≤ ((n : ℝ) + 2) ^ (1 / ((n : ℝ) + 1))
    apply Real.one_le_rpow
    · have := Nat.cast_nonneg (α := ℝ) n
      linarith
    · positivity
  · intro R hR hRn
    have hn' : (n : ℝ) ≤ 1 := by exact_mod_cast hn
    linarith

/-- The range and candidate conditions are vacuous in stages zero and one. -/
theorem stageModel_small (d κ ℓ S η ρ : ℝ) (n : ℕ) (hn : n ≤ 1)
    (m : ℕ) (s : ℕ → ℝ) (gain δ₀ : ℝ) :
    StageModel d κ ℓ S η ρ n m s gain δ₀ := by
  intro N K L d' W ω ν E P B f g G hprob hprof Mp Dp
  refine ⟨0, fun ε hε => ⟨1, one_pos, 0, ?_⟩⟩
  intro k hk r T nw κ' C lev par γ j c u Q R A F lst hpath H hH hmass
  refine ⟨initialStage n, initialStage_good d κ ℓ S n hn, ?_⟩
  intro R hR hRn
  have hn' : (n : ℝ) ≤ 1 := by exact_mod_cast hn
  linarith

/-- Both initial stages meet the entire prepared-model conclusion. -/
theorem stageReady_small (d κ ℓ S η ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (hn : n ≤ 1) :
    StageReady d κ ℓ S η ρ n := by
  obtain ⟨m, s, hgrid⟩ := exists_fineGrid (1 / 8) ρ (by norm_num) hρ
  refine ⟨m, s, 1 / 8, ρ / 16, hgrid, by norm_num, le_rfl,
    by positivity, by linarith, stageModel_small d κ ℓ S η ρ n hn m s _ _⟩

end

end Submission.Obl.k4_finite_positive_prepared_models
