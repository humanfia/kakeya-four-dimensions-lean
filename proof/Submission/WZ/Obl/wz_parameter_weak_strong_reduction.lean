-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_parameter_weak_strong_reduction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_parameter_weak_strong_reduction.Counting
import Submission.WZ.Obl.wz_parameter_weak_strong_reduction.Layers
import Submission.WZ.Obl.wz_parameter_weak_strong_reduction.Measure
import Submission.WZ.Obl.wz_parameter_weak_strong_reduction.Parameters
import Submission.WZ.Obl.wz_parameter_weak_strong_reduction.Scale
set_option linter.unusedVariables false

/-!
Uniform weak L^(3/2) bounds at every error exponent imply the strong
bound for finite strip families. A compact coefficient cover bounds the
multiplicity by a fixed power of the scale; finitely many geometric bands
and a smaller scale cutoff absorb the resulting constant.
-/

open WangZahlLot.Obl.wz_parameter_weak_strong_reduction in
theorem WangZahlLot.wz_parameter_weak_strong_reduction : ∀ P : (n : ℕ) → (Fin n → EuclideanSpace ℝ (Fin 3)) → (Fin n → ℝ → ℝ) → Prop, (∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1/100 : ℝ) → ∀ (n : ℕ) (q : Fin n → EuclideanSpace ℝ (Fin 3)) (g : Fin n → ℝ → ℝ), (∀ i, ‖q i‖ ≤ 10) → (∀ i, ContDiff ℝ 2 (g i)) → P n q g → (∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) → (∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ 1 → (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) ≤ δ ^ (-η) * (r / δ)) → ∀ lam : ℝ, 1 ≤ lam → MeasureTheory.volume {p : ℝ × ℝ | ENNReal.ofReal lam ≤ (Finset.sum Finset.univ (fun i => Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} (fun _ => (1 : ENNReal)) p))} ≤ ENNReal.ofReal (δ ^ (-ε) * lam ^ (-(3/2 : ℝ)))) → (∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1/100 : ℝ) → ∀ (n : ℕ) (q : Fin n → EuclideanSpace ℝ (Fin 3)) (g : Fin n → ℝ → ℝ), (∀ i, ‖q i‖ ≤ 10) → (∀ i, ContDiff ℝ 2 (g i)) → P n q g → (∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) → (∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ 1 → (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) ≤ δ ^ (-η) * (r / δ)) → MeasureTheory.lintegral MeasureTheory.volume (fun p : ℝ × ℝ => (Finset.sum Finset.univ (fun i => Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} (fun _ => (1 : ENNReal)) p)) ^ (3/2 : ℝ)) ≤ ENNReal.ofReal (δ ^ (-ε))) := by
  intro P hweak ε hε
  obtain ⟨C, hC, hcount⟩ := exists_coefficient_count_constant
  obtain ⟨ηw, hηw, dw, hdw, hweakw⟩ := hweak (ε / 4) (by linarith)
  obtain ⟨K, hKn⟩ := exists_nat_gt (18 / ε)
  have hK : 3 ≤ ε / 6 * ((K + 1 : ℕ) : ℝ) := by
    have h := (div_lt_iff₀ hε).mp hKn
    push_cast
    nlinarith
  obtain ⟨dc, hdc, hconst⟩ := exists_power_cutoff C 1 (by norm_num)
  obtain ⟨dk, hdk, hbands⟩ := exists_power_cutoff ((K + 1 : ℕ) : ℝ) (ε / 2) (by linarith)
  refine ⟨min ηw 1, lt_min hηw (by norm_num),
    min dw (min dc dk), lt_min hdw (lt_min hdc hdk), ?_⟩
  intro δ hδ hδd hδsmall n q g hq hg hP hsep hlocal
  have hδ1 : δ ≤ 1 := by linarith
  have hδw : δ ≤ dw := hδd.trans (min_le_left _ _)
  have hδc : δ ≤ dc := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδk : δ ≤ dk := hδd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have htransfer : ∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ),
      δ ≤ r → r ≤ 1 → (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) ≤
        δ ^ (-ηw) * (r / δ) := by
    intro q0 r hr hr1
    refine (hlocal q0 r hr hr1).trans (mul_le_mul_of_nonneg_right ?_ ?_)
    · exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1
        (neg_le_neg (min_le_left _ _))
    · exact div_nonneg (hδ.le.trans hr) hδ.le
  have hunit (q0 : EuclideanSpace ℝ (Fin 3)) :
      (Set.ncard {i | q i ∈ Metric.ball q0 1} : ℝ) ≤ δ ^ (-2 : ℝ) := by
    calc
      _ ≤ δ ^ (-(min ηw 1)) * (1 / δ) := hlocal q0 1 hδ1 le_rfl
      _ ≤ δ ^ (-1 : ℝ) * (1 / δ) :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg (min_le_right _ _)))
          (by positivity)
      _ = δ ^ (-2 : ℝ) := by
        rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_add hδ]
        norm_num
  have hn : (n : ℝ) ≤ δ ^ (-3 : ℝ) := by
    calc
      (n : ℝ) ≤ C * δ ^ (-2 : ℝ) :=
        hcount n q _ hq (Real.rpow_nonneg hδ.le _) hunit
      _ ≤ δ ^ (-1 : ℝ) * δ ^ (-2 : ℝ) :=
        mul_le_mul_of_nonneg_right (hconst δ hδ hδc) (Real.rpow_nonneg hδ.le _)
      _ = δ ^ (-3 : ℝ) := by rw [← Real.rpow_add hδ]; norm_num
  apply weak_strong_scale_bound MeasureTheory.volume (multiplicity δ g)
    (measurable_multiplicity δ (fun i => (hg i).continuous)) ε δ hε hδ hδ1 K hK
    (hbands δ hδ hδk) (multiplicity_zero_or_one_le δ g)
  · intro p
    calc
      multiplicity δ g p ≤ (n : ENNReal) := multiplicity_le_card δ g p
      _ = ENNReal.ofReal (n : ℝ) := (ENNReal.ofReal_natCast n).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hn
  · intro lam hlam
    exact hweakw δ hδ hδw hδsmall n q g hq hg hP hsep htransfer lam hlam
