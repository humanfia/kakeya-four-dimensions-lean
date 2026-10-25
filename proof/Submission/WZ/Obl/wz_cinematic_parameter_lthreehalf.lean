-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_cinematic_parameter_lthreehalf.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_normalized_cinematic_jet_bounds
import Submission.WZ.Obl.wz_jet_family_rich_point_bound
import Submission.WZ.Obl.wz_parameter_weak_strong_reduction

set_option linter.unusedVariables false

theorem WangZahlLot.wz_cinematic_parameter_lthreehalf : (fun N : (ℝ → ℝ) → Prop => ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1/100 : ℝ) → ∀ f : ℝ → ℝ, N f → |f 0| ≤ 1 → ∀ (n : ℕ) (q : Fin n → EuclideanSpace ℝ (Fin 3)), (∀ i, ‖q i‖ ≤ 10) → (∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) → (∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ 1 → (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) ≤ δ ^ (-η) * (r / δ)) → MeasureTheory.lintegral MeasureTheory.volume (fun p : ℝ × ℝ => (Finset.sum Finset.univ (fun i => Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - (q i 0 + q i 1 * f p.2 + q i 2 * p.2 * f p.2)| ≤ δ} (fun _ => (1 : ENNReal)) p)) ^ (3/2 : ℝ)) ≤ ENNReal.ofReal (δ ^ (-ε))) (fun f : ℝ → ℝ => ContDiff ℝ 2 f ∧ ∀ z : ℝ, z ∈ Set.Icc (-1) 1 → 1 ≤ |deriv f z| ∧ |deriv f z| ≤ 2 ∧ |deriv (deriv f) z| ≤ (1/100 : ℝ)) := by
  let P : (n : ℕ) → (Fin n → EuclideanSpace ℝ (Fin 3)) → (Fin n → ℝ → ℝ) → Prop := fun n q g =>
    ∀ (i j : Fin n) (z : ℝ), z ∈ Set.Icc (-1 : ℝ) 1 → dist (q i) (q j) ≤ 30 * (|g i z - g j z| + |deriv (g i) z - deriv (g j) z| + |deriv (deriv (g i)) z - deriv (deriv (g j)) z|) ∧ (|g i z - g j z| + |deriv (g i) z - deriv (g j) z| + |deriv (deriv (g i)) z - deriv (deriv (g j)) z|) ≤ 19 * dist (q i) (q j)
  have hstrong := WangZahlLot.wz_parameter_weak_strong_reduction P
    WangZahlLot.wz_jet_family_rich_point_bound
  intro ε hε
  obtain ⟨η, hη, d0, hd0, hbound⟩ := hstrong ε hε
  refine ⟨η, hη, d0, hd0, ?_⟩
  intro δ hδ hδd0 hδ100 f hf hf0 n q hq hsep hcount
  let g : Fin n → ℝ → ℝ :=
    fun i z => q i 0 + q i 1 * f z + q i 2 * z * f z
  have hgeometry := WangZahlLot.wz_normalized_cinematic_jet_bounds f hf.1 hf.2 hf0
  exact hbound δ hδ hδd0 hδ100 n q g hq
    (fun i => hgeometry.1 (q i))
    (fun i j z hz => hgeometry.2 (q i) (q j) z hz) hsep hcount
