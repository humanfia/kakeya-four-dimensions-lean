-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.FrozenUnionAdapter
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.OrientedWindow

/-! The short-window contact estimate, coefficient localization, and sampling
reduction yield the frozen restricted rich-area bound with density exponent one. -/

open WangZahlLot.Obl.wz_jet_bipartite_rich_area in
theorem WangZahlLot.wz_jet_bipartite_rich_area : ∀ τ : ℝ, 0 < τ → ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1/100 : ℝ) → ∀ (n : ℕ) (q : Fin n → EuclideanSpace ℝ (Fin 3)) (g : Fin n → ℝ → ℝ), (∀ i, ‖q i‖ ≤ 10) → (∀ i, ContDiff ℝ 2 (g i)) → (∀ (i j : Fin n) (z : ℝ), z ∈ Set.Icc (-1 : ℝ) 1 → dist (q i) (q j) ≤ 30 * (|g i z - g j z| + |deriv (g i) z - deriv (g j) z| + |deriv (deriv (g i)) z - deriv (deriv (g j)) z|) ∧ (|g i z - g j z| + |deriv (g i) z - deriv (g j) z| + |deriv (deriv (g i)) z - deriv (deriv (g j)) z|) ≤ 19 * dist (q i) (q j)) → (∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) → ∀ (A B : Finset (Fin n)) (D K mu : ℝ), δ ≤ D → D ≤ 20 → 1 ≤ K → (∀ i ∈ A, ∀ j ∈ A, dist (q i) (q j) ≤ D / 100) → (∀ i ∈ B, ∀ j ∈ B, dist (q i) (q j) ≤ D / 100) → (∀ i ∈ A, ∀ j ∈ B, D ≤ dist (q i) (q j) ∧ dist (q i) (q j) ≤ 2 * D) → (∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ D → (Set.ncard {i : Fin n | i ∈ (A ∪ B) ∧ q i ∈ Metric.ball q0 r} : ℝ) ≤ K * (r / δ)) → 1 ≤ mu → δ * mu * δ ^ (-8 * τ) ≤ D → MeasureTheory.volume {p : ℝ × ℝ | ENNReal.ofReal mu ≤ Finset.sum A (fun i => Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} (fun _ => (1 : ENNReal)) p) ∧ ENNReal.ofReal mu ≤ Finset.sum B (fun i => Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} (fun _ => (1 : ENNReal)) p) ∧ Finset.sum A (fun i => Finset.sum B (fun j => Set.indicator ({p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} ∩ {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g j p.2| ≤ δ} ∩ {p : ℝ × ℝ | δ ^ (4 * τ) * mu ^ (-(1/2 : ℝ)) * dist (q i) (q j) ≤ |deriv (g i) p.2 - deriv (g j) p.2|}) (fun _ => (1 : ENNReal)) p)) < ENNReal.ofReal (mu ^ 2 / 100)} ≤ ENNReal.ofReal (C * δ ^ (-τ) * K ^ a * δ * ((A.card : ℝ) + (B.card : ℝ)) * mu ^ (-(3/2 : ℝ))) := by

  intro τ hτ
  obtain ⟨θ, C, hθ, hθsmall, hC, hlocal⟩ := exists_oriented_window_estimate τ hτ
  let C' : ℝ := 400000+20000*(27648/θ^3)^2*C
  have hC' : 0 < C' := by dsimp [C']; positivity
  have hunion : NarrowUnionEstimate τ C' :=
    narrowUnionEstimate_of_orientedWindowEstimate hτ.le hθ hθsmall hC.le hlocal
  refine ⟨1, by norm_num, 576*C', by positivity, ?_⟩
  intro δ hδ hδ100 n q g hq hg hjet hsep A B D K μ hδD hD20 hK hA hB hcross hcount hμ hscale
  exact restricted_area_of_union_estimate hτ.le hC'.le hunion hq hg hjet A B
    hδ hδ100 hsep hδD hD20 (by linarith) hK hA hB hcross hcount hscale
