-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_tower_convex_count_composition.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_tower_convex_count_composition.Composition
import Submission.WZ.Obl.wz_tower_convex_count_composition.Arithmetic
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_tower_convex_count_composition`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_tower_convex_count_composition`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_tower_convex_count_composition/`
belong to this obligation.
-/

theorem WangZahlLot.wz_tower_convex_count_composition : ∀ (B : ℕ) (ε : ℝ), ∀ μ, μ = ((MeasureTheory.volume : MeasureTheory.Measure LeanEval.Analysis.WangZahlKakeya.Space)) → ∀ e, e = (ENNReal.ofReal) → ∀ T, T = (fun (d : ℝ) (p q : LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening d (segment ℝ p (p+q))) → ∀ K, K = (fun (d L : ℝ) (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) => ∀ W, Convex ℝ W → e (Set.ncard {i | T d (x i) (v i) ⊆ W} * d^2) ≤ e L * μ W) → ∀ H, H = (fun (b : Bool) (d L g : ℝ) (B n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) => ∃ J : ℕ, 1≤J ∧ J≤B ∧ ∃ (r : ℕ → ℝ) (N : ℕ → ℕ) (y w : ∀ j, Fin (N j) → LeanEval.Analysis.WangZahlKakeya.Space) (f : ∀ j, Fin (N (j+1)) → Fin (N j)), r 0=1 ∧ r J=d ∧ N 0=1 ∧ (∃ u : Fin n ≃ Fin (N J), ∀ i, y J (u i)=x i ∧ w J (u i)=v i) ∧ (∀ j, j≤J → ∀ k, ‖w j k‖=1) ∧ (∀ j, j<J → 0<r (j+1) ∧ r (j+1)<r j ∧ d^g*r j≤r (j+1) ∧ ∀ i, T (r (j+1)) (y (j+1) i) (w (j+1) i) ⊆ T (r j) (y j (f j i)) (w j (f j i))) ∧ (if b then ∀ j, j≤J → K (r j) L (N j) (y j) (w j) else ∀ j, j<J → ∀ k W, Convex ℝ W → e (Set.ncard {i | f j i=k ∧ T (r (j+1)) (y (j+1) i) (w (j+1) i) ⊆ W} * (r (j+1))^2) ≤ e L * μ W)) → 0<ε → ∃ θ : ℝ, 0<θ ∧ θ≤ε ∧ ∃ d₀ : ℝ, 0<d₀ ∧ ∀ δ : ℝ, 0<δ → δ≤1/100 → δ≤d₀ → ∀ (g : ℝ) (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space), H false δ (δ^(-θ)) g B n x v → H true δ (δ^(-ε)) g B n x v := by
  classical
  rintro B ε μ rfl e rfl T rfl K rfl H rfl hε
  obtain ⟨θ, hθ, hθε, d₀, hd₀, hbudget⟩ :=
    WangZahlLot.Obl.wz_tower_convex_count_composition.power_budget 131072 (by norm_num) B ε hε
  refine ⟨θ, hθ, hθε, d₀, hd₀, ?_⟩
  intro δ hδ hδ100 hδd g n x v hlocal
  obtain ⟨J, hJ1, hJB, r, N, y, w, f, hr0, hrJ, hN0, hleaf, hunit, hedge, hfiber⟩ := hlocal
  refine ⟨J, hJ1, hJB, r, N, y, w, f, hr0, hrJ, hN0, hleaf, hunit, hedge, ?_⟩
  have hrange : ∀ j, j ≤ J → 0 < r j ∧ r j ≤ 1 := by
    intro j
    induction j with
    | zero => intro _; rw [hr0]; norm_num
    | succ j ih =>
      intro hj
      have hj' : j < J := by omega
      exact ⟨(hedge j hj').1, (hedge j hj').2.1.le.trans (ih (by omega)).2⟩
  have hglobal : ∀ j, j ≤ J →
      WangZahlLot.Obl.wz_tower_convex_count_composition.Counts (r j)
        ((131072 * δ ^ (-θ)) ^ j) (N j) (y j) (w j) := by
    intro j
    induction j with
    | zero =>
      intro _
      simpa only [hr0, pow_zero] using
        WangZahlLot.Obl.wz_tower_convex_count_composition.counts_root hN0 (y 0) (w 0)
          (hunit 0 (Nat.zero_le _))
    | succ j ih =>
      intro hj
      have hj' : j < J := by omega
      have hjle : j ≤ J := by omega
      have hc := WangZahlLot.Obl.wz_tower_convex_count_composition.counts_compose
        (hedge j hj').1 (hrange j hjle).1 (hrange j hjle).2
        (show 0 ≤ (131072 * δ ^ (-θ)) ^ j by positivity)
        (Real.rpow_nonneg hδ.le (-θ))
        (y (j + 1)) (w (j + 1)) (y j) (w j) (f j)
        (hunit (j + 1) hj) (hunit j hjle) (hedge j hj').2.2.2
        (ih hjle) (hfiber j hj')
      convert hc using 1
      rw [pow_succ]
      ring
  intro j hj
  exact WangZahlLot.Obl.wz_tower_convex_count_composition.counts_mono (hglobal j hj)
    (hbudget δ hδ (by linarith) hδd j (hj.trans hJB))
