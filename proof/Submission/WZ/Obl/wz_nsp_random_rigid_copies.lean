-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_random_rigid_copies.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_nsp_convex_test_family
import Submission.WZ.Obl.wz_nsp_translation_model
import Submission.WZ.Obl.wz_nsp_finite_load_selection

set_option linter.unusedVariables false

theorem WangZahlLot.wz_nsp_random_rigid_copies : ∀ T, T = (fun (d : ℝ) (p q : LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening d (segment ℝ p (p + q))) → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (r ρ M L : ℝ) (K n : ℕ) (y w : Fin K → LeanEval.Analysis.WangZahlKakeya.Space) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (g : Fin n → Fin K), 0 < r → r ≤ ρ → ρ ≤ 1 → 1 ≤ M → (∀ k : Fin K, ‖w k‖ = 1 ∧ ((Set.ncard {i : Fin n | g i = k} : ℕ) : ℝ) ≤ M) → (∀ i : Fin n, ‖v i‖ = 1 ∧ T r (x i) (v i) ⊆ Metric.ball 0 1 ∧ T r (x i) (v i) ⊆ T ρ (y (g i)) (w (g i))) → (∀ (k : Fin K) (W : Set LeanEval.Analysis.WangZahlKakeya.Space), Convex ℝ W → ENNReal.ofReal (((Set.ncard {i : Fin n | g i = k ∧ T r (x i) (v i) ⊆ W} : ℕ) : ℝ) * r ^ 2) ≤ ENNReal.ofReal L * MeasureTheory.volume W) → ∃ (N : ℕ) (A : Fin N → (LeanEval.Analysis.WangZahlKakeya.Space ≃ᵃⁱ[ℝ] LeanEval.Analysis.WangZahlKakeya.Space)), ρ ^ 2 ≤ (N : ℝ) * M * r ^ 2 ∧ (N : ℝ) * M * r ^ 2 ≤ ρ ^ 2 + M * r ^ 2 ∧ (∀ (j : Fin N) (p : LeanEval.Analysis.WangZahlKakeya.Space), ‖p‖ < 1 → ‖A j p - p‖ ≤ ρ) ∧ ∀ (k : Fin K) (W : Set LeanEval.Analysis.WangZahlKakeya.Space), Convex ℝ W → ENNReal.ofReal (((Set.ncard {q : Fin N × Fin n | g q.2 = k ∧ T r (A q.1 (x q.2)) ((A q.1).linear (v q.2)) ⊆ W} : ℕ) : ℝ) * r ^ 2) ≤ ENNReal.ofReal (C * r ^ (-ε) * Real.log (2 + (K : ℝ)) * L) * MeasureTheory.volume W := by
  intro T hT ε hε
  obtain ⟨D, hD, htests⟩ := WangZahlLot.wz_nsp_convex_test_family T hT
  obtain ⟨a, ha, hmodel⟩ := WangZahlLot.wz_nsp_translation_model T hT
  obtain ⟨C, hC, hselect⟩ :=
    WangZahlLot.wz_nsp_finite_load_selection a D ha hD ε hε
  refine ⟨D * C, mul_pos (lt_of_lt_of_le zero_lt_one hD) hC, ?_⟩
  intro r ρ M L K n y w x v g hr hrρ hρ hM hg ht hKT
  have hr1 : r ≤ 1 := hrρ.trans hρ
  obtain ⟨H, P, hsize, hP, htransfer⟩ := htests r hr hr1
  obtain ⟨N, m, B, X, hm, hround_lo, hround_hi, hmove, hcopies,
      hbounded, haverage, hreconstruct⟩ :=
    hmodel r ρ M L K n H x v g P hr hrρ hρ hM
      (fun k => (hg k).2) (fun i => ⟨(ht i).1, (ht i).2.1⟩) hKT hP
  obtain ⟨f, hf⟩ := hselect r K H m N X hr hr1 hm hsize hbounded haverage
  have hlog : 0 ≤ Real.log (2 + (K : ℝ)) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) K; linarith)
  have hu : 0 ≤ C * r ^ (-ε) * Real.log (2 + (K : ℝ)) :=
    mul_nonneg (mul_nonneg hC.le (Real.rpow_pos_of_pos hr _).le) hlog
  have hcount := hreconstruct f (C * r ^ (-ε) * Real.log (2 + (K : ℝ))) hu hf
  have hfinal := htransfer K N n
    (fun q => B (f q.1) (x q.2))
    (fun q => (B (f q.1)).linear (v q.2)) g
    (C * r ^ (-ε) * Real.log (2 + (K : ℝ)) * L)
    (fun q => hcopies (f q.1) q.2) hcount
  refine ⟨N, fun j => B (f j), hround_lo, hround_hi,
    fun j p hp => hmove (f j) p hp, ?_⟩
  intro k W hW
  have hcoeff : D * (C * r ^ (-ε) * Real.log (2 + (K : ℝ)) * L) =
      D * C * r ^ (-ε) * Real.log (2 + (K : ℝ)) * L := by ring
  simpa only [hcoeff] using hfinal k W hW
