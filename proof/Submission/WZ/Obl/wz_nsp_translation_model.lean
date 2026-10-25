-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_translation_model.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_nsp_translation_model.Normalization
import Submission.WZ.Obl.wz_nsp_translation_model.Coefficient
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_nsp_translation_model`

A finite separated net of translations gives a uniform geometric average.
Normalize the translated group counts by `L * volume(P h)`, and round the copy
count upward. The original convex count bound controls each load; longitudinal
ball packing controls their averages. Summing the loads reconstructs all selected
test counts, with multiplicity.
-/

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_nsp_translation_model

theorem WangZahlLot.wz_nsp_translation_model : ∀ T, T = (fun (d : ℝ) (p q : LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening d (segment ℝ p (p + q))) → ∃ a : ℝ, 1 ≤ a ∧ ∀ (r ρ M L : ℝ) (K n H : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (g : Fin n → Fin K) (P : Fin H → Set LeanEval.Analysis.WangZahlKakeya.Space), 0 < r → r ≤ ρ → ρ ≤ 1 → 1 ≤ M → (∀ k : Fin K, ((Set.ncard {i : Fin n | g i = k} : ℕ) : ℝ) ≤ M) → (∀ i : Fin n, ‖v i‖ = 1 ∧ T r (x i) (v i) ⊆ Metric.ball 0 1) → (∀ (k : Fin K) (W : Set LeanEval.Analysis.WangZahlKakeya.Space), Convex ℝ W → ENNReal.ofReal (((Set.ncard {i : Fin n | g i = k ∧ T r (x i) (v i) ⊆ W} : ℕ) : ℝ) * r ^ 2) ≤ ENNReal.ofReal L * MeasureTheory.volume W) → (∀ h : Fin H, Convex ℝ (P h) ∧ MeasurableSet (P h) ∧ 0 < MeasureTheory.volume (P h) ∧ MeasureTheory.volume (P h) ≠ ⊤) → ∃ (N m : ℕ) (B : Fin m → (LeanEval.Analysis.WangZahlKakeya.Space ≃ᵃⁱ[ℝ] LeanEval.Analysis.WangZahlKakeya.Space)) (X : Fin K → Fin H → Fin m → ℝ), 0 < m ∧ ρ ^ 2 ≤ (N : ℝ) * M * r ^ 2 ∧ (N : ℝ) * M * r ^ 2 ≤ ρ ^ 2 + M * r ^ 2 ∧ (∀ (s : Fin m) (p : LeanEval.Analysis.WangZahlKakeya.Space), ‖p‖ < 1 → ‖B s p - p‖ ≤ ρ) ∧ (∀ (s : Fin m) (i : Fin n), ‖(B s).linear (v i)‖ = 1 ∧ T r (B s (x i)) ((B s).linear (v i)) ⊆ Metric.ball 0 2) ∧ (∀ (k : Fin K) (h : Fin H) (s : Fin m), 0 ≤ X k h s ∧ X k h s ≤ 1) ∧ (∀ (k : Fin K) (h : Fin H), (N : ℝ) * Finset.sum Finset.univ (fun s : Fin m => X k h s) ≤ a * (m : ℝ)) ∧ (∀ (f : Fin N → Fin m) (u : ℝ), 0 ≤ u → (∀ (k : Fin K) (h : Fin H), Finset.sum Finset.univ (fun j : Fin N => X k h (f j)) ≤ u) → ∀ (k : Fin K) (h : Fin H), ENNReal.ofReal (((Set.ncard {q : Fin N × Fin n | g q.2 = k ∧ T r (B (f q.1) (x q.2)) ((B (f q.1)).linear (v q.2)) ⊆ P h} : ℕ) : ℝ) * r ^ 2) ≤ ENNReal.ofReal (u * L) * MeasureTheory.volume (P h)) := by
  classical
  rintro T rfl
  refine ⟨1572865, by norm_num, ?_⟩
  intro r ρ M L K n H x v g P hr hrρ hρ1 hM hgroup hv hcount hP
  have hρ : 0 < ρ := hr.trans_le hrρ
  have hMpos : 0 < M := by linarith
  obtain ⟨N, hNlower, hNupper, hNapprox⟩ := rounded_copies (ρ := ρ) hr hMpos
  by_cases hn : n = 0
  · subst n
    refine ⟨N, 1, (fun _ => AffineIsometryEquiv.refl ℝ Space),
      (fun _ _ _ => 0), by decide, hNlower, hNupper, ?_, ?_, ?_, ?_, ?_⟩
    · intro s p hp
      simpa using hρ.le
    · intro s i
      exact Fin.elim0 i
    · intro k h s
      norm_num
    · intro k h
      norm_num
    · intro f u hu hsum k h
      have he : {q : Fin N × Fin 0 | g q.2 = k ∧
          Tube r (x q.2) (v q.2) ⊆ P h} = ∅ := Set.eq_empty_of_isEmpty _
      change ENNReal.ofReal ((ncard {q : Fin N × Fin 0 | g q.2 = k ∧
        Tube r (x q.2) (v q.2) ⊆ P h} : ℝ) * r ^ 2) ≤ _
      simp [he]
  · have hLcoef : 1 ≤ 384 * L := coefficient_lower hr (hrρ.trans hρ1)
      x v g (fun i => (hv i).1) hcount ⟨0, Nat.pos_of_ne_zero hn⟩
    have hLpos : 0 < L := by linarith
    obtain ⟨m, t, hm, ht, havg⟩ := translation_average hr hrρ
    let B : Fin m → (Space ≃ᵃⁱ[ℝ] Space) := fun s => AffineIsometryEquiv.vaddConst ℝ (t s)
    let C : Fin K → Fin H → Fin m → ℝ := fun k h s =>
      (ncard {i : Fin n | g i = k ∧ Tube r (x i + t s) (v i) ⊆ P h} : ℝ)
    let X : Fin K → Fin H → Fin m → ℝ := fun k h s =>
      C k h s * r ^ 2 / (L * volume.real (P h))
    have hV (h : Fin H) : 0 < volume.real (P h) :=
      ENNReal.toReal_pos (hP h).2.2.1.ne' (hP h).2.2.2
    have hC (k : Fin K) (h : Fin H) (s : Fin m) :
        C k h s * r ^ 2 ≤ L * volume.real (P h) :=
      count_real hLpos.le (hP h).2.2.2 (Nat.cast_nonneg _)
        (translated_count x v g hcount k (P h) (hP h).1 (t s))
    refine ⟨N, m, B, X, hm, hNlower, hNupper, ?_, ?_, ?_, ?_, ?_⟩
    · intro s p hp
      change ‖p + t s - p‖ ≤ ρ
      simpa using ht s
    · intro s i
      change ‖v i‖ = 1 ∧ Tube r (x i + t s) (v i) ⊆ ball (0 : Space) 2
      exact ⟨(hv i).1, translated_ball hρ1 (ht s) (hv i).2⟩
    · intro k h s
      exact normalized_load_bounds (Nat.cast_nonneg _) hLpos (hV h) (hC k h s)
    · intro k h
      exact normalized_average (C k h) hr hρ hMpos hLcoef (hV h) hNapprox
        (fun s => Nat.cast_nonneg _) (hC k h)
        (group_average t x v g hgroup (fun i => (hv i).1) havg k (P h) (hP h).2.2.2)
    · intro f u hu hsum k h
      exact reconstruct_loads hLpos (hP h).2.2.1 (hP h).2.2.2
        (fun s i => g i = k ∧ Tube r (x i + t s) (v i) ⊆ P h) f u hu (hsum k h)
