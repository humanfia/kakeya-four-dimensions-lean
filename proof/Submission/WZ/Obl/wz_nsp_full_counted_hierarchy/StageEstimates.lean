-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.StageEstimates.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.SingleScale
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Mass

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_tower_convex_count_composition (Counts)

/-- The supplied single-scale theorem produces all edges of a buffered source
tower, with uniform convex-count, fullness and mass estimates. -/
theorem buffered_stage_estimates (hSS : SingleScale) {u : ℝ} (hu : 0 < u) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ (J : ℕ) (r M : ℕ → ℝ) (n : ℕ → ℕ)
        (x v : ∀ j, Fin (n j) → Space)
        (f : ∀ j, Fin (n (j + 1)) → Fin (n j)),
        (n J : ℝ) ≤ δ ^ (-7 : ℝ) →
        (∀ j, j ≤ J → δ ≤ r j ∧ r j ≤ 1 ∧ 0 < n j ∧
          (∀ i, ‖v j i‖ = 1 ∧ Tube (r j) (x j i) (v j i) ⊆ Metric.ball 0 1) ∧
          Counts (r j) (δ ^ (-u)) (n j) (x j) (v j)) →
        (∀ j, j < J → 16 * r (j + 1) ≤ r j ∧ 1 ≤ M j ∧
          (∀ i, M j / 2 ≤ (Set.ncard {s | f j s = i} : ℝ) ∧
            (Set.ncard {s | f j s = i} : ℝ) ≤ M j) ∧
          ∀ i, Tube (r (j + 1)) (x (j + 1) i) (v (j + 1) i) ⊆
            Tube (r j / 4) (x j (f j i)) (v j (f j i))) →
        ∃ (D : ℕ → ℕ) (A : ∀ j, Fin (D j) → (Space ≃ᵃⁱ[ℝ] Space)),
          ∀ j, j < J → 0 < D j ∧
            (∀ a i, Tube (r (j + 1)) (A j a (x (j + 1) i))
              ((A j a).linear (v (j + 1) i)) ⊆ Tube (r j) (x j (f j i)) (v j (f j i))) ∧
            (∀ i, (1 / 32 : ℝ) * (r j) ^ 2 ≤
              (D j : ℝ) * (Set.ncard {s | f j s = i} : ℝ) * (r (j + 1)) ^ 2) ∧
            (D j : ℝ) * ((n (j + 1) : ℝ) * (r (j + 1)) ^ 2) ≤
              (49 * δ ^ (-u)) * ((n j : ℝ) * (r j) ^ 2) ∧
            ∀ k W, Convex ℝ W →
              ENNReal.ofReal ((Set.ncard {q : Fin (D j) × Fin (n (j + 1)) |
                f j q.2 = k ∧ Tube (r (j + 1)) (A j q.1 (x (j + 1) q.2))
                  ((A j q.1).linear (v (j + 1) q.2)) ⊆ W} : ℝ) * (r (j + 1)) ^ 2) ≤
                ENNReal.ofReal (C * δ ^ (-3 * u)) * volume W := by
  classical
  obtain ⟨C₁, hC₁, hcopies⟩ := choose_stage_copies hSS hu
  obtain ⟨C₂, hC₂, hlog⟩ := log_count_power_bound (show (0 : ℝ) < 7 by norm_num) hu
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  intro δ hδ hδ1 J r M n x v f hnJ hl he
  have hL : 0 ≤ δ ^ (-u) := Real.rpow_nonneg hδ.le _
  have hL1 : 1 ≤ δ ^ (-u) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (show -u ≤ 0 by linarith)
  have hrpos (j) (hj : j ≤ J) : 0 < r j := hδ.trans_le (hl j hj).1
  have hsurj (j) (hj : j < J) : Function.Surjective (f j) :=
    surjective_of_fiber_lower (f j) (show 0 < M j / 2 by have := (he j hj).2.1; linarith)
      (fun i => ((he j hj).2.2.1 i).1)
  have hn (j) (hj : j ≤ J) : (n j : ℝ) ≤ δ ^ (-7 : ℝ) :=
    (Nat.cast_le.mpr (layer_card_le n f J hsurj hj le_rfl)).trans hnJ
  have hlocal (j) (hj : j < J) (k : Fin (n j)) (W : Set Space) (hW : Convex ℝ W) :
      ENNReal.ofReal ((Set.ncard {i | f j i = k ∧
        Tube (r (j + 1)) (x (j + 1) i) (v (j + 1) i) ⊆ W} : ℝ) * (r (j + 1)) ^ 2) ≤
        ENNReal.ofReal (δ ^ (-u)) * volume W := by
    apply le_trans _ ((hl (j + 1) (by omega)).2.2.2.2 W hW)
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact Nat.cast_le.mpr (Set.ncard_le_ncard (fun _ hi => hi.2))
  obtain ⟨D, A, hA⟩ := hcopies J r (fun j => r j / 4) M (fun _ => δ ^ (-u)) n x v f
    (by
      intro j hj
      have hnext := hrpos (j + 1) (by omega)
      have hp := (hl j (by omega)).2.1
      have hh := he j hj
      exact ⟨hnext, by linarith [hh.1], by linarith, hh.2.1⟩)
    (by intro j hj i; exact ⟨((hl j (by omega)).2.2.2.1 i).1, ((he j hj).2.2.1 i).2⟩)
    (by
      intro j hj i
      exact ⟨((hl (j + 1) (by omega)).2.2.2.1 i).1,
        ((hl (j + 1) (by omega)).2.2.2.1 i).2, (he j hj).2.2.2 i⟩)
    hlocal
  refine ⟨D, A, ?_⟩
  intro j hj
  obtain ⟨hD, hlo, hhi, hmove, hcount⟩ := hA j hj
  have hr := hrpos j (by omega)
  have hr1 := (hl j (by omega)).2.1
  refine ⟨hD, ?_, ?_, ?_, ?_⟩
  · intro a i
    apply local_moved_containment (A j a) ((he j hj).2.2.2 i) _ (hmove a) (by linarith)
    exact (Metric.self_subset_thickening hr _).trans ((hl j (by omega)).2.2.2.1 (f j i)).2
  · intro i
    have hc := copied_fiber_fullness (L := 2) (show (0 : ℝ) < 2 by norm_num)
      (show M j ≤ 2 * (Set.ncard {s | f j s = i} : ℝ) by
        have := ((he j hj).2.2.1 i).1
        linarith) hlo
    norm_num at hc
    nlinarith
  · let i : Fin (n j) := ⟨0, (hl j (by omega)).2.2.1⟩
    have hm := regular_fiber_mass_bound (show 0 < r j / 4 by positivity)
      (show r j / 4 ≤ 1 by linarith) hL (x (j + 1)) (v (j + 1)) (f j)
      (x j i) (v j i) ((hl j (by omega)).2.2.2.1 i).1 i
      (by intro s hs; simpa only [hs] using (he j hj).2.2.2 s)
      (hl (j + 1) (by omega)).2.2.2.2 ((he j hj).2.2.1 i).1
    have hc := copy_mass_step (card_le_mul_of_fibers (f j) (fun k => ((he j hj).2.2.1 k).2)) hm hhi
    apply hc.trans
    have hk : 0 ≤ (n j : ℝ) * (r j) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hL1 hk]
  · intro k W hW
    apply (hcount k W hW).trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    have hp : (r (j + 1)) ^ (-u) ≤ δ ^ (-u) :=
      Real.rpow_le_rpow_of_nonpos hδ (hl (j + 1) (by omega)).1 (by linarith)
    have hlog' := hlog δ (n j) hδ hδ1 (Nat.cast_nonneg _) (hn j (by omega))
    have hlog0 : 0 ≤ Real.log (2 + (n j : ℝ)) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (n j); linarith)
    calc
      _ ≤ C₁ * δ ^ (-u) * (C₂ * δ ^ (-u)) * δ ^ (-u) := by gcongr
      _ = (C₁ * C₂) * δ ^ (-3 * u) := by
        rw [show -3 * u = -u + -u + -u by ring,
          Real.rpow_add hδ, Real.rpow_add hδ]
        ring

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
