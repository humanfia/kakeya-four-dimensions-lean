-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_tower_balanced_refinement.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_direction_density_transfer.Arithmetic

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_tower_balanced_refinement

open MeasureTheory Metric Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

abbrev Tube (d : ℝ) (x v : Space) : Set Space := thickening d (segment ℝ x (x + v))

abbrev ConvexCount (d L : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ W, Convex ℝ W → ENNReal.ofReal ((Set.ncard {i | Tube d (x i) (v i) ⊆ W} : ℝ) * d ^ 2)
    ≤ ENNReal.ofReal L * volume W

abbrev SlabCount (d L : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ (u : Space) (t r : ℝ), ‖u‖ = 1 → 0 < r →
    ENNReal.ofReal (Set.ncard {i | Tube d (x i) (v i) ⊆
      ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r}} : ℝ) ≤
    ENNReal.ofReal (L * n) * volume (ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r})

abbrev Admissible (d η M L : ℝ) (n : ℕ) (x v : Fin n → Space)
    (Y : Fin n → Set Space) : Prop :=
  0 < n ∧ (∀ i, ‖v i‖ = 1 ∧ Tube d (x i) (v i) ⊆ ball 0 1 ∧
    MeasurableSet (Y i) ∧ Y i ⊆ Tube d (x i) (v i)) ∧
  (∀ i j, i ≠ j → volume (Tube d (x i) (v i) ∩ Tube d (x j) (v j)) ≤
    1 / 2 * volume (Tube d (x i) (v i))) ∧
  ENNReal.ofReal (d ^ η * n * d ^ 2) ≤ ∑ i, volume (Y i) ∧
  ConvexCount d M n x v ∧ SlabCount d L n x v

abbrev GlobalTower (d L g : ℝ) (B n : ℕ) (x v : Fin n → Space) : Prop :=
  ∃ J : ℕ, 1 ≤ J ∧ J ≤ B ∧ ∃ (r : ℕ → ℝ) (N : ℕ → ℕ)
    (y w : ∀ j, Fin (N j) → Space) (f : ∀ j, Fin (N (j + 1)) → Fin (N j)),
    r 0 = 1 ∧ r J = d ∧ N 0 = 1 ∧
    (∃ u : Fin n ≃ Fin (N J), ∀ i, y J (u i) = x i ∧ w J (u i) = v i) ∧
    (∀ j, j ≤ J → ∀ k, ‖w j k‖ = 1) ∧
    (∀ j, j < J → 0 < r (j + 1) ∧ r (j + 1) < r j ∧ d ^ g * r j ≤ r (j + 1) ∧
      ∀ i, Tube (r (j + 1)) (y (j + 1) i) (w (j + 1) i) ⊆
        Tube (r j) (y j (f j i)) (w j (f j i))) ∧
    ∀ j, j ≤ J → ConvexCount (r j) L (N j) (y j) (w j)

lemma convexCount_mono {d L L' : ℝ} {n : ℕ} {x v : Fin n → Space}
    (h : ConvexCount d L n x v) (hL : L ≤ L') : ConvexCount d L' n x v := by
  intro W hW
  exact (h W hW).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hL) le_rfl)

lemma count_restrict {n m : ℕ} (a : Fin m → Fin n) (ha : Function.Injective a)
    (P : Fin n → Prop) : Set.ncard {i | P (a i)} ≤ Set.ncard {i | P i} := by
  exact Set.ncard_le_ncard_of_injOn a (fun _ h => h) ha.injOn

lemma convexCount_restrict {d L : ℝ} {n m : ℕ} {x v : Fin n → Space}
    (a : Fin m → Fin n) (ha : Function.Injective a) (h : ConvexCount d L n x v) :
    ConvexCount d L m (x ∘ a) (v ∘ a) := by
  intro W hW
  apply le_trans _ (h W hW)
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (count_restrict a ha (fun i => Tube d (x i) (v i) ⊆ W))) (sq_nonneg d)

/-- Only existence of finite constants is needed for admissibility after restriction. -/
lemma finite_constants {d : ℝ} (hd : 0 < d) {n : ℕ} (x v : Fin n → Space) :
    ∃ M L : ℝ, ConvexCount d M n x v ∧ SlabCount d L n x v := by
  obtain ⟨L, hL, h⟩ := WangZahlLot.Obl.wz_direction_density_transfer.finite_slab_bound hd x v
  refine ⟨(L * n) * d ^ 2, L, ?_, ?_⟩
  · intro W hW
    calc
      ENNReal.ofReal ((Set.ncard {i | Tube d (x i) (v i) ⊆ W} : ℝ) * d ^ 2) =
          ENNReal.ofReal (d ^ 2) * ENNReal.ofReal
            (Set.ncard {i | Tube d (x i) (v i) ⊆ W} : ℝ) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg d), mul_comm]
      _ ≤ ENNReal.ofReal (d ^ 2) * (ENNReal.ofReal (L * n) * volume W) :=
        mul_le_mul' le_rfl (h W)
      _ = ENNReal.ofReal ((L * n) * d ^ 2) * volume W := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg d), mul_comm (d ^ 2)]
  · intro u t r hu hr
    exact h _

end WangZahlLot.Obl.wz_tower_balanced_refinement
