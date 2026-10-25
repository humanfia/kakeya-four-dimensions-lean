-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.Counts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Basic

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- Injectively selecting indices can only decrease the count in a fixed container. -/
theorem count_comp_le {n m : ℕ} (g : Fin m → Fin n) (hg : Function.Injective g)
    (P : Fin n → Prop) : Set.ncard {i : Fin m | P (g i)} ≤ Set.ncard {i : Fin n | P i} :=
  Set.ncard_le_ncard_of_injOn g (fun _ hi => hi) hg.injOn

theorem KatzTao.comp {d L : ℝ} {n m : ℕ} {x v : Fin n → Space}
    (h : KatzTao d L n x v) (g : Fin m → Fin n) (hg : Function.Injective g) :
    KatzTao d L m (x ∘ g) (v ∘ g) := by
  intro W hW
  apply le_trans (ENNReal.ofReal_le_ofReal _) (h W hW)
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (count_comp_le g hg (fun i => Tube d (x i) (v i) ⊆ W))) (sq_nonneg d)

/-- The Frostman constant scales by the ratio of the old and selected cardinalities. -/
theorem Frostman.comp {d L L' : ℝ} {n m : ℕ} {x v : Fin n → Space}
    (h : Frostman d L n x v) (g : Fin m → Fin n) (hg : Function.Injective g)
    (hL : L * n ≤ L' * m) : Frostman d L' m (x ∘ g) (v ∘ g) := by
  intro u t r hu hr
  apply le_trans _ ((h u t r hu hr).trans (mul_le_mul_of_nonneg_right
    (ENNReal.ofReal_le_ofReal hL) (by positivity)))
  exact ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr
    (count_comp_le g hg (fun i => Tube d (x i) (v i) ⊆
      Metric.ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r})))

/-- All geometric conditions survive an injective selection and measurable shading restriction. -/
theorem Admissible.comp {d η η' M L L' : ℝ} {n m : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (h : Admissible d η M L n x v Y)
    (g : Fin m → Fin n) (hg : Function.Injective g) (hm : 0 < m)
    (Z : Fin m → Set Space) (hZm : ∀ i, MeasurableSet (Z i)) (hZY : ∀ i, Z i ⊆ Y (g i))
    (hden : ENNReal.ofReal (d ^ η' * m * d ^ 2) ≤ ∑ i, volume (Z i))
    (hL : L * n ≤ L' * m) : Admissible d η' M L' m (x ∘ g) (v ∘ g) Z := by
  refine ⟨hm, ?_, ?_, hden, h.2.2.2.2.1.comp g hg, h.2.2.2.2.2.comp g hg hL⟩
  · intro i
    exact ⟨(h.2.1 (g i)).1, (h.2.1 (g i)).2.1, hZm i,
      (hZY i).trans (h.2.1 (g i)).2.2.2⟩
  · intro i j hij
    exact h.2.2.1 (g i) (g j) (fun hgg => hij (hg hgg))

/-- Convert the ball-normalized slab estimate to a relative slab estimate in a larger container. -/
theorem Frostman.relative {d L L' C : ℝ} {n : ℕ} {x v : Fin n → Space}
    (h : Frostman d L n x v) (hb : ∀ i, Tube d (x i) (v i) ⊆ Metric.ball 0 1)
    {W : Set Space} (hBW : Metric.ball (0 : Space) 1 ⊆ W)
    (hC : 0 ≤ C) (hW : volume W ≤ ENNReal.ofReal C) (hL : C * L ≤ L') :
    ∀ (u : Space) (t r : ℝ), ‖u‖ = 1 → 0 < r →
      ENNReal.ofReal (Set.ncard {i | Tube d (x i) (v i) ⊆
        W ∩ {p | |inner ℝ u p - t| ≤ r}} : ℝ) * volume W ≤
      ENNReal.ofReal (L' * n) * volume (W ∩ {p | |inner ℝ u p - t| ≤ r}) := by
  intro u t r hu hr
  let S : Set Space := {p | |inner ℝ u p - t| ≤ r}
  have hcount : Set.ncard {i | Tube d (x i) (v i) ⊆ W ∩ S} ≤
      Set.ncard {i | Tube d (x i) (v i) ⊆ Metric.ball 0 1 ∩ S} := by
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    intro i hi p hp
    exact ⟨hb i hp, (hi hp).2⟩
  have hbound : ENNReal.ofReal (Set.ncard {i | Tube d (x i) (v i) ⊆ W ∩ S} : ℝ) ≤
      ENNReal.ofReal (L * n) * volume (Metric.ball 0 1 ∩ S) :=
    (ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr hcount)).trans (h u t r hu hr)
  calc
    _ ≤ (ENNReal.ofReal (L * n) * volume (Metric.ball 0 1 ∩ S)) * ENNReal.ofReal C :=
      mul_le_mul hbound hW (by positivity) (by positivity)
    _ = ENNReal.ofReal (C * L * n) * volume (Metric.ball 0 1 ∩ S) := by
      rw [show C * L * (n : ℝ) = C * (L * n) by ring, ENNReal.ofReal_mul hC]
      ac_rfl
    _ ≤ ENNReal.ofReal (L' * n) * volume (W ∩ S) := by
      gcongr

end WangZahlLot.Obl.wz_multiscale_finite_tower
