-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.Tower.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Basic

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- The containing unit ball supplies a single root for the original family. -/
theorem tower_one {d L g : ℝ} {n : ℕ} {x v : Fin n → Space}
    (hd : 0 < d) (hd1 : d < 1) (hg : 1 ≤ g) (hn : 0 < n)
    (hv : ∀ i, ‖v i‖ = 1) (hb : ∀ i, Tube d (x i) (v i) ⊆ Metric.ball 0 1)
    (hK : KatzTao d L n x v) : Tower false d L g 1 n x v := by
  let i₀ : Fin n := ⟨0, hn⟩
  let r : ℕ → ℝ := fun j => match j with | 0 => 1 | _ + 1 => d
  let N : ℕ → ℕ := fun j => match j with | 0 => 1 | _ + 1 => n
  let y : ∀ j, Fin (N j) → Space := fun j => match j with
    | 0 => fun _ => 0
    | _ + 1 => x
  let w : ∀ j, Fin (N j) → Space := fun j => match j with
    | 0 => fun _ => v i₀
    | _ + 1 => v
  let f : ∀ j, Fin (N (j + 1)) → Fin (N j) := fun j => match j with
    | 0 => fun _ => 0
    | _ + 1 => fun i => i
  refine ⟨1, le_rfl, le_rfl, r, N, y, w, f, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact ⟨Equiv.refl _, fun _ => ⟨rfl, rfl⟩⟩
  · intro j hj k
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · exact hv i₀
    · exact hv k
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    refine ⟨hd, hd1, ?_, ?_⟩
    · change d ^ g * 1 ≤ d
      simpa using Real.rpow_le_rpow_of_exponent_ge hd hd1.le hg
    · intro i
      change Tube d (x i) (v i) ⊆ Tube 1 0 (v i₀)
      exact (hb i).trans (Metric.ball_subset_thickening (left_mem_segment ℝ 0 (0 + v i₀)) 1)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    intro j hj k W hW
    have hj0 : j = 0 := by omega
    subst j
    change ENNReal.ofReal ((Set.ncard {i : Fin n | (0 : Fin 1) = k ∧
      Tube d (x i) (v i) ⊆ W} : ℝ) * d ^ 2) ≤ ENNReal.ofReal L * volume W
    simpa only [Subsingleton.elim (0 : Fin 1) k, true_and] using hK W hW

/-- Increasing the length bound, the gap exponent, or the count constant preserves a tower. -/
theorem Tower.mono {b : Bool} {d L L' g g' : ℝ} {B B' n : ℕ} {x v : Fin n → Space}
    (h : Tower b d L g B n x v) (hd : 0 < d) (hd1 : d ≤ 1)
    (hL : L ≤ L') (hg : g ≤ g') (hB : B ≤ B') : Tower b d L' g' B' n x v := by
  obtain ⟨J, hJ, hJB, r, N, y, w, f, hr0, hrJ, hN0, hbottom, hw, hedge, hcount⟩ := h
  have hrpos : ∀ j, j ≤ J → 0 < r j := by
    intro j hj
    cases j with
    | zero => simp [hr0]
    | succ j => exact (hedge j (by omega)).1
  refine ⟨J, hJ, hJB.trans hB, r, N, y, w, f, hr0, hrJ, hN0, hbottom, hw, ?_, ?_⟩
  · intro j hj
    obtain ⟨hr, hrr, hgap, hsub⟩ := hedge j hj
    refine ⟨hr, hrr, le_trans ?_ hgap, hsub⟩
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 hg) (hrpos j hj.le).le
  · cases b with
    | false =>
      intro j hj k W hW
      exact (hcount j hj k W hW).trans (by gcongr)
    | true =>
      intro j hj
      exact (hcount j hj).mono hL

/-- The initial family itself is the retained refinement at depth zero. -/
theorem initial_refinement {d η ε : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (hd : 0 < d) (hd1 : d < 1) (hε : 0 ≤ ε) (hη : η ≤ ε)
    (h : Admissible d η (d ^ (-η)) (d ^ (-η)) n x v Y) :
    ∃ (m : ℕ) (x' v' : Fin m → Space) (Y' : Fin m → Set Space) (M L : ℝ),
      Admissible d ε M L m x' v' Y' ∧ (⋃ j, Y' j) ⊆ (⋃ i, Y i) ∧
      ENNReal.ofReal (d ^ ε) * (∑ i, volume (Y i)) ≤ ∑ j, volume (Y' j) ∧
      Tower false d (d ^ (-ε)) 2 1 m x' v' := by
  have hA := h.mono_error hd hd1.le hη
  refine ⟨n, x, v, Y, d ^ (-ε), d ^ (-ε), hA, Set.Subset.rfl, ?_, ?_⟩
  · exact mul_le_of_le_one_left (by positivity)
      ((ENNReal.ofReal_le_one).mpr (Real.rpow_le_one hd.le hd1.le hε))
  · exact tower_one hd hd1 (by norm_num) h.1
      (fun i => (h.2.1 i).1) (fun i => (h.2.1 i).2.1) hA.2.2.2.2.1

end WangZahlLot.Obl.wz_multiscale_finite_tower
