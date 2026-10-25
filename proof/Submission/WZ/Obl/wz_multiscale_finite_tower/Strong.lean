-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.Strong.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Counts
import Submission.WZ.Obl.wz_multiscale_finite_tower.Scales

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

abbrev DoubledTube (r : ℝ) (y w : Space) : Set Space :=
  Tube (2 * r) (y - (1 / 2 : ℝ) • w) (2 • w)

/-- Slab counts normalized by the volume and cardinality of an assigned fibre. -/
def RelativeSlab (d L : ℝ) {n : ℕ} (x v : Fin n → Space)
    (P : Fin n → Prop) (W : Set Space) : Prop :=
  ∀ (u : Space) (t s : ℝ), ‖u‖ = 1 → 0 < s →
    ENNReal.ofReal (Set.ncard {i | P i ∧ Tube d (x i) (v i) ⊆
      W ∩ {p | |inner ℝ u p - t| ≤ s}} : ℝ) * volume W ≤
    ENNReal.ofReal (L * Set.ncard {i | P i}) * volume (W ∩ {p | |inner ℝ u p - t| ≤ s})

/-- The induction invariant also records slab counts inside each doubled parent. -/
def StrongTower (d L g : ℝ) (B n : ℕ) (x v : Fin n → Space) : Prop :=
  ∃ J : ℕ, 1 ≤ J ∧ J ≤ B ∧ ∃ (r : ℕ → ℝ) (N : ℕ → ℕ)
    (y w : ∀ j, Fin (N j) → Space) (f : ∀ j, Fin (N (j + 1)) → Fin (N j)),
    r 0 = 1 ∧ r J = d ∧ N 0 = 1 ∧
    (∃ u : Fin n ≃ Fin (N J), ∀ i, y J (u i) = x i ∧ w J (u i) = v i) ∧
    (∀ j, j ≤ J → ∀ k, ‖w j k‖ = 1) ∧
    (∀ j, j < J → 0 < r (j + 1) ∧ r (j + 1) < r j ∧ d ^ g * r j ≤ r (j + 1) ∧
      ∀ i, Tube (r (j + 1)) (y (j + 1) i) (w (j + 1) i) ⊆
        Tube (r j) (y j (f j i)) (w j (f j i))) ∧
    ∀ j, j < J → ∀ k,
      (∀ W, Convex ℝ W → ENNReal.ofReal ((Set.ncard {i | f j i = k ∧
        Tube (r (j + 1)) (y (j + 1) i) (w (j + 1) i) ⊆ W} : ℝ) * (r (j + 1)) ^ 2) ≤
          ENNReal.ofReal L * volume W) ∧
      RelativeSlab (r (j + 1)) L (y (j + 1)) (w (j + 1)) (fun i => f j i = k)
        (DoubledTube (r j) (y j k) (w j k))

lemma StrongTower.forget {d L g : ℝ} {B n : ℕ} {x v : Fin n → Space}
    (h : StrongTower d L g B n x v) : Tower false d L g B n x v := by
  obtain ⟨J, hJ, hJB, r, N, y, w, f, h0, hd, hN, hu, hw, hg, hl⟩ := h
  exact ⟨J, hJ, hJB, r, N, y, w, f, h0, hd, hN, hu, hw, hg, fun j hj k => (hl j hj k).1⟩

lemma doubled_root_contains_ball {w : Space} (hw : ‖w‖ = 1) :
    Metric.ball (0 : Space) 1 ⊆ DoubledTube 1 0 w := by
  intro p hp
  apply Metric.mem_thickening_iff.mpr
  refine ⟨0 - (1 / 2 : ℝ) • w, left_mem_segment _ _ _, ?_⟩
  rw [Metric.mem_ball, dist_zero_right] at hp
  rw [dist_eq_norm]
  have hb : ‖0 - (1 / 2 : ℝ) • w‖ = 1 / 2 := by simp [norm_smul, hw]
  calc
    ‖p - (0 - (1 / 2 : ℝ) • w)‖ ≤ ‖p‖ + ‖0 - (1 / 2 : ℝ) • w‖ := norm_sub_le _ _
    _ < 2 * 1 := by rw [hb]; linarith

lemma doubled_root_volume {w : Space} (hw : ‖w‖ = 1) :
    volume (DoubledTube 1 0 w) ≤ ENNReal.ofReal 4096 := by
  have hleft : 0 - (1 / 2 : ℝ) • w ∈ Metric.ball (0 : Space) 2 := by
    norm_num [Metric.mem_ball, dist_zero_right, norm_smul, hw]
  have he : 0 - (1 / 2 : ℝ) • w + 2 • w = (3 / 2 : ℝ) • w := by module
  have hright : 0 - (1 / 2 : ℝ) • w + 2 • w ∈ Metric.ball (0 : Space) 2 := by
    rw [he]
    norm_num [Metric.mem_ball, dist_zero_right, norm_smul, hw]
  have hseg := (convex_ball (0 : Space) (2 : ℝ)).segment_subset hleft hright
  have hsub : DoubledTube 1 0 w ⊆ Metric.ball (0 : Space) 4 := by
    intro p hp
    obtain ⟨z, hz, hpz⟩ := Metric.mem_thickening_iff.mp hp
    have hzball := hseg hz
    rw [Metric.mem_ball, dist_zero_right] at hzball ⊢
    have hn : ‖p‖ ≤ dist p z + ‖z‖ := by
      calc
        ‖p‖ = ‖(p - z) + z‖ := by simp
        _ ≤ ‖p - z‖ + ‖z‖ := norm_add_le _ _
        _ = _ := by rw [dist_eq_norm]
    linarith
  apply (measure_mono hsub).trans
  rw [EuclideanSpace.volume_ball_fin_three, ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 4),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4 ^ 3)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [Real.pi_lt_four]

/-- A single edge already has the strengthened slab invariant, at a fixed geometric cost. -/
theorem strong_tower_one {d L L0 g : ℝ} {n : ℕ} {x v : Fin n → Space}
    (hd : 0 < d) (hd1 : d < 1) (hg : 1 ≤ g) (hn : 0 < n)
    (hv : ∀ i, ‖v i‖ = 1) (hb : ∀ i, Tube d (x i) (v i) ⊆ Metric.ball 0 1)
    (hK : KatzTao d L n x v) (hF : Frostman d L0 n x v) (hL : 4096 * L0 ≤ L) :
    StrongTower d L g 1 n x v := by
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
  · intro j hj k
    have hj0 : j = 0 := by omega
    subst j
    constructor
    · intro W hW
      change ENNReal.ofReal ((Set.ncard {i : Fin n | (0 : Fin 1) = k ∧
        Tube d (x i) (v i) ⊆ W} : ℝ) * d ^ 2) ≤ ENNReal.ofReal L * volume W
      simpa only [Subsingleton.elim (0 : Fin 1) k, true_and] using hK W hW
    · change RelativeSlab d L x v (fun _ => (0 : Fin 1) = k) (DoubledTube 1 0 (v i₀))
      have hr := hF.relative hb (doubled_root_contains_ball (hv i₀))
        (by norm_num : (0 : ℝ) ≤ 4096) (doubled_root_volume (hv i₀)) hL
      simpa only [RelativeSlab, Subsingleton.elim (0 : Fin 1) k, true_and,
        Set.ofPred_true, Set.ncard_univ, Nat.card_fin] using hr

end WangZahlLot.Obl.wz_multiscale_finite_tower
