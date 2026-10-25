-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.SourceCopy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.StageEstimates
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.ShiftedCopy
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.MassBudget
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Budgets
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Certificates

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped BigOperators

/-- A prepared buffered source tower suffices for the entire copying and
hierarchy construction, with uniform losses chosen before the small scale. -/
theorem source_tower_copies (hSS : SingleScale) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (B : ℕ) :
    ∃ u : ℝ, 0 < u ∧ ∃ d : ℝ, 0 < d ∧ ∃ C : ℝ, 0 < C ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ (m : ℕ) (x v : Fin m → Space) (H : ℝ),
        δ ^ u * H ≤ (m : ℝ) → SourceTower Tube δ a u B m x v →
        ∃ (N m' : ℕ) (A : Fin N → (Space ≃ᵃⁱ[ℝ] Space))
          (c : Fin m' → Fin m) (g : Fin m' → Fin N) (x' v' : Fin m' → Space),
          0 < m' ∧ (N : ℝ) * H * δ ^ 2 ≤ C * δ ^ (-a) ∧
          (∀ s, x' s = A (g s) (x (c s)) ∧ v' s = (A (g s)).linear (v (c s))) ∧
          FullHierarchy δ a b B m' x' v' := by
  classical
  let κ : ℝ := (1 / 100) ^ 2
  have hκ : 0 < κ := by norm_num [κ]
  have hκ1 : κ ≤ 1 := by norm_num [κ]
  obtain ⟨u, hu, hua, hbudget⟩ := iteration_budgets ha hb hκ hκ1 B
  obtain ⟨C₁, hC₁, hstage⟩ := buffered_stage_estimates hSS hu
  obtain ⟨d, hd, hsmall⟩ := hbudget C₁ hC₁
  refine ⟨u, hu, min d (1 / 2), lt_min hd (by norm_num), 49 ^ B, by positivity, ?_⟩
  intro δ hδ hδd m x v H hH hsource
  have hδsmall : δ ≤ d := hδd.trans (min_le_left _ _)
  have hδ1 : δ < 1 := lt_of_le_of_lt (hδd.trans (min_le_right _ _)) (by norm_num)
  rcases hsource with ⟨J, hJ, hJB, r, n, z, w, f, M, hr0, hrJ, hn0,
    ⟨e, he⟩, htop, hm, hl, hedges⟩
  have hmn : m = n J := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  have hglobal : ∀ j, j ≤ J → δ ≤ r j ∧ r j ≤ 1 ∧ 0 < n j ∧
      (∀ i, ‖w j i‖ = 1 ∧ Tube (r j) (z j i) (w j i) ⊆ Metric.ball 0 1) ∧
      WangZahlLot.Obl.wz_tower_convex_count_composition.Counts
        (r j) (δ ^ (-u)) (n j) (z j) (w j) := by
    intro j hj
    obtain ⟨hlo, hhi, hn, htubes, hcounts⟩ := hl j hj
    refine ⟨hlo, hhi.trans (by norm_num), hn, ?_, hcounts⟩
    intro i
    exact ⟨(htubes i).1, (htubes i).2.trans (Metric.ball_subset_ball (by norm_num))⟩
  obtain ⟨D, A, hA⟩ := hstage δ hδ hδ1.le J r M n z w f (hmn ▸ hm) hglobal
    (by
      intro j hj
      obtain ⟨hsep, _, hM, hbranch, hsub⟩ := hedges j hj
      exact ⟨hsep, hM, hbranch, hsub⟩)
  let L := max 1 (C₁ * δ ^ (-3 * u))
  obtain ⟨hupper, hlower⟩ := hsmall δ hδ hδ1.le hδsmall (J + 1)
    (C₁ * δ ^ (-3 * u)) (by omega) (by positivity) le_rfl
  have hhierarchy := hierarchy_of_shifted_copies hδ hδ1 ha
    (show (0 : ℝ) < 1 / 100 by norm_num) (show (1 / 100 : ℝ) ≤ 1 by norm_num)
    (le_max_left 1 _) hκ hκ1 (le_refl κ) (show κ ≤ 1 / 32 by norm_num [κ])
    hJB r n D z w f A hr0 hrJ hn0 (hl J le_rfl).2.2.1
    (fun j hj => (hA j hj).1)
    (fun j hj => ⟨(hl j hj).1, (hglobal j hj).2.1⟩)
    (by
      intro j hj
      have hrpos : 0 < r (j + 1) := hδ.trans_le (hl (j + 1) (by omega)).1
      have := (hedges j hj).1
      linarith)
    htop (fun j hj => (hedges j hj).2.1)
    (fun j hj i => ((hl j hj).2.2.2.1 i).1)
    (fun i => ((hglobal 0 (by omega)).2.2.2.1 i).2)
    (fun j hj => (hA j hj).2.1) (fun j hj => (hA j hj).2.2.1)
    (by
      intro j hj i W hW
      exact ((hA j hj).2.2.2.2 i W hW).trans
        (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right 1 _)) le_rfl))
    hupper hlower
  let I := MotionWord D J × Fin (n J)
  let ef : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let em : Fin (Fintype.card (MotionWord D J)) ≃ MotionWord D J :=
    (Fintype.equivFin (MotionWord D J)).symm
  let At (i) := composedMotion D A J (em i)
  let c (s : Fin (Fintype.card I)) := e.symm (ef s).2
  let g (s : Fin (Fintype.card I)) := em.symm (ef s).1
  let xt (s : Fin (Fintype.card I)) := composedMotion D A J (ef s).1 (z J (ef s).2)
  let vt (s : Fin (Fintype.card I)) := (composedMotion D A J (ef s).1).linear (w J (ef s).2)
  refine ⟨Fintype.card (MotionWord D J), Fintype.card I, At, c, g, xt, vt, ?_, ?_, ?_, hhierarchy⟩
  · simp only [I, Fintype.card_prod, card_motionWord, Fintype.card_fin]
    exact Nat.mul_pos (Finset.prod_pos (fun j hj => (hA j (Finset.mem_range.mp hj)).1))
      (hl J le_rfl).2.2.1
  · rw [card_motionWord]
    apply motion_mass_budget hδ hδ1.le hu hua (by omega) D n r hrJ _ (hmn ▸ hH)
      (fun j hj => (hA j hj).2.2.2.1)
    rw [hn0, hr0]
    norm_num
  · intro s
    obtain ⟨hx, hv⟩ := he (e.symm (ef s).2)
    simp only [e.apply_symm_apply] at hx hv
    dsimp only [xt, vt, At, g, c]
    rw [em.apply_symm_apply, hx, hv]
    exact ⟨rfl, rfl⟩

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
