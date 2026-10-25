-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.NormLevels.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormWeak

/-!
# Levels of original covers in Finset form

One level of the separated all-scale covers of the original family, with the containment
partition `f` and the balance and local convex counts rewritten with `Finset` cardinalities.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory Finset
open scoped ENNReal
open WangZahlLot.Obl.wz_separated_cover_refinement (ncard_setOf)

open scoped Classical in
theorem level_of_separated {η δ r : ℝ} {n : ℕ} {x v : Fin n → Space}
    (hS : Separated η δ n x v) (hδr : δ ≤ r) (hr1 : r ≤ 1) :
    ∃ (ρ : ℝ) (k : ℕ) (z w : Fin k → Space) (f : Fin n → Fin k),
      r ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ δ ^ (-η) * r ∧ (∀ j, ‖w j‖ = 1) ∧
      (∀ j j', j ≠ j' → volume (tube ρ (z j) (w j) ∩ tube ρ (z j') (w j')) ≤
        (1 / 2 : ℝ≥0∞) * volume (tube ρ (z j) (w j))) ∧
      (∀ i j, tube δ (x i) (v i) ⊆ tube ρ (z j) (w j) ↔ f i = j) ∧
      (∀ j j', ((univ.filter (fun i => f i = j)).card : ℝ) ≤
        δ ^ (-η) * ((univ.filter (fun i => f i = j')).card : ℝ)) ∧
      (∀ j (W : Set Space), Convex ℝ W →
        ENNReal.ofReal (((univ.filter (fun i => f i = j ∧ tube δ (x i) (v i) ⊆ W)).card : ℝ) *
          ρ ^ 2) ≤ ENNReal.ofReal (δ ^ (-η) * ((univ.filter (fun i => f i = j)).card : ℝ)) *
            volume W) := by
  classical
  obtain ⟨ρ, hrρ, hρ1, hρr, k, hk, z, w, hw, hsep, huniq, hfull, hbal, hfrost, -⟩ :=
    hS r hδr hr1
  choose f hf using huniq
  have hiff : ∀ i j, tube δ (x i) (v i) ⊆ tube ρ (z j) (w j) ↔ f i = j := by
    intro i j
    constructor
    · intro h; exact (hf i).2 j h |>.symm
    · intro h; rw [← h]; exact (hf i).1
  have hcount : ∀ j, ({i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j)}.ncard : ℝ) =
      ((univ.filter (fun i => f i = j)).card : ℝ) := by
    intro j
    simp_rw [hiff]
    exact_mod_cast ncard_setOf (fun i : Fin n => f i = j)
  have hcountW : ∀ j (W : Set Space), ({i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j) ∧
      tube δ (x i) (v i) ⊆ W}.ncard : ℝ) =
      ((univ.filter (fun i => f i = j ∧ tube δ (x i) (v i) ⊆ W)).card : ℝ) := by
    intro j W
    simp_rw [hiff]
    exact_mod_cast ncard_setOf (fun i : Fin n => f i = j ∧ tube δ (x i) (v i) ⊆ W)
  refine ⟨ρ, k, z, w, f, hrρ, hρ1, hρr, hw, hsep, hiff, ?_, ?_⟩
  · intro j j'
    have h := hbal j j'
    rwa [hcount, hcount] at h
  · intro j W hW
    have h := hfrost j W hW
    rwa [hcountW, hcount] at h

/-- A cover containing a tube through the zoom centre has its start within `3` of the centre. -/
theorem cover_near_center {n : ℕ} {c : Space} {lam δ ρ : ℝ} (hlam : 1 ≤ lam) (hδ : 0 < δ)
    (hρ : ρ ≤ 1 / 6) {x v : Fin n → Space} (hv : ∀ i, ‖v i‖ = 1) {z w : Space} (hw : ‖w‖ = 1)
    {i : Fin n} (hi : i ∈ zoomThrough c lam x v) (hT : tube δ (x i) (v i) ⊆ tube ρ z w) :
    ‖c - z‖ ≤ 3 := by
  have hlam0 : 0 < lam := by linarith
  obtain ⟨t, ht, hct⟩ := mem_zoomThrough.mp hi
  have h4 : 1 / (4 * lam) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  have hcx : ‖c - x i‖ ≤ 1 + 1 / 4 := by
    calc ‖c - x i‖ = ‖(c - (x i + t • v i)) + t • v i‖ := by congr 1; abel
      _ ≤ ‖c - (x i + t • v i)‖ + ‖t • v i‖ := norm_add_le _ _
      _ ≤ 1 / 4 + 1 := by
          rw [norm_smul, hv i, mul_one, Real.norm_eq_abs, abs_of_nonneg ht.1]
          linarith [ht.2]
      _ = 1 + 1 / 4 := by ring
  have hcxv : ‖c - (x i + v i)‖ ≤ 1 + 1 / 4 := by
    calc ‖c - (x i + v i)‖ = ‖(c - (x i + t • v i)) - (1 - t) • v i‖ := by congr 1; module
      _ ≤ ‖c - (x i + t • v i)‖ + ‖(1 - t) • v i‖ := norm_sub_le _ _
      _ ≤ 1 / 4 + 1 := by
          rw [norm_smul, hv i, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
          linarith [ht.1]
      _ = 1 + 1 / 4 := by ring
  rcases endpoints_close hδ (hv i) hw hT with ⟨h0, -⟩ | ⟨-, h1⟩
  · calc ‖c - z‖ ≤ ‖c - x i‖ + ‖x i - z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 3 := by linarith
  · calc ‖c - z‖ ≤ ‖c - (x i + v i)‖ + ‖x i + v i - z‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 3 := by linarith

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
