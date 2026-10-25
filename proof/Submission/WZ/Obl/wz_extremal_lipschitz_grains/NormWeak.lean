-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.NormWeak.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormCovers
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormSelect
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormDegree

/-!
# All-scale covers of the zoomed family

Given finitely many levels of original covers (each with its partition, balance and local
convex counts), a selection `Q` without conflicts at each level and with retention `t`, and a
family of zoomed scales covering `[lam δ, 1]` up to the factor `(lam δ) ^ (-η₁)`, the zoomed
family satisfies o060's `Weak` hypothesis.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory Finset
open scoped ENNReal
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate enumerate_mem CoverAt)

theorem CoverAt.mono_K {n k : ℕ} {δ K K' ρ : ℝ} {x v : Fin n → Space} {z w : Fin k → Space}
    (h : CoverAt δ K ρ x v z w) (hK : K ≤ K') : CoverAt δ K' ρ x v z w := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, h3, h4, fun j j' => (h5 j j').trans ?_, fun j W hW => (h6 j W hW).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg _)
  · gcongr

open scoped Classical in
/-- The zoomed family satisfies the all-scale cover hypothesis. -/
theorem weak_zoom {n L : ℕ} {c : Space} {lam δ η η₁ t : ℝ} {x v : Fin n → Space}
    {Q : Finset (Fin n)} (k : Fin L → ℕ) (z w : ∀ m, Fin (k m) → Space) (ρ : Fin L → ℝ)
    (f : ∀ m, Fin n → Fin (k m))
    (hlam : 1 ≤ lam) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 ≤ η) (hlδ : lam * δ ≤ 1 / 4)
    (hv : ∀ i, ‖v i‖ = 1)
    (hglob : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal ({i | tube δ (x i) (v i) ⊆ W}.ncard : ℝ) ≤
        ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume W)
    (hδρ : ∀ m, δ ≤ ρ m) (hR : ∀ m, lam * (25 * ρ m) ≤ 1 / 10000)
    (hw : ∀ m j, ‖w m j‖ = 1)
    (hsep : ∀ m j j', j ≠ j' → volume (tube (ρ m) (z m j) (w m j) ∩ tube (ρ m) (z m j') (w m j')) ≤
      (1 / 2 : ℝ≥0∞) * volume (tube (ρ m) (z m j) (w m j)))
    (hf : ∀ m i j, tube δ (x i) (v i) ⊆ tube (ρ m) (z m j) (w m j) ↔ f m i = j)
    (hbal : ∀ m j j', ((univ.filter (fun i => f m i = j)).card : ℝ) ≤
      δ ^ (-η) * ((univ.filter (fun i => f m i = j')).card : ℝ))
    (hfrost : ∀ m j (W : Set Space), Convex ℝ W →
      ENNReal.ofReal (((univ.filter (fun i => f m i = j ∧ tube δ (x i) (v i) ⊆ W)).card : ℝ) *
        ρ m ^ 2) ≤ ENNReal.ofReal (δ ^ (-η) * ((univ.filter (fun i => f m i = j)).card : ℝ)) *
          volume W)
    (ht : 0 < t) (hQ : Q ⊆ zoomThrough c lam x v) (hQne : Q.Nonempty)
    (hnc : ∀ m, ∀ i ∈ Q, ∀ i' ∈ Q, f m i ≠ f m i' →
      ¬ conflict c lam (lam * (25 * ρ m)) (z m) (w m)
        (fun j => ∃ i ∈ zoomThrough c lam x v, f m i = j) (f m i) (f m i'))
    (hret : ∀ m j, (Q.filter (fun i => f m i = j)).Nonempty →
      t * ((univ.filter (fun i => f m i = j)).card : ℝ) ≤ ((Q.filter (fun i => f m i = j)).card : ℝ))
    (hret0 : t * (n : ℝ) ≤ (Q.card : ℝ))
    (hscales : ∀ r : ℝ, lam * δ ≤ r → r ≤ 1 →
      (∃ m, r ≤ lam * (25 * ρ m) ∧ lam * (25 * ρ m) ≤ (lam * δ) ^ (-η₁) * r) ∨
        1 ≤ (lam * δ) ^ (-η₁) * r)
    (hC1 : 5000000 * lam ^ 2 * δ ^ (-η) / t ≤ (lam * δ) ^ (-η₁))
    (hC2 : 8000 * δ ^ (-η) / t ≤ (lam * δ) ^ (-η₁)) :
    WangZahlLot.Obl.wz_separated_cover_refinement.Weak η₁ (lam * δ) Q.card (zx c lam x v Q)
      (zv v Q) := by
  intro r hr hr1
  rcases hscales r hr hr1 with ⟨m, hm1, hm2⟩ | htop
  · refine ⟨lam * (25 * ρ m), hm1, ?_, hm2, ?_⟩
    · have := hR m; linarith
    obtain ⟨k', hk', z', w', hcov⟩ := coverAt_zoom (f m) hlam hδ (hδρ m) (hR m) hv (hw m)
      (hsep m) (hf m) (hbal m) (hfrost m) (Real.rpow_nonneg hδ.le _) ht hQ hQne (hnc m) (hret m)
    exact ⟨k', hk', z', w', CoverAt.mono_K hcov hC1⟩
  · refine ⟨1, hr1, le_rfl, htop, 1, one_pos,
      fun _ => -(1 / 2 : ℝ) • zv v Q ⟨0, card_pos.mpr hQne⟩,
      fun _ => zv v Q ⟨0, card_pos.mpr hQne⟩, ?_⟩
    exact CoverAt.mono_K (coverAt_zoom_top hlam hδ hδ1 hη hlδ hv hglob ht hQ hQne hret0) hC2

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
