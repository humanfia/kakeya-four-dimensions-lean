-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.PreparedMesh.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.AssignedCover
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.InputCounts
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Mesh
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.SmallRoot

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_tower_convex_count_composition (Counts counts_mono)

/-- Restricting the fine assignment and applying a common motion preserves the
supply of convex-counted coarse covers. -/
theorem cover_supply_rigid_subfamily {δ η : ℝ} {n m : ℕ} {x v : Fin n → Space}
    (D : Space ≃ᵃⁱ[ℝ] Space) (c : Fin m → Fin n) (hs : CoverSupply δ η n x v) :
    CoverSupply δ η m (fun i => D (x (c i))) (fun i => D.linear (v (c i))) := by
  intro ρ₀ hδρ hρ1
  obtain ⟨ρ, hlo, hhi, k, y, w, f, hw, hsub, hc⟩ := hs ρ₀ hδρ hρ1
  exact ⟨ρ, hlo, hhi, k, (fun i => D (y i)), (fun i => D.linear (w i)), f ∘ c,
    (fun i => rigid_unit D (hw i)), (fun i => rigid_containment D (hsub (c i))),
    counts_rigid D hc⟩

/-- Any positive-radius tube controls the location of its core, hence of its
enlargements. -/
theorem tube_ball_enlargement {s R r : ℝ} (hs : 0 < s) {y w : Space}
    (hball : Tube s y w ⊆ ball 0 R) : Tube r y w ⊆ ball 0 (R + r) := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  have hq' : ‖q‖ < R := by
    simpa only [mem_ball, dist_zero_right] using hball (self_subset_thickening hs _ hq)
  have hh := dist_triangle p q 0
  simp only [dist_zero_right] at hh
  simpa only [mem_ball, dist_zero_right] using (show ‖p‖ < R + r by linarith)

/-- Choose the occupied covers on the mesh, add the small root and the exact
fine family, and certify that every enlarged layer stays inside the fixed ball. -/
theorem prepared_assigned_mesh {δ η u b : ℝ} {J m : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hu : 0 < u) (hη : 0 < η)
    (hJ : 0 < J) (hm : 0 < m) (hb : 0 < b) (hb1 : b ≤ 1) (hbJ : b ^ J = δ)
    (hsmall : δ ^ (-η) * b ≤ (1 / 51200 : ℝ))
    (hcountbudget : 32 ^ 2 * δ ^ (-η) ≤ δ ^ (-u))
    (x v : Fin m → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hsupply : CoverSupply δ η m x v) (hfine : Counts δ (δ ^ (-u)) m x v)
    (y₀ w₀ : Space) (hw₀ : ‖w₀‖ = 1)
    (hroot : ∀ i, Tube δ (x i) (v i) ⊆ Tube (1 / 3200 : ℝ) y₀ w₀)
    (hrootball : Tube (1 / 100 : ℝ) y₀ w₀ ⊆ ball 0 (3 / 4 : ℝ)) :
    ∃ s : ℕ → ℝ,
      ∃ H : ∀ j, AssignedCover δ (s j) (if j < J then 32 * s j else δ) (δ ^ (-u)) m x v,
        s 0 = (1 / 3200 : ℝ) ∧ s J = δ ∧ (H 0).n = 1 ∧
        (∃ e : Fin m ≃ Fin (H J).n, ∀ i, (H J).z (e i) = x i ∧ (H J).w (e i) = v i) ∧
        (∀ j, 0 < j → j ≤ J → b ^ j ≤ s j ∧ s j ≤ δ ^ (-η) * b ^ j) ∧
        (∀ j, j ≤ J → ∀ i, Tube (if j < J then 32 * s j else δ) ((H j).z i) ((H j).w i) ⊆
          ball 0 (3 / 4 : ℝ)) := by
  classical
  have hL : 1 ≤ δ ^ (-u) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (show -u ≤ 0 by linarith)
  have hq : 1 ≤ δ ^ (-η) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (show -η ≤ 0 by linarith)
  have hex (j : ℕ) : ∃ s : ℝ,
      ∃ H : AssignedCover δ s (if j < J then 32 * s else δ) (δ ^ (-u)) m x v,
        (j = 0 → s = 1 / 3200 ∧ H.n = 1 ∧
          ∀ i, Tube (if j < J then 32 * s else δ) (H.z i) (H.w i) ⊆ ball 0 (3 / 4 : ℝ)) ∧
        (J ≤ j → s = δ ∧ ∃ e : Fin m ≃ Fin H.n,
          ∀ i, H.z (e i) = x i ∧ H.w (e i) = v i) ∧
        (0 < j → j ≤ J → b ^ j ≤ s ∧ s ≤ δ ^ (-η) * b ^ j) := by
    by_cases hj0 : j = 0
    · subst j
      let R : ℝ := if 0 < J then 32 * (1 / 3200) else δ
      have hR : R = 1 / 100 := by simp only [R, ite_eq_left hJ]; norm_num
      let H : AssignedCover δ (1 / 3200) R (δ ^ (-u)) m x v := {
        n := 1, z := fun _ => y₀, w := fun _ => w₀, assign := fun _ => 0,
        onto := fun i => ⟨⟨0, hm⟩, Subsingleton.elim _ _⟩,
        unit := fun _ => hw₀, contains := hroot,
        counts := counts_mono (singleton_convex_counts (by rw [hR]; norm_num)
          rfl (fun _ => y₀) (fun _ => w₀) (fun _ => hw₀)) hL }
      refine ⟨1 / 3200, H, ?_, ?_, ?_⟩
      · intro _
        refine ⟨rfl, rfl, ?_⟩
        intro i
        change Tube R y₀ w₀ ⊆ _
        rwa [hR]
      · intro hh
        omega
      · intro hh
        omega
    · by_cases hj : j < J
      · have hδbase : δ ≤ b ^ j := by
          rw [← hbJ]
          exact pow_le_pow_of_le_one hb.le hb1 (by omega)
        obtain ⟨ρ, hlo, hhi, k, y, w, f, hw, hsub, hc⟩ :=
          hsupply (b ^ j) hδbase (pow_le_one₀ hb.le hb1)
        have hρ : 0 < ρ := hδ.trans_le (hδbase.trans hlo)
        obtain ⟨H'⟩ := occupied_cover y w f hw hsub
          (counts_mono (counts_enlarged hρ.le (show (1 : ℝ) ≤ 32 by norm_num) y w hc) hcountbudget)
        let H : AssignedCover δ ρ (if j < J then 32 * ρ else δ) (δ ^ (-u)) m x v :=
          by simpa only [ite_eq_left hj] using H'
        exact ⟨ρ, H, (fun h => (hj0 h).elim), (fun h => (Nat.not_le.mpr hj h).elim),
          (fun _ _ => ⟨hlo, hhi⟩)⟩
      · let H : AssignedCover δ δ (if j < J then 32 * δ else δ) (δ ^ (-u)) m x v := {
          n := m, z := x, w := v, assign := id, onto := Function.surjective_id,
          unit := hv, contains := fun _ => Set.Subset.rfl,
          counts := by simpa only [ite_eq_right hj] using hfine }
        refine ⟨δ, H, (fun h => (hj0 h).elim), ?_, ?_⟩
        · intro _
          exact ⟨rfl, Equiv.refl _, fun _ => ⟨rfl, rfl⟩⟩
        · intro _ hjJ
          have he : j = J := by omega
          rw [he, hbJ]
          exact ⟨le_rfl, le_mul_of_one_le_left hδ.le hq⟩
  choose s H hzero hlast hscale using hex
  obtain ⟨hs0, hn0, hball0⟩ := hzero 0 rfl
  obtain ⟨hsJ, e, he⟩ := hlast J le_rfl
  refine ⟨s, H, hs0, hsJ, hn0, ⟨e, he⟩, hscale, ?_⟩
  intro j hj i
  by_cases hj0 : j = 0
  · subst j
    exact hball0 i
  · have hsj : 0 < s j := (pow_pos hb j).trans_le (hscale j (by omega) hj).1
    have hsjhi : s j ≤ 1 / 51200 := by
      calc
        s j ≤ δ ^ (-η) * b ^ j := (hscale j (by omega) hj).2
        _ ≤ δ ^ (-η) * b := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hδ.le _)
          simpa only [pow_one] using pow_le_pow_of_le_one hb.le hb1 (show 1 ≤ j by omega)
        _ ≤ _ := hsmall
    obtain ⟨l, hl⟩ := (H j).onto i
    have hsub := (H j).contains l
    rw [hl] at hsub
    have hR : (if j < J then 32 * s j else δ) ≤ 32 * s j := by
      split_ifs with h
      · rfl
      · have he : j = J := by omega
        rw [he, hsJ]
        linarith
    apply (enlarged_common_descendant (R := if j < J then 32 * s j else δ)
      hδ hsj (hv l) ((H j).unit i) hsub (hroot l)).trans
    apply (Metric.thickening_mono (show
      (if j < J then 32 * s j else δ) + 1 / 3200 + 4 * s j ≤ (1 / 100 : ℝ) by linarith) _).trans
    exact hrootball

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
