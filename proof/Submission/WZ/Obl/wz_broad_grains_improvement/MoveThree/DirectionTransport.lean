-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.DirectionTransport.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/DirectionTransport.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 commit be976b9, DirectionTransport.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.UnitTransport

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit pd pd_triangle pd_symm)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (unit_pos_smul unit_linear_pd_le)

/-- On directions with bounded forward expansion, an invertible linear map
has a controlled inverse on projective directions. -/
theorem unit_linear_inverse_pd (A : V ≃ₗ[ℝ] V) {C B : ℝ}
    (hC : 0 ≤ C) (hB : 0 < B)
    (hInv : ∀ u, ‖A.symm u‖ ≤ C * ‖u‖)
    {u v : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hAu : ‖A u‖ ≤ B) :
    pd u v ≤ (2 * C * B) * pd (unit (A u)) (unit (A v)) := by
  have hpos (w : V) (hw : ‖w‖ = 1) : 0 < ‖A w‖ := by
    apply norm_pos_iff.mpr
    intro hz
    have hwz : w = 0 := A.injective (by simpa only [map_zero] using hz)
    simp only [hwz, norm_zero] at hw
    norm_num at hw
  have hundo (w : V) : A.symm (unit (A w)) = ‖A w‖⁻¹ • w := by
    rw [unit, map_smul, A.symm_apply_apply]
  have hnorm (w : V) (hw : ‖w‖ = 1) :
      ‖A.symm (unit (A w))‖ = ‖A w‖⁻¹ := by
    rw [hundo, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hpos w hw)), hw, mul_one]
  have hunit (w : V) (hw : ‖w‖ = 1) : unit (A.symm (unit (A w))) = w := by
    rw [hundo, unit_pos_smul (inv_pos.mpr (hpos w hw))]
    simp only [unit, hw, inv_one, one_smul]
  have hlo : B⁻¹ ≤ ‖A.symm (unit (A u))‖ := by
    rw [hnorm u hu]
    exact inv_anti₀ (hpos u hu) hAu
  have hv0 : A.symm (unit (A v)) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hnorm v hv]
    exact (inv_pos.mpr (hpos v hv)).ne'
  have H := unit_linear_pd_le A.symm.toLinearMap hC (inv_pos.mpr hB) hInv hlo hv0
  change pd (unit (A.symm (unit (A u)))) (unit (A.symm (unit (A v)))) ≤
    (2 * C / B⁻¹) * pd (unit (A u)) (unit (A v)) at H
  simpa only [hunit u hu, hunit v hv, div_inv_eq_mul] using H

/-- A projective inverse Lipschitz estimate transfers finite directional
broadness. The center of a nonempty cap is replaced by one of its directions. -/
theorem finite_subfamily_broad_transport {n : ℕ} (F F₀ : Finset (Fin n))
    (v v' : Fin n → V) {δ β B K : ℝ}
    (hδ : 0 < δ) (hB : 0 ≤ B) (hK : 1 ≤ K)
    (hFF : F ⊆ F₀)
    (hv : ∀ i ∈ F, ‖v i‖ = 1)
    (hpair : ∀ i ∈ F, ∀ j ∈ F, pd (v i) (v j) ≤ K * pd (v' i) (v' j))
    (hbr : ∀ u r, ‖u‖ = 1 → δ ≤ r →
      ((F₀.filter (fun i => pd (v i) u ≤ r)).card : ℝ) ≤ B * r ^ β * F₀.card) :
    ∀ u r, δ ≤ r →
      ((F.filter (fun i => pd (v' i) u ≤ r)).card : ℝ) ≤
        (B * (2 * K) ^ β) * r ^ β * F₀.card := by
  classical
  intro u r hr
  have hr0 : 0 < r := hδ.trans_le hr
  let Q := F.filter (fun i => pd (v' i) u ≤ r)
  by_cases hQ : Q.Nonempty
  · obtain ⟨j, hj⟩ := hQ
    obtain ⟨hjF, hjcap⟩ := Finset.mem_filter.mp hj
    have hsub : Q ⊆ F₀.filter (fun i => pd (v i) (v j) ≤ 2 * K * r) := by
      intro i hi
      obtain ⟨hiF, hicap⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_filter.mpr ⟨hFF hiF, ?_⟩
      have hangle : pd (v' i) (v' j) ≤ 2 * r := by
        have H := pd_triangle (v' i) u (v' j)
        rw [pd_symm u] at H
        linarith
      exact (hpair i hiF j hjF).trans (by nlinarith)
    have hδR : δ ≤ 2 * K * r := by nlinarith
    calc
      (Q.card : ℝ) ≤ ((F₀.filter (fun i => pd (v i) (v j) ≤ 2 * K * r)).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ ≤ B * (2 * K * r) ^ β * F₀.card := hbr (v j) _ (hv j hjF) hδR
      _ = _ := by rw [Real.mul_rpow (by positivity : 0 ≤ 2 * K) hr0.le]; ring
  · have hQ0 : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQ
    change (Q.card : ℝ) ≤ _
    rw [hQ0, Finset.card_empty, Nat.cast_zero]
    positivity

theorem finite_broad_transport {n : ℕ} (F : Finset (Fin n))
    (v v' : Fin n → V) {δ β B K : ℝ}
    (hδ : 0 < δ) (hB : 0 ≤ B) (hK : 1 ≤ K)
    (hv : ∀ i ∈ F, ‖v i‖ = 1)
    (hpair : ∀ i ∈ F, ∀ j ∈ F, pd (v i) (v j) ≤ K * pd (v' i) (v' j))
    (hbr : ∀ u r, ‖u‖ = 1 → δ ≤ r →
      ((F.filter (fun i => pd (v i) u ≤ r)).card : ℝ) ≤ B * r ^ β * F.card) :
    ∀ u r, δ ≤ r →
      ((F.filter (fun i => pd (v' i) u ≤ r)).card : ℝ) ≤
        (B * (2 * K) ^ β) * r ^ β * F.card :=
  finite_subfamily_broad_transport F F v v' hδ hB hK Finset.Subset.rfl hv hpair hbr

/-- Disjoint groups of comparable positive incidence counts inherit
broadness from the fine directions. `M` includes any pointwise loss caused
by restricting to the chosen groups. -/
theorem grouped_broad_of_fine {n L : ℕ} (F : Finset (Fin n))
    (J : Finset (Fin L)) (I : Fin L → Finset (Fin n))
    (v : Fin n → V) (w : Fin L → V) {δ β B m M s D : ℝ}
    (hδ : 0 < δ) (hB : 0 ≤ B) (hm : 0 < m) (hM : 0 ≤ M)
    (hsub : ∀ j ∈ J, I j ⊆ F)
    (hdisj : (↑J : Set (Fin L)).PairwiseDisjoint I)
    (hlower : ∀ j ∈ J, m ≤ (I j).card)
    (hupper : D ≤ M * m * J.card)
    (hclose : ∀ j ∈ J, ∀ i ∈ I j, pd (v i) (w j) ≤ s)
    (hbr : ∀ u r, δ ≤ r →
      ((F.filter (fun i => pd (v i) u ≤ r)).card : ℝ) ≤ B * r ^ β * D) :
    ∀ u r, δ ≤ r → s ≤ r →
      ((J.filter (fun j => pd (w j) u ≤ r)).card : ℝ) ≤
        (M * B * (2 : ℝ) ^ β) * r ^ β * J.card := by
  classical
  intro u r hr hsr
  have hr0 : 0 < r := hδ.trans_le hr
  let K := J.filter (fun j => pd (w j) u ≤ r)
  have hdisjK : (↑K : Set (Fin L)).PairwiseDisjoint I := by
    intro j hj k hk hjk
    exact hdisj (Finset.mem_of_mem_filter _ hj) (Finset.mem_of_mem_filter _ hk) hjk
  have hcard : m * K.card ≤ ((K.biUnion I).card : ℝ) := by
    rw [Finset.card_biUnion hdisjK]
    push_cast
    calc
      _ = ∑ _ ∈ K, m := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun j hj => hlower j (Finset.mem_of_mem_filter _ hj))
  have hcap : K.biUnion I ⊆ F.filter (fun i => pd (v i) u ≤ 2 * r) := by
    intro i hi
    obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨hjJ, hjcap⟩ := Finset.mem_filter.mp hj
    refine Finset.mem_filter.mpr ⟨hsub j hjJ hij, ?_⟩
    have H := pd_triangle (v i) (w j) u
    linarith [hclose j hjJ i hij]
  have H : m * K.card ≤ m * ((M * B * (2 : ℝ) ^ β) * r ^ β * J.card) := by
    calc
      _ ≤ ((K.biUnion I).card : ℝ) := hcard
      _ ≤ ((F.filter (fun i => pd (v i) u ≤ 2 * r)).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hcap)
      _ ≤ B * (2 * r) ^ β * D := hbr u _ (by linarith)
      _ ≤ B * (2 * r) ^ β * (M * m * J.card) := by gcongr
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr0.le]; ring
  exact (mul_le_mul_iff_right₀ hm).mp H

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
