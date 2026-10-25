-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.CentralAlignedFamily.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.CentralRecenter
import Submission.WZ.Obl.wz_multiscale_finite_tower.AlignedInitialization

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_multiscale_finite_tower
  (Admissible AlignedFamily axisMidpoint direction_cap_selection slabBound_comp
    midpoint_bound_of_unit_ball)
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives (convexExpansionLoss)

noncomputable section

/-- Central shadings can be aligned by an injective selection and an explicit
longitudinal shift. Each selected shading is kept in full. -/
theorem central_aligned_family : ∃ C₀ : ℝ, 1 ≤ C₀ ∧
    ∀ {d h M₀ L₀ : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V},
      0 < d → 0 ≤ M₀ → 0 ≤ L₀ → A d h M₀ L₀ n x v Y →
      (∀ i, ‖axisMidpoint (x i) (v i)‖ ≤ 1/2) →
      (∀ i, Y i ⊆ closedBall 0 (1/2)) →
    ∃ (k : ℕ) (j : Fin k → Fin n) (u : V), Function.Injective j ∧ k ≤ n ∧
      AlignedFamily d (d^h/2) (M₀*convexExpansionLoss 2)
        (512000000*L₀*n/k) u 0 k (fun i => recenterStart (x (j i)) (v (j i)))
          (v ∘ j) (Y ∘ j) ∧
      O (1/(2*C₀)) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Y (j i)) := by
  classical
  obtain ⟨C₀,hC₀,Hcap⟩ := direction_cap_selection
  refine ⟨C₀,hC₀,?_⟩
  intro d h M₀ L₀ n x v Y hd hM hL hA hmid hcentral
  have hCpos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hAb : Admissible d h M₀ L₀ n x v Y := hA
  obtain ⟨U,hU,hUmass,hUdense⟩ := hAb.heavy_indices hd
  have hUpos : 0 < ∑ i ∈ U, volume (Y i) :=
    (ENNReal.mul_pos (by norm_num) (hAb.mass_pos hd).ne').trans_le hUmass
  obtain ⟨S,hSU,hS,u,hu,hSmass,hdir⟩ := Hcap U v (fun i => (hA.2.1 i).1)
    (fun i => volume (Y i)) hUpos
  let a : Fin n → ℝ := fun i => -(inner ℝ (v i) (axisMidpoint (x i) (v i)))
  let X : Fin n → V := fun i => x i+a i•v i
  have hX (i : Fin n) : X i = recenterStart (x i) (v i) := by
    simp only [X,a,recenterStart,neg_smul,sub_eq_add_neg]
  have ha (i : Fin n) : |a i| ≤ 1/2 := by
    have hh := abs_real_inner_le_norm (v i) (axisMidpoint (x i) (v i))
    rw [(hA.2.1 i).1, one_mul] at hh
    simpa only [a,abs_neg] using hh.trans (hmid i)
  have hball (i : Fin n) : T d (X i) (v i) ⊆ I := by
    rw [hX]
    exact recenter_tube_in_ball (hA.2.1 i).1 (hA.2.1 i).2.1
  have hY (i : Fin n) : Y i ⊆ T d (X i) (v i) := by
    rw [hX]
    exact central_shading_subset_recenter (hA.2.1 i).1 (hA.2.1 i).2.2.2 (hcentral i)
  let j := WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate S
  have hj := WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate_injective S
  have hjS (i : Fin S.card) : j i ∈ S :=
    WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate_mem S i
  have hk : 0 < S.card := Finset.card_pos.mpr hS
  have hk0 : (S.card : ℝ) ≠ 0 := (Nat.cast_pos.mpr hk).ne'
  have hcount := (hAb.2.2.2.2.1.longitudinal_shift hd hM a ha hball).comp j hj
  have hslab := hAb.2.2.2.2.2.longitudinal_root_shift hd hL
    (fun i => (hA.2.1 i).2.1) a ha hball u hu
  have hslab' := slabBound_comp hslab j hj
    (show 512000000*L₀*n ≤ (512000000*L₀*n/S.card)*S.card by
      rw [div_mul_cancel₀ _ hk0])
  have hF : AlignedFamily d (d^h/2) (M₀*convexExpansionLoss 2)
      (512000000*L₀*n/S.card) u 0 S.card (X ∘ j) (v ∘ j) (Y ∘ j) := by
    refine ⟨hk,fun i => (hA.2.1 (j i)).1,fun i => hball (j i),
      fun i => (hA.2.1 (j i)).2.2.1,fun i => hY (j i),?_,hcount,hslab',hu,
      fun i => hdir (j i) (hjS i),?_,?_⟩
    · intro i
      convert hUdense (j i) (hSU (hjS i)) using 1
      · congr 1
        ring
      · rfl
    · intro i
      simpa only [Function.comp_apply,hX] using recenter_aligned (x := x (j i))
        (hA.2.1 (j i)).1
    · intro i
      exact midpoint_bound_of_unit_ball hd (hA.2.1 (j i)).1 (hball (j i))
  refine ⟨S.card,j,u,hj,by simpa using Finset.card_le_univ S,?_,?_⟩
  · simpa only [Function.comp_def,hX] using hF
  · change _ ≤ ∑ i, volume (Y (WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate S i))
    rw [WangZahlLot.Obl.wz_tower_balanced_refinement.sum_enumerate S
      (fun i => volume (Y i))]
    have hraw := mul_le_mul_right hSmass (O C₀⁻¹)
    have hcancel : O C₀⁻¹*O C₀ = 1 := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hCpos.le),inv_mul_cancel₀ hCpos.ne',
        ENNReal.ofReal_one]
    rw [← mul_assoc,hcancel,one_mul] at hraw
    have hh := (mul_le_mul_right hUmass (O C₀⁻¹)).trans hraw
    convert hh using 1
    rw [← mul_assoc,show (1/2:ENNReal) = O (1/2:ℝ) by
      norm_num [O, ENNReal.ofReal_div_of_pos],
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hCpos.le)]
    congr 2
    ring

end
end WangZahlLot.Obl.wz_broad_grains_improvement
