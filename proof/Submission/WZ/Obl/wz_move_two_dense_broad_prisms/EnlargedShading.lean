-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.EnlargedShading.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.BallPrismSelection

/-! Local shadings in the selected enlarged prism. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set Metric MeasureTheory
open scoped ENNReal

/-- Regularity at an old-grain point places a fixed amount of each selected
fine shading inside one enlarged prism. -/
theorem enlarged_shading_selection {n : ℕ} {d a b c L t : ℝ}
    (hd : 0 < d) (hda : d ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hc1 : c ≤ 1) (hL : 100000000*c ≤ L) (ht : 0 < t)
    (x v : Fin n → V) (hv : ∀ i, ‖v i‖ = 1)
    (z : V) (e : V ≃ₗᵢ[ℝ] V) (H : Finset (Fin n)) (hH : H.Nonempty)
    (U : Fin n → Set V) (hUm : ∀ i, MeasurableSet (U i))
    (hUT : ∀ i, U i ⊆ T d (x i) (v i))
    (hcross : ∀ i ∈ H, Crosses d a b c (x i) (v i) z e)
    (hmeet : ∀ i ∈ H, ∃ p ∈ U i ∩ P a b c z e,
      4*L ≤ dist p (x i) ∧ 4*L ≤ dist p (x i+v i))
    (hreg : ∀ i p, p ∈ U i → O (L*t/256) ≤ volume (U i ∩ ball p (L/8))) :
    ∃ (F : Finset (Fin n)) (g : V ≃ₗᵢ[ℝ] V) (Q : Fin n → Set V),
      F.Nonempty ∧ F ⊆ H ∧ (H.card : ℝ) ≤ 1000000000*(L/c)^3*(F.card : ℝ) ∧
      d ≤ 10000*a ∧ 10000*a ≤ 10000*enlargedSlope b c*L ∧
      10000*enlargedSlope b c*L ≤ L ∧
      (∀ i, MeasurableSet (Q i) ∧ Q i ⊆ U i ∩
        P (10000*a) (10000*enlargedSlope b c*L) L z g ∧ Q i ⊆ ball z (L/2)) ∧
      (∀ i, i ∉ F → Q i = ∅) ∧
      ∀ i ∈ F, O (L*t/256) ≤ volume (Q i) ∧
        Crosses d (10000*a) (10000*enlargedSlope b c*L) L (x i) (v i) z g := by
  classical
  have ha : 0 < a := hd.trans_le hda
  have hc : 0 < c := ha.trans_le (hab.trans hbc)
  have hLp : 0 < L := by linarith
  let en : Fin H.card → Fin n := fun k => (H.equivFin.symm k).val
  have henmem (k) : en k ∈ H := (H.equivFin.symm k).property
  have heninj : Function.Injective en := Subtype.val_injective.comp H.equivFin.symm.injective
  obtain ⟨S, g, hS, hcard, hdA, hAB, hBL, hcore, hgood⟩ :=
    enlarged_prism_selection_all (Finset.card_pos.mpr hH) hd hda hab hbc hc1 hL
      (x ∘ en) (v ∘ en) z e (fun i => hv _)
      (fun i => hcross _ (henmem i)) (fun i => by
        obtain ⟨p, hp, he1, he2⟩ := hmeet _ (henmem i)
        exact ⟨p, ⟨hUT _ hp.1, hp.2⟩, he1, he2⟩)
      (fun _ => 1) (fun _ => by norm_num) (by simpa using (Nat.cast_pos.mpr (Finset.card_pos.mpr hH) : (0:ℝ) < H.card))
  let F := S.image en
  let Q : Fin n → Set V := fun i => if i ∈ F then U i ∩ ball z (L/2) else ∅
  have hFsub : F ⊆ H := by
    intro i hi
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
    exact henmem k
  have hQsub (i) : Q i ⊆ U i := by
    by_cases hi : i ∈ F
    · simp only [Q, ite_eq_left hi]; exact inter_subset_left
    · simp only [Q, ite_eq_right hi]; exact empty_subset _
  have hQball (i) : Q i ⊆ ball z (L/2) := by
    by_cases hi : i ∈ F
    · simp only [Q, ite_eq_left hi]; exact inter_subset_right
    · simp only [Q, ite_eq_right hi]; exact empty_subset _
  have hFg (i) (hi : i ∈ F) :
      Crosses d (10000*a) (10000*enlargedSlope b c*L) L (x i) (v i) z g ∧
      T d (x i) (v i) ∩ ball z (L/2) ⊆ P (10000*a) (10000*enlargedSlope b c*L) L z g := by
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
    exact hgood k hk
  refine ⟨F, g, Q, hS.image _, hFsub, ?_, hdA, hAB, hBL, ?_, ?_, ?_⟩
  · have he : F.card = S.card := Finset.card_image_of_injective _ heninj
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, he] using hcard
  · intro i
    refine ⟨?_, ?_, hQball i⟩
    · dsimp [Q]
      split_ifs
      · exact (hUm i).inter measurableSet_ball
      · exact MeasurableSet.empty
    · intro p hp
      have hi : i ∈ F := by
        by_contra hh
        simp only [Q, ite_eq_right hh, mem_empty_iff_false] at hp
      exact ⟨hQsub i hp, (hFg i hi).2 ⟨hUT i (hQsub i hp), hQball i hp⟩⟩
  · intro i hi
    simp only [Q, ite_eq_right hi]
  · intro i hi
    refine ⟨?_, (hFg i hi).1⟩
    obtain ⟨p, hp, _, _⟩ := hmeet i (hFsub hi)
    refine (hreg i p hp.1).trans (measure_mono ?_)
    rw [show Q i = U i ∩ ball z (L/2) by simp only [Q, ite_eq_left hi]]
    apply inter_subset_inter_right
    intro q hq
    have hpz : dist p z ≤ c := wz_clustered_cover_volume_gain.frozen_prism_norm ha.le hab hbc z e hp.2
    have hqp : dist q p < L/8 := hq
    have hqz := dist_triangle q p z
    change dist q z < L/2
    linarith

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
