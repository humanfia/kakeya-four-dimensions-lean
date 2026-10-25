-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.EndpointPrisms.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.PrismSelect
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.EndpointGeometry
import Submission.WZ.Obl.wz_normalized_projection_iteration.Expansion
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SparsePackets

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, EndpointPrisms.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory Metric Classical
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V O T P I A)
open WangZahlLot.Obl.wz_coarse_grains_assembly (rIdx rIdx_mem rIdx_injective)

/-- Removing entire prisms near coarse endpoints loses at most half the
input incidence budget when both coarse radius and prism length are small.
Every surviving prism keeps its original density and broadness. -/
theorem endpoint_prism_mass_retention {ω ζ δ h ρ c R : ℝ} {n : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hR : 0 ≤ R)
    (hbudget : 4608 * (R + 2 * c + 6 * ρ) ≤ δ ^ (2 * h))
    (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y)
    (H : D.Valid ω ζ δ h ρ c x v Y 1) :
    (1 / 2 : ENNReal) * O (δ ^ h) * ∑ i, volume (Y i) ≤
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => D.Away ρ c R j), volume (D.W i j) := by
  classical
  let J := Finset.univ.filter (fun j => D.Away ρ c R j)
  let B := Finset.univ.filter (fun j => ¬ D.Away ρ c R j)
  let r := R + 2 * c + 6 * ρ
  have Hcopy := H
  rcases Hcopy with ⟨ha, hab, hbc, _, hW, hmass, _⟩
  have hc0 := hδ.trans_le (ha.trans (hab.trans hbc))
  have hρ0 : 0 < ρ := (mul_pos_iff.mp (hδ.trans_le (ha.trans hab))).resolve_right
    (by intro h; linarith [h.2]) |>.1
  have hdr : δ ≤ r := by
    dsimp only [r]
    linarith [ha.trans (hab.trans hbc)]
  have hbad (i : Fin n) : ∑ j ∈ B, volume (D.W i j) ≤ O (2304 * r * δ ^ 2) := by
    have hm : volume (⋃ j ∈ B, D.W i j) = ∑ j ∈ B, volume (D.W i j) :=
      measure_biUnion_finset (fun j _ j' _ hne => (hW i j).2.2 j' hne) (fun j _ => (hW i j).1)
    rw [← hm]
    have hsub : (⋃ j ∈ B, D.W i j) ⊆
        (T δ (x i) (v i) ∩ closedBall (x i) r) ∪
          (T δ (x i) (v i) ∩ closedBall (x i + v i) r) := by
      intro p hp
      obtain ⟨j, hj, hp⟩ := mem_iUnion₂.mp hp
      have hpT := (hA.2.1 i).2.2.2 ((hW i j).2.1 hp).1
      have he := bad_prism_near_fine_ends D hδ (fun i => (hA.2.1 i).1) H
        (Finset.mem_filter.mp hj).2 hp
      exact he.elim (fun hl => Or.inl ⟨hpT, hl⟩) (fun hr => Or.inr ⟨hpT, hr⟩)
    have hl := WangZahlLot.Obl.wz_normalized_projection_iteration.tube_inter_ball_volume_le
      hδ hdr (x i) (v i) (x i) (hA.2.1 i).1
    have hr := WangZahlLot.Obl.wz_normalized_projection_iteration.tube_inter_ball_volume_le
      hδ hdr (x i) (v i) (x i + v i) (hA.2.1 i).1
    apply (measure_mono hsub).trans ((measure_union_le _ _).trans ((add_le_add hl hr).trans ?_))
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact le_of_eq (congrArg O (by ring))
  have hbad_sum : ∑ i, ∑ j ∈ B, volume (D.W i j) ≤ O ((n : ℝ) * (2304 * r * δ ^ 2)) := by
    apply (Finset.sum_le_sum (fun i _ => hbad i)).trans_eq
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [O, ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  have hsmall : ∑ i, ∑ j ∈ B, volume (D.W i j) ≤
      (1 / 2 : ENNReal) * (O (δ ^ h) * ∑ i, volume (Y i)) := by
    apply hbad_sum.trans
    have hnum : (n : ℝ) * (2304 * r * δ ^ 2) ≤
        (1 / 2 : ℝ) * (δ ^ h * (δ ^ h * n * δ ^ 2)) := by
      have hp := mul_le_mul_of_nonneg_right hbudget (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg δ))
      have he : δ ^ (2 * h) = δ ^ h * δ ^ h := by
        rw [show 2 * h = h + h by ring, Real.rpow_add hδ]
      rw [he] at hp
      change 4608 * r * ((n : ℝ) * δ ^ 2) ≤ _ at hp
      nlinarith
    calc
      O ((n : ℝ) * (2304 * r * δ ^ 2)) ≤ O ((1 / 2 : ℝ) * (δ ^ h * (δ ^ h * n * δ ^ 2))) :=
        ENNReal.ofReal_le_ofReal hnum
      _ = (1 / 2 : ENNReal) * (O (δ ^ h) * O (δ ^ h * n * δ ^ 2)) := by
        simp only [O]
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
        norm_num [ENNReal.ofReal_div_of_pos]
      _ ≤ _ := mul_le_mul' le_rfl (mul_le_mul' le_rfl hA.2.2.2.1)
  have hsplit : (∑ i, ∑ j ∈ J, volume (D.W i j)) +
      (∑ i, ∑ j ∈ B, volume (D.W i j)) = ∑ i, ∑ j, volume (D.W i j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hYfinite : (∑ i, volume (Y i)) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro i _
    exact ne_top_of_le_ne_top (measure_ball_ne_top (μ := volume) (x := (0 : V)) (r := 1))
      (measure_mono ((hA.2.1 i).2.2.2.trans (hA.2.1 i).2.1))
  have hh := WangZahlLot.Obl.wz_clustered_cover_volume_gain.half_mass_after_loss
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hYfinite) (hmass.trans_eq hsplit.symm) hsmall
  simpa only [mul_assoc] using hh

/-- Whole-prism endpoint trimming produces valid data with clearance for
all fine tubes incident to every retained prism. -/
theorem exists_endpoint_clear_prisms {ω ζ δ h h' ρ c R : ℝ} {n : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hhh : h ≤ h') (hR : 0 ≤ R)
    (hbudget : 4608 * (R + 2 * c + 6 * ρ) ≤ δ ^ (2 * h))
    (herr : O (δ ^ h') ≤ (1 / 2 : ENNReal) * O (δ ^ h))
    (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y)
    (H : D.Valid ω ζ δ h ρ c x v Y 1) :
    ∃ D' : PrismData n, D'.a = D.a ∧ D'.L ≤ D.L ∧
      D'.Valid ω ζ δ h' ρ c x v Y 1 ∧
      ∀ i j, (D'.W i j).Nonempty → ∀ p ∈ P D'.a (ρ * c) c (D'.z j) (D'.e j),
        R < dist p (x i) ∧ R < dist p (x i + v i) := by
  classical
  let J := Finset.univ.filter (fun j => D.Away ρ c R j)
  let f := rIdx J
  have hm := endpoint_prism_mass_retention D hδ hR hbudget hA H
  have hsum (i : Fin n) : ∑ j : Fin J.card, volume (D.W i (f j)) = ∑ j ∈ J, volume (D.W i j) := by
    calc
      _ = ∑ j : J, volume (D.W i j.val) := J.equivFin.symm.sum_comp _
      _ = _ := Finset.sum_coe_sort J (fun j => volume (D.W i j))
  have hmass : O (δ ^ h') * ∑ i, volume (Y i) ≤ ∑ i, ∑ j, volume (D.W i (f j)) := by
    simp_rw [hsum]
    exact (mul_le_mul' herr le_rfl).trans hm
  refine ⟨D.select D.s f id (D.γ ∘ f), rfl, ?_,
    valid_select_prisms D hδ hδ1 hhh H f (rIdx_injective J) hmass, ?_⟩
  · simpa only [PrismData.select, Fintype.card_fin] using Fintype.card_le_of_injective f (rIdx_injective J)
  · intro i j hi p hp
    exact prism_endpoint_clearance D hδ (fun i => (hA.2.1 i).1) H hi
      (Finset.mem_filter.mp (rIdx_mem J j)).2 p hp

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
