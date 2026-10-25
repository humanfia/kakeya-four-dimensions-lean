-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.EndpointPairs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.Witness
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxGeometry
import Submission.WZ.Obl.wz_normalized_projection_iteration.Expansion
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SparsePackets

/- Adapted from this workspace: o197/x0567, d9e04e2b24c3, EndpointPairs.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory Metric
open scoped Classical
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V O P T I A)

/-- The entire prism is clear of the two endpoints of one fine tube. -/
def PrismData.PairAway {n : ℕ} (D : PrismData n) (ρ c R : ℝ)
    (x v : Fin n → V) (i : Fin n) (j : Fin D.L) : Prop :=
  ∀ p ∈ P D.a (ρ * c) c (D.z j) (D.e j),
    R < dist p (x i) ∧ R < dist p (x i + v i)

/-- If a prism is close to one fine endpoint, its whole incidence piece is
in a slightly larger ball around that endpoint. -/
theorem bad_pair_near_fine_ends {ω ζ δ h ρ c R : ℝ} {n o : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (H : D.Valid ω ζ δ h ρ c x v Y o)
    {i : Fin n} {j : Fin D.L} (hbad : ¬ D.PairAway ρ c R x v i j)
    {q : V} (hq : q ∈ D.W i j) :
    q ∈ closedBall (x i) (R + 2 * c) ∪ closedBall (x i + v i) (R + 2 * c) := by
  rcases H with ⟨ha, hab, hbc, _, hW, _⟩
  have hc : 0 < c := hδ.trans_le (ha.trans (hab.trans hbc))
  have hbox := WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_subset_closedBall
    hab hbc hc.le (D.z j) (D.e j)
  have hqz : dist q (D.z j) ≤ c := hbox ((hW i j).2.1 hq).2
  have hdiam (p : V) (hp : p ∈ P D.a (ρ * c) c (D.z j) (D.e j)) : dist q p ≤ 2 * c := by
    have hpz : dist p (D.z j) ≤ c := hbox hp
    calc
      _ ≤ dist q (D.z j) + dist (D.z j) p := dist_triangle _ _ _
      _ ≤ _ := by rw [dist_comm (D.z j) p]; linarith
  by_contra hn
  simp only [mem_union, mem_closedBall, not_or, not_le] at hn
  apply hbad
  intro p hp
  have hd := hdiam p hp
  constructor
  · linarith [dist_triangle q p (x i)]
  · linarith [dist_triangle q p (x i + v i)]

/-- The total mass of bad endpoint pairs is controlled solely by prism
length. The coarse radius does not enter this estimate. -/
theorem endpoint_pair_mass_loss {ω ζ δ h ρ c R : ℝ} {n o : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hR : 0 ≤ R)
    (hv : ∀ i, ‖v i‖ = 1) (hYT : ∀ i, Y i ⊆ T δ (x i) (v i))
    (H : D.Valid ω ζ δ h ρ c x v Y o) :
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => ¬ D.PairAway ρ c R x v i j),
      volume (D.W i j) ≤ O ((n : ℝ) * (2304 * (R + 2 * c) * δ ^ 2)) := by
  classical
  have Hcopy := H
  rcases Hcopy with ⟨ha, hab, hbc, _, hW, _⟩
  have hdc : δ ≤ c := ha.trans (hab.trans hbc)
  have hc : 0 < c := hδ.trans_le hdc
  have hdr : δ ≤ R + 2 * c := by linarith
  have hbad (i : Fin n) :
      ∑ j ∈ Finset.univ.filter (fun j => ¬ D.PairAway ρ c R x v i j), volume (D.W i j) ≤
        O (2304 * (R + 2 * c) * δ ^ 2) := by
    let B := Finset.univ.filter (fun j => ¬ D.PairAway ρ c R x v i j)
    have hm : volume (⋃ j ∈ B, D.W i j) = ∑ j ∈ B, volume (D.W i j) :=
      measure_biUnion_finset (fun j _ j' _ hne => (hW i j).2.2 j' hne) (fun j _ => (hW i j).1)
    rw [← hm]
    have hsub : (⋃ j ∈ B, D.W i j) ⊆
        (T δ (x i) (v i) ∩ closedBall (x i) (R + 2 * c)) ∪
          (T δ (x i) (v i) ∩ closedBall (x i + v i) (R + 2 * c)) := by
      intro p hp
      obtain ⟨j, hj, hp⟩ := mem_iUnion₂.mp hp
      have hpT := hYT i ((hW i j).2.1 hp).1
      have he := bad_pair_near_fine_ends D hδ H (Finset.mem_filter.mp hj).2 hp
      exact he.elim (fun hl => Or.inl ⟨hpT, hl⟩) (fun hr => Or.inr ⟨hpT, hr⟩)
    have hl := WangZahlLot.Obl.wz_normalized_projection_iteration.tube_inter_ball_volume_le
      hδ hdr (x i) (v i) (x i) (hv i)
    have hr := WangZahlLot.Obl.wz_normalized_projection_iteration.tube_inter_ball_volume_le
      hδ hdr (x i) (v i) (x i + v i) (hv i)
    apply (measure_mono hsub).trans ((measure_union_le _ _).trans ((add_le_add hl hr).trans ?_))
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact le_of_eq (congrArg O (by ring))
  apply (Finset.sum_le_sum (fun i _ => hbad i)).trans_eq
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [O, ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]

/-- At polynomially small length, all endpoint-clear pairs together keep
half the input incidence budget, even at macroscopic coarse radius. -/
theorem endpoint_pair_mass_fraction {ω ζ δ h ρ c R : ℝ} {n o : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hR : 0 ≤ R)
    (hbudget : 4608 * (R + 2 * c) ≤ δ ^ (2 * h))
    (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y)
    (H : D.Valid ω ζ δ h ρ c x v Y o) :
    (1 / 2 : ENNReal) * (∑ i, ∑ j, volume (D.W i j)) ≤
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => D.PairAway ρ c R x v i j), volume (D.W i j) := by
  classical
  let J (i : Fin n) := Finset.univ.filter (fun j => D.PairAway ρ c R x v i j)
  let B (i : Fin n) := Finset.univ.filter (fun j => ¬ D.PairAway ρ c R x v i j)
  have hbad := endpoint_pair_mass_loss D hδ hR (fun i => (hA.2.1 i).1)
    (fun i => (hA.2.1 i).2.2.2) H
  have hsmall : ∑ i, ∑ j ∈ B i, volume (D.W i j) ≤
      (1 / 2 : ENNReal) * (O (δ ^ h) * ∑ i, volume (Y i)) := by
    apply hbad.trans
    have hnum : (n : ℝ) * (2304 * (R + 2 * c) * δ ^ 2) ≤
        (1 / 2 : ℝ) * (δ ^ h * (δ ^ h * n * δ ^ 2)) := by
      have hp := mul_le_mul_of_nonneg_right hbudget (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg δ))
      have he : δ ^ (2 * h) = δ ^ h * δ ^ h := by
        rw [show 2 * h = h + h by ring, Real.rpow_add hδ]
      rw [he] at hp
      nlinarith
    calc
      _ ≤ O ((1 / 2 : ℝ) * (δ ^ h * (δ ^ h * n * δ ^ 2))) := ENNReal.ofReal_le_ofReal hnum
      _ = (1 / 2 : ENNReal) * (O (δ ^ h) * O (δ ^ h * n * δ ^ 2)) := by
        simp only [O]
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
        norm_num [ENNReal.ofReal_div_of_pos]
      _ ≤ _ := mul_le_mul' le_rfl (mul_le_mul' le_rfl hA.2.2.2.1)
  have hsplit : (∑ i, ∑ j ∈ J i, volume (D.W i j)) +
      (∑ i, ∑ j ∈ B i, volume (D.W i j)) = ∑ i, ∑ j, volume (D.W i j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hYfinite : (∑ i, volume (Y i)) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro i _
    exact ne_top_of_le_ne_top (measure_ball_ne_top (μ := volume) (x := (0 : V)) (r := 1))
      (measure_mono ((hA.2.1 i).2.2.2.trans (hA.2.1 i).2.1))
  have hMfinite : (∑ i, ∑ j, volume (D.W i j)) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro i _
    apply ENNReal.sum_ne_top.mpr
    intro j _
    exact ne_top_of_le_ne_top
      (ne_top_of_le_ne_top hYfinite (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i)))
      (measure_mono ((H.2.2.2.2.1 i j).2.1.trans inter_subset_left))
  exact WangZahlLot.Obl.wz_clustered_cover_volume_gain.half_mass_after_loss
    hMfinite (le_of_eq hsplit.symm)
    (hsmall.trans (mul_le_mul' le_rfl H.2.2.2.2.2.1))

/-- The retained endpoint-clear pairs also keep half the required input budget. -/
theorem endpoint_pair_mass_retention {ω ζ δ h ρ c R : ℝ} {n o : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hR : 0 ≤ R)
    (hbudget : 4608 * (R + 2 * c) ≤ δ ^ (2 * h))
    (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y)
    (H : D.Valid ω ζ δ h ρ c x v Y o) :
    (1 / 2 : ENNReal) * O (δ ^ h) * ∑ i, volume (Y i) ≤
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => D.PairAway ρ c R x v i j), volume (D.W i j) := by
  rw [mul_assoc]
  exact (mul_le_mul' le_rfl H.2.2.2.2.2.1).trans
    (endpoint_pair_mass_fraction D hδ hR hbudget hA H)

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
