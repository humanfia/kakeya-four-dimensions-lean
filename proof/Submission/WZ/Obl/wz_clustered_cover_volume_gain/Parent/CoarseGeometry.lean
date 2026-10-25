-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.CoarseGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoarseCounts

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

noncomputable section

theorem point_box_dist_le_twelve {a b : ℝ} (ha : a ≤ 8) (hb : b ≤ 8)
    {z p : Space} {e : Space ≃ₗᵢ[ℝ] Space} (hp : p ∈ Factor.box a b 8 z e) :
    dist p z ≤ 12 := by
  have h0 : |e (p - z) 0| ≤ 4 := by linarith [hp.1]
  have h1 : |e (p - z) 1| ≤ 4 := by linarith [hp.2.1]
  have h2 : |e (p - z) 2| ≤ 4 := by convert hp.2.2 using 1 <;> norm_num
  have hs0 : (e (p - z) 0) ^ 2 ≤ 16 := by
    nlinarith [sq_abs (e (p - z) 0), pow_le_pow_left₀ (abs_nonneg _) h0 2]
  have hs1 : (e (p - z) 1) ^ 2 ≤ 16 := by
    nlinarith [sq_abs (e (p - z) 1), pow_le_pow_left₀ (abs_nonneg _) h1 2]
  have hs2 : (e (p - z) 2) ^ 2 ≤ 16 := by
    nlinarith [sq_abs (e (p - z) 2), pow_le_pow_left₀ (abs_nonneg _) h2 2]
  have hn := wz_affine_robust_cluster_estimate.norm_sq_coords (e (p - z))
  rw [e.norm_map] at hn
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (p - z)]

/-- Every point of a centered carrier lies within its radius plus half its length. -/
theorem carrier_dist_center_lt {L ρ : ℝ} (hL : 0 ≤ L) {z w p : Space}
    (hw : ‖w‖ = 1) (hp : p ∈ Carrier L ρ (z - (1 / 2 : ℝ) • w) w) :
    dist p z < ρ + L / 2 := by
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨s, hs, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq
  have heq : z - (1 / 2 : ℝ) • w + ((1 - L) / 2) • w + s • (L • w) - z =
      (L * (s - 1 / 2)) • w := by module
  have habs : |L * (s - 1 / 2)| ≤ L / 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [hs.1, hs.2]
  have hqz : dist (z - (1 / 2 : ℝ) • w + ((1 - L) / 2) • w + s • (L • w)) z ≤ L / 2 := by
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, hw, mul_one]
    exact habs
  exact (dist_triangle p _ z).trans_lt (add_lt_add_of_lt_of_le hpq hqz)

namespace Interfaces

/-- The center of every assigned box stays within a fixed ball, including after selection. -/
theorem factored_center_norm_lt {δ η h ρ K m a b : ℝ} {n N L : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N} {U : Finset (Fin N)}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {g : Fin N → Fin L}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hA : A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f)
    (hcover : Factor.AssignedCover 4 ρ K y w U m a b L z e g) :
    ∀ j : Fin L, ‖z j‖ < 13 := by
  classical
  intro j
  have ha : 0 < a := hδ.trans_le (hδρ.trans hcover.width)
  have hb : 0 < b := ha.trans_le hcover.ordered
  have hpacket : (U.filter fun k => g k = j).Nonempty := by
    by_contra hn
    have hr := hcover.rich j
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty, Nat.cast_zero,
      zero_mul, mul_zero] at hr
    have hp : 0 < m * (a * b * (2 * 4)) := mul_pos hcover.coefficient_pos (by positivity)
    linarith
  obtain ⟨k, hk⟩ := hpacket
  obtain ⟨hkU, hkj⟩ := Finset.mem_filter.mp hk
  obtain ⟨i, hiS, hfi⟩ := c_fibers_nonempty hδ hA hC k
  have hxi : x i ∈ T δ (x i) (v i) :=
    self_subset_thickening hδ _ (left_mem_segment ℝ _ _)
  have hxiI : ‖x i‖ < 1 := by simpa only [I, mem_ball, dist_zero_right] using (hA.2.1 i).2.1 hxi
  have hxiT : x i ∈ T ρ (y k) (w k) := by
    simpa only [hfi] using hC.2.2.2.1 i hiS hxi
  have hxiB : x i ∈ Factor.box a b 8 (z j) (e j) := by
    simpa only [hkj, show (2 : ℝ) * 4 = 8 by norm_num] using hcover.covers k hkU hxiT
  have hb8 : b ≤ 8 := by simpa only [show (2 : ℝ) * 4 = 8 by norm_num] using hcover.bounded
  have hd := point_box_dist_le_twelve (hcover.ordered.trans hb8) hb8 hxiB
  have ht := norm_le_norm_add_norm_sub (x i) (z j)
  rw [← dist_eq_norm] at ht
  linarith

/-- The enlarged coarse carriers are uniformly bounded in the original coordinates. -/
theorem factored_carrier_subset_ball {δ η h ρ K m a b : ℝ} {n N L : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N} {U : Finset (Fin N)}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {g : Fin N → Fin L}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hA : A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f)
    (hcover : Factor.AssignedCover 4 ρ K y w U m a b L z e g) :
    ∀ j : Fin L, factoringCarrier b (z j) (e j) ⊆ ball 0 42 := by
  intro j p hp
  have hw : ‖(e j).symm (EuclideanSpace.single 2 (1 : ℝ))‖ = 1 := by simp
  have hd := carrier_dist_center_lt (by norm_num : (0 : ℝ) ≤ 8) hw hp
  have hz := factored_center_norm_lt hδ hδρ hA hC hcover j
  have hb8 : b ≤ 8 := by simpa only [show (2 : ℝ) * 4 = 8 by norm_num] using hcover.bounded
  have ht := norm_le_norm_add_norm_sub (z j) p
  rw [← dist_eq_norm, dist_comm] at ht
  rw [mem_ball, dist_zero_right]
  linarith

end Interfaces

end

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
