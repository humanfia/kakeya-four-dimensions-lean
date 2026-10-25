-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.BoxRegularization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxNormalization
import Submission.WZ.Obl.wz_flat_factored_improvement.FlatRegularization

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement (gridKeys gridCell gridUnion)
open WangZahlLot.Obl.wz_flat_factored_improvement (flat_prism_regularization)

/-- Density regularization in cubes of the short box scale. The selected cubes
meet the original box, including when its middle width was truncated for normalization. -/
theorem box_regularization {δ a b c lam ρ : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a)
    (hab : a ≤ b) (haSmall : a ≤ 1 / 100) (hlam : 0 < lam) (hρ : 0 < ρ)
    {K : ℕ} (hK : 0 < K) (hcut : 432 * ρ ^ K * a * b ≤ lam * δ ^ 2 / 2)
    (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) {n : ℕ} (hn : 0 < n)
    (x v : Fin n → Space) (Y : Fin n → Set Space)
    (hv : ∀ i, ‖v i‖ = 1) (hYm : ∀ i, MeasurableSet (Y i))
    (hYT : ∀ i, Y i ⊆ Tube δ (x i) (v i))
    (hYB : ∀ i, Y i ⊆ ball (0 : Space) 1) (hYW : ∀ i, Y i ⊆ Box a b c z e)
    (hden : ∀ i, ENNReal.ofReal (lam * δ ^ 2) ≤ volume (Y i)) :
    ∃ (s : Finset (Fin 3 → ℤ)) (t : ℝ) (N : ℕ) (j : Fin N → Fin n),
      s ⊆ gridKeys a ∧ (∀ k ∈ s, (Box a b c z e ∩ gridCell a k).Nonempty) ∧
      0 < t ∧ 0 < N ∧ Function.Injective j ∧ lam / (224 * K) * n ≤ N ∧
      (∀ i, ENNReal.ofReal (lam / (4 * K) * δ ^ 2) ≤ volume (Y (j i) ∩ gridUnion a s)) ∧
      (∀ k ∈ s, t * a ^ 3 ≤ volume.real ((⋃ i, Y i) ∩ gridCell a k)) ∧
      ρ * volume.real (⋃ i, Y (j i) ∩ gridUnion a s) ≤ t * (432 * a * b) := by
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have habmin : a ≤ min b 2 := le_min hab (haSmall.trans (by norm_num))
  have hYnorm : ∀ i, Y i ⊆ normalFrame b z e ''
      WangZahlLot.Obl.wz_flat_factored_improvement.StandardPrism a (min b 2) := by
    intro i p hp
    exact box_unitBall_subset_normalPrism ha.le hb.le z e
      ⟨hYW i hp, ball_subset_closedBall (hYB i hp)⟩
  have hcut' : 432 * ρ ^ K * a * min b 2 ≤ lam * δ ^ 2 / 2 := by
    apply le_trans _ hcut
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
  obtain ⟨s, t, N, j, hs, _, ht, hN, hj, hret, hden', hloc, htotal⟩ :=
    flat_prism_regularization hδ hδa habmin (min_le_right _ _)
      (haSmall.trans (by norm_num)) hlam hρ hK hcut' (normalFrame b z e) hn
      x v Y hv hYm hYT hYB hYnorm hden
  refine ⟨s, t, N, j, hs, ?_, ht, hN, hj, hret, hden', hloc, ?_⟩
  · intro k hk
    have hp : 0 < volume.real ((⋃ i, Y i) ∩ gridCell a k) :=
      (mul_pos ht (pow_pos ha 3)).trans_le (hloc k hk)
    have hne : ((⋃ i, Y i) ∩ gridCell a k).Nonempty := by
      by_contra hnone
      rw [Set.not_nonempty_iff_eq_empty.mp hnone] at hp
      simp at hp
    obtain ⟨p, hpY, hpk⟩ := hne
    obtain ⟨i, hi⟩ := mem_iUnion.mp hpY
    exact ⟨p, hYW i hi, hpk⟩
  · exact htotal.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)) ht.le)

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
