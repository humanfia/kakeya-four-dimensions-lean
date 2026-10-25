-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.LocalCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.CoverTransport
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.CoverParameters
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.MassTransfer
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.Balance
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.AlternativeTypes

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (axis)

attribute [local irreducible] normalize

set_option maxHeartbeats 1000000 in
lemma local_cover_of_normalized {ζ ω θ η r s : ℝ} (hζ : 0 < ζ)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hθ1 : θ ≤ 1) (hθτ : θ ≤ ζ / 100)
    (hη : 0 < η) (hητ : η ≤ ζ / 100) (hr : 0 < r) (hr1 : r ≤ 1)
    (hs : 0 < s) (hsr : s ≤ r) (hs1 : s ≤ 1 / 100)
    {q : ℕ} (hq : 0 < q) (hτq : 4 < (ζ / 100) * q)
    (hsmall : normalizedRadius r s ≤ contraction ^ 2)
    (hqsmall : (normalizedRadius r s) ^ (ζ / 100) * (q : ℝ) ≤ 1)
    (hrsmall : (normalizedRadius r s) ^ (ω / 100) ≤ 1 / (100 * coverScale))
    (hmasssmall : (s / r) ^ ζ ≤ (normalizedRadius r s) ^ (3 * (ζ / 100)))
    (herrorsmall : coverError * (normalizedRadius r s) ^ (-(6 * (ζ / 100))) ≤ (s / r) ^ (-ζ))
    {y w : Space} (hw : ‖w‖ = 1) (e : Space ≃ₗᵢ[ℝ] Space) (hew : e w = axis)
    {n M : ℕ} (x v : Fin n → Space) (Y : Fin n → Set Space)
    (hF : Fibre r s η y w x v Y) (j : Fin M → Fin n) (hj : Function.Injective j)
    (z u : Fin M → Space)
    (hA : Admissible (normalizedRadius r s) θ ((normalizedRadius r s) ^ (-θ))
      ((normalizedRadius r s) ^ (-θ)) z u (fun i => normalize e y w r hr '' Y (j i)))
    (hforward : ∀ i, normalize e y w r hr '' tube s (x (j i)) (v (j i)) ⊆ tube (normalizedRadius r s) (z i) (u i))
    (hmid : ∀ i, z i + (1 / 2 : ℝ) • u i = normalize e y w r hr (x (j i) + (1 / 2 : ℝ) • v (j i)))
    (hselected : ENNReal.ofReal ((normalizedRadius r s) ^ θ) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Y (j i)))
    (hG : GlobalCover (normalizedRadius r s) (ζ / 100) ω z u (fun i => normalize e y w r hr '' Y (j i))) :
    FibreCover r s ζ coverScale ω y w x v Y := by
  classical
  let d := normalizedRadius r s
  let τ := ζ / 100
  let δ := s / r
  let A := normalize e y w r hr
  have hd : 0 < d := normalizedRadius_pos hr hs
  have hd1 : d ≤ 1 := hsmall.trans (by norm_num)
  have hdlt : d < 1 := hsmall.trans_lt (by norm_num)
  have hδ : 0 < δ := div_pos hs hr
  have hδ1 : δ ≤ 1 := (div_le_one hr).mpr hsr
  have hdδ : d ≤ δ := by
    rw [show d = 4 * contraction * δ from radius_eq_ratio r s]
    norm_num [contraction]
    linarith only [hδ]
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨S, Z, ρ, N, zc, uc, f, hZ, hmass, hρlo, hρhi, huc, hcontain, hK, hFunused, hSf⟩ := hG
  let Zp := fun i => A ⁻¹' Z i
  obtain ⟨hZp, hmassp⟩ := pullback_shadings A (by positivity : 0 < jacobian r)
    (normalize_volume e y w hr) (fun i => Y (j i)) Z hZ hmass
  have hMcount : (M : ℝ) * d ^ 2 ≤ d ^ (-θ) * 8 := by
    simpa only [mul_comm] using admissible_card_bound hA (Real.rpow_pos_of_pos hd _).le
  have hMq : (M : ℝ) < (d ^ (-τ)) ^ q :=
    WangZahlLot.Obl.wz_tower_balanced_refinement.cardinal_lt_power hd hd1 hθ1 (by norm_num)
      (by have hh := hsmall; norm_num [contraction] at hh; dsimp [d]; linarith only [hh]) hτq hMcount
  have hB1 : 1 < d ^ (-τ) := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hd hdlt (neg_neg_of_pos hτ)
  obtain ⟨S', hS, hmassbal, hwhole, hbal⟩ := balance_whole_fibres hq hB1 hMq S f (fun i => volume (Zp i))
  have hmassbal' := absorb_finite_weight hd hqsmall hmassbal
  have hmassall : ENNReal.ofReal (d ^ (3 * τ)) * (∑ i, volume (Y i)) ≤ ∑ i ∈ S', volume (Zp i) :=
    retained_three_powers hd hd1 hθτ hselected hmassp hmassbal'
  have hden : ENNReal.ofReal (d ^ τ * n * s ^ 2) ≤ ∑ i, volume (Y i) := by
    have hp : d ^ τ ≤ δ ^ η :=
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 hητ).trans
        (Real.rpow_le_rpow hd.le hdδ hη.le)
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _)) (sq_nonneg s))).trans hF.2.2.1
  have hret := retained_card_of_mass hd hs (hs1.trans (by norm_num)) x v Y j Zp S'
    (fun i => (hF.2.1 i).1) (fun i => (hZp i).2.trans (hF.2.1 (j i)).2.2.2) hden hmassall
  have hρ : 0 < ρ := (Real.rpow_pos_of_pos hd _).trans_le hρlo
  have hρsmall := hρhi.trans hrsmall
  obtain ⟨N', X, V, g, hN', hV, hchild, hKp, hSbp, hSfp⟩ :=
    transport_balanced_cover e hew hr hr1 hs hs1 hρ hρsmall hsmall
      (Real.rpow_pos_of_pos hd _).le (by positivity : 0 < d ^ (4 * τ) / 56)
      (Real.rpow_pos_of_pos hδ _).le (Real.rpow_pos_of_pos hd _).le hw hF.1
      x v j hj z u zc uc f S S' hS hwhole hret hbal
      (fun i => (hF.2.1 i).1) (fun i => (hA.2.1 i).1) huc
      (fun i => (hF.2.1 i).2.1) hforward hmid hcontain hK hF.2.2.2.2 hSf
  have hexp : d ^ (-τ) ≤ d ^ (-(6 * τ)) :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith only [hτ])
  have hKloss : coarseConvexLoss * d ^ (-τ) ≤ δ ^ (-ζ) := by
    exact (mul_le_mul coarseLoss_le_coverError hexp (Real.rpow_pos_of_pos hd _).le coverError_pos.le).trans herrorsmall
  have hFloss : localSlabLoss * d ^ (-τ) ≤ δ ^ (-ζ) := by
    exact (mul_le_mul localLoss_le_coverError hexp (Real.rpow_pos_of_pos hd _).le coverError_pos.le).trans herrorsmall
  have hSloss : 2000000 * (d ^ (-τ) * δ ^ (-η) / (d ^ (4 * τ) / 56)) ≤ δ ^ (-ζ) := by
    exact (parent_error_bound hd hd1 hdδ hη.le hητ).trans
      ((mul_le_mul_of_nonneg_right parentLoss_le_coverError (Real.rpow_pos_of_pos hd _).le).trans herrorsmall)
  obtain ⟨S₀, Z₀, g₀, hZ₀, hmass₀, hpred₀, hmap₀⟩ := extend_selection hA.1 j hj S' g Y Zp hZp
  have hradii := physical_radius_range hr hδ hω hω1
    (by simpa only [radius_eq_ratio] using hρlo) (by simpa only [radius_eq_ratio] using hρhi)
  refine ⟨S₀, Z₀, coverScale * r * ρ, N', X, V, g₀, hZ₀, ?_, hradii.1, hradii.2, hV, ?_,
    convexCount_mono hKloss hKp, slabBound_mono hSloss hSbp, ?_⟩
  · rw [hmass₀]
    exact (mul_le_mul_left (ENNReal.ofReal_le_ofReal hmasssmall) _).trans hmassall
  · intro i hi
    obtain ⟨a, ha, hji, hgi⟩ := hmap₀ i hi
    rw [hgi, ← hji]
    exact hchild a ha
  · intro k
    apply slabBound_embedding j hj (U := fun i => tube s (x i) (v i))
      (P := fun i => i ∈ S' ∧ g i = k) (Q := fun i => i ∈ S₀ ∧ g₀ i = k)
    · intro i
      simpa only [and_assoc] using hpred₀ k i
    · exact slabBound_mono hFloss (hSfp k)

end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
