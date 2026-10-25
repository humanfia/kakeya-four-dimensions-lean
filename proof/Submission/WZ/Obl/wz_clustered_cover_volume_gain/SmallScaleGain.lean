-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.SmallScaleGain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.MediumEstimate
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CoverAssembly
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.NearRoundCover
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoarseRefinement

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set MeasureTheory
open scoped ENNReal

set_option maxHeartbeats 3000000

/-- The large Katz--Tao coefficient case at sufficiently small scales,
with the fine, medium and coarse multiplicity gains all assembled. -/
theorem clustered_gain_small {σ ω : ℝ} (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hE : E σ ω) (hJ : J σ ω)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ h α κ d : ℝ, 0 < h ∧ h ≤ ζ / 10 ∧ 0 < α ∧ 0 < κ ∧ 0 < d ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ d →
    ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
    A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
    ∀ (S : Finset (Fin n)) (Z : Fin n → Set V) (ρ : ℝ) (N : ℕ)
      (y w : Fin N → V) (f : Fin n → Fin N),
    G ω δ h n x v Y S Z ρ N y w f →
    (∀ U : Finset (Fin N), O (δ ^ (ζ / 2)) * ∑ i ∈ S, volume (Z i) ≤
        ∑ i ∈ S.filter (fun i => f i ∈ U), volume (Z i) →
      ¬ ∀ Q, Convex ℝ Q → O (q N {k | k ∈ U ∧ T ρ (y k) (w k) ⊆ Q} * ρ ^ 2) ≤
        O (δ ^ (-ζ)) * volume Q) →
    O (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ volume (⋃ i, Y i) := by
  classical
  let u := σ * ζ / 100
  have hu : 0 < u := by dsimp [u]; positivity
  obtain ⟨Cc, Hc, dc, hCc, hHc, hdc, Hcoarse⟩ :=
    Parent.Interfaces.coarse_refinement_from_packet_bound hσ.le hσhalf hω.le hω1 hE
      (τ := u) (χ := u) (D := 4) hu hu (by norm_num)
  let em := min u (Hc / 4)
  have hem : 0 < em := lt_min hu (by positivity)
  have hemu : em ≤ u := min_le_left _ _
  have hemHc : em ≤ Hc / 4 := min_le_right _ _
  obtain ⟨Cm, Hm, αm, κm, dm, hCm, hHm, hαm, hκm, hdm, Hmedium⟩ :=
    medium_estimate hσ.le hσhalf hω hω1 hE em hem
  obtain ⟨Cf, ηf, hCf, hηf, Hfine⟩ := fine_level_bound hσ.le hσhalf hω.le hE u hu
  let t := u / 100
  have ht : 0 < t := by dsimp [t]; positivity
  let νmax := min (Hm / 4) (min (u / 1000) (min (ηf / 10) (1 / 1000)))
  have hνmax : 0 < νmax := lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by norm_num)))
  obtain ⟨κr, ν, hr, dr, hκr, hν, hνmax', hνζ, hhr, hhrν, hdr, Hround⟩ :=
    Parent.Interfaces.near_round_factored_cover hσ.le (by linarith) hω hζ ht hνmax hJ
  have hνHm : ν ≤ Hm / 4 := hνmax'.trans (min_le_left _ _)
  have hνu : ν ≤ u / 1000 := hνmax'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνηf : ν ≤ ηf / 10 := hνmax'.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hνsmall : ν ≤ 1 / 1000 := hνmax'.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  let h := min hr (em / 10)
  have hh : 0 < h := lt_min hhr (by positivity)
  have hhr' : h ≤ hr := min_le_left _ _
  have hhem : h ≤ em / 10 := min_le_right _ _
  have hhν : h ≤ ν / 20 := hhr'.trans hhrν
  have hhζ : h ≤ ζ / 10 := by linarith
  let α := min (ω * t / 4) (min αm (σ * ζ / 4))
  have hα : 0 < α := lt_min (by positivity) (lt_min hαm (by positivity))
  have hαr : α ≤ ω * t / 4 := min_le_left _ _
  have hαm' : α ≤ αm := (min_le_right _ _).trans (min_le_left _ _)
  have hαgain : α ≤ σ * ζ / 4 := (min_le_right _ _).trans (min_le_right _ _)
  let Ctot := (2 * Cf) * Cm * Cc
  have hCtot : 0 < Ctot := by dsimp [Ctot]; positivity
  let κ := min κr (min κm Ctot⁻¹)
  have hκ : 0 < κ := lt_min hκr (lt_min hκm (inv_pos.mpr hCtot))
  obtain ⟨dp, hdp, Hconst⟩ := constant_power_bound (by norm_num : (0 : ℝ) < 384) hν
  let d := min (1 / 20000) (min dc (min dm (min dr dp)))
  refine ⟨h, α, κ, d, hh, hhζ, hα, hκ,
    lt_min (by norm_num) (lt_min hdc (lt_min hdm (lt_min hdr hdp))), ?_⟩
  intro δ hδ hδ100 hδd n x v Y hA S Z ρ N y w f hG hno
  have hδ1 : δ ≤ 1 := by linarith
  have hδsmall : δ ≤ 1 / 20000 := hδd.trans (min_le_left _ _)
  have hδc : δ ≤ dc := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδm : δ ≤ dm := hδd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδr : δ ≤ dr := hδd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hδp : δ ≤ dp := hδd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  have hδρ : δ ≤ ρ := by
    apply le_trans _ hG.2.1
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (show 1 - ω / 100 ≤ 1 by linarith)
  have hρ1 : ρ ≤ 1 := hG.2.2.1.trans (Real.rpow_le_one hδ.le hδ1 (by positivity))
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hC := hG.1
  have hCr := cover_error_mono hδ hδ1 hhr' hC
  rcases Hround δ hδ hδ100 hδr h hhr' n N x v Y Z S ρ y w f hδρ hρ1 hA hCr hno with hgain | hround
  · exact Parent.Interfaces.gain_mono hδ hδ1 hαr (min_le_left _ _) hκr.le hgain
  obtain ⟨U, m₀, a₀, b₀, Jn, z₀, e₀, g, hU, hm₀, hcover, hshape, hrich, hkeep, hcmp, hdense⟩ := hround
  let τ := hr + 2 * ν + ν / 10
  have hτ : 0 ≤ τ := by dsimp [τ]; positivity
  have hτHm : τ ≤ Hm := by dsimp [τ]; linarith
  have hhHm : h ≤ Hm := by linarith
  obtain ⟨Gd⟩ := grainData_of_G hG
  have hcov : ∀ k ∈ U, T ρ (y k) (w k) ⊆ P a₀ b₀ 8 (z₀ (g k)) (e₀ (g k)) := by
    intro k hk
    simpa only [Parent.Factor.tube, Parent.Factor.box, T, P, ι,
      show (2 : ℝ) * 4 = 8 by norm_num] using hcover.covers k hk
  rcases Hmedium δ h τ hδ hδm hh.le hhHm hτ hτHm n N Jn x v Y Z S ρ y w f hδρ hρ1 hA hC Gd
    U g z₀ e₀ a₀ b₀ hcover.width hcover.ordered hcov hkeep with hgain | hmedium
  · exact Parent.Interfaces.gain_mono hδ hδ1 hαm' ((min_le_right _ _).trans (min_le_left _ _)) hκm.le hgain
  obtain ⟨W, hMR⟩ := hmedium
  obtain ⟨k₀, hk₀⟩ := hU
  have hJn : 0 < Jn := by have := (g k₀).isLt; omega
  have hJnR : (0 : ℝ) < Jn := Nat.cast_pos.mpr hJn
  have hb₀ : 0 < b₀ := hρ.trans_le (hcover.width.trans hcover.ordered)
  obtain ⟨mf, hmf, hfine⟩ := Gd.fine_positive (fun i => (hC.1 i).2.2)
    (frozen_shading_mass_positive hδ hA hC)
  have hfdense : O (δ ^ ηf * q n {i | i ∈ S ∧ f i = k₀} * δ ^ 2) ≤
      ∑ i ∈ S.filter (fun i => f i = k₀), volume (Z i) := by
    apply le_trans _ (hdense k₀ hk₀)
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg δ)
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hmfBound := Hfine δ ρ b₀ h (t + ν) ζ Jn mf hδ hδ100 hδρ hρ1 hb₀ hJnR hh.le hmf.le
    n N x v Y Z S y w f k₀ hA hC hfdense (fun p hp => (hfine k₀ p hp).1) hrich
  let ef := u + h + σ * (t + ν + h)
  have hmfBound' : 2 * mf ≤ (2 * Cf) * δ ^ (σ * ζ - ef) * (δ / ρ) ^ (-ω) *
      ((n : ℝ) / Jn * δ * ρ / b₀ ^ 2) ^ σ := by
    have he : σ * ζ - u - h - σ * (t + ν + h) = σ * ζ - ef := by dsimp [ef]; ring
    rw [he] at hmfBound
    convert mul_le_mul_of_nonneg_left hmfBound (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
  let B := (2 * mf) * (Cm * δ ^ (-em) * (ρ / b₀) ^ (-ω - σ))
  have hB : 0 < B := by dsimp [B]; positivity
  have hpacket : ∀ p j, Parent.fiberMultiplicity (g ∘ f) W j p ≤ O B :=
    packet_count_of_medium (by positivity) hMR (fun k p hp => (hfine k p hp).2)
  have hW : ∀ i, MeasurableSet (W i) ∧ W i ⊆ Z i := fun i => ⟨(hMR.1 i).1, (hMR.1 i).2.1⟩
  have hsupport : ∀ i, (W i).Nonempty → i ∈ S ∧ f i ∈ U := by
    intro i hi
    constructor
    · by_contra hh
      exact hi.ne_empty ((hMR.1 i).2.2 (Or.inl hh))
    · by_contra hh
      exact hi.ne_empty ((hMR.1 i).2.2 (Or.inr hh))
  have hWden : O (δ ^ (em + h) * n * δ ^ 2) ≤ ∑ i, volume (W i) := by
    calc
      _ = O (δ ^ em) * O (δ ^ h * n * δ ^ 2) := by
        rw [Real.rpow_add hδ, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
        congr 1
        ring
      _ ≤ O (δ ^ em) * ∑ i, volume (Y i) := mul_le_mul' le_rfl hA.2.2.2.1
      _ ≤ _ := hMR.2.1
  have hnmax : (n : ℝ) ≤ δ ^ (-4 : ℝ) := by
    apply (power_count_bound hδ (admissible_count_eight hδ hA)).trans
    have hpow : δ ^ (-(h + 2)) ≤ δ ^ (-3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    calc
      _ ≤ 8 * δ ^ (-3 : ℝ) := mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ ≤ δ⁻¹ * δ ^ (-3 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hδ.le _)
        rw [← one_div]
        exact (le_div_iff₀ hδ).mpr (by linarith)
      _ = _ := by rw [← Real.rpow_neg_one, ← Real.rpow_add hδ]; norm_num
  have hcard : (n : ℝ) ≤ δ ^ (-(4 * ν)) * (S.filter fun i => f i ∈ U).card :=
    selected_fine_card_power f U hδ hδ1 (Hconst δ hδ hδp)
      (by linarith) hA (fun i => (hC.1 i).2.1) hkeep
  obtain ⟨W', hW', hretain, hmult⟩ := Hcoarse (η := h) (h := h) (ν := ν) (ξ := 4 * ν)
    (t := t) (r := em + h) hδ hδc hδρ hh.le hh.le hν.le (by positivity)
    (by linarith) (by linarith) (by linarith) (by linarith) (le_refl _) (by linarith)
    ⟨k₀, hk₀⟩ hA hC hcover hshape hnmax hcard hW hsupport hWden hB hpacket
  have hretainY : O (δ ^ (em + u)) * ∑ i, volume (Y i) ≤ ∑ i, volume (W' i) := by
    calc
      _ = O (δ ^ u) * (O (δ ^ em) * ∑ i, volume (Y i)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), ← Real.rpow_add hδ]
        congr 3
        ring
      _ ≤ O (δ ^ u) * ∑ i, volume (W i) := mul_le_mul' le_rfl hMR.2.1
      _ ≤ _ := hretain
  have hmult' : ∀ p, Parent.multiplicity W' p ≤
      O (Ctot * δ ^ (-ω + (σ * ζ - ef - em - u)) * (n * δ) ^ σ) := by
    intro p
    apply (hmult p).trans
    apply ENNReal.ofReal_le_ofReal
    have hBbound : B ≤ ((2 * Cf) * δ ^ (σ * ζ - ef) * (δ / ρ) ^ (-ω) *
        ((n : ℝ) / Jn * δ * ρ / b₀ ^ 2) ^ σ) * (Cm * δ ^ (-em) * (ρ / b₀) ^ (-ω - σ)) :=
      mul_le_mul_of_nonneg_right hmfBound' (by positivity)
    calc
      _ ≤ Cc * (((2 * Cf) * δ ^ (σ * ζ - ef) * (δ / ρ) ^ (-ω) *
        ((n : ℝ) / Jn * δ * ρ / b₀ ^ 2) ^ σ) * (Cm * δ ^ (-em) * (ρ / b₀) ^ (-ω - σ))) *
        δ ^ (-u) * (b₀ ^ (-ω) * (Jn * b₀) ^ σ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBbound hCc.le)
              (Real.rpow_nonneg hδ.le _)) (by positivity)
      _ = _ := coarse_packet_product hδ hρ hb₀ (Nat.cast_pos.mpr hA.1) hJnR
  have hshapeLoss : σ * (t + ν + h) ≤ u := by
    have hm := mul_le_mul_of_nonneg_right hσhalf (show 0 ≤ t + ν + h by positivity)
    dsimp [t] at hm
    dsimp only [t]
    nlinarith only [hm, hνu, hhν, hu]
  have hbudget : h + (em + u) + α ≤ σ * ζ - ef - em - u := by
    dsimp [ef]
    have huval : 100 * u = σ * ζ := by dsimp [u]; ring
    linarith only [hαgain, hshapeLoss, hemu, hhν, hνu, huval, hu]
  have hgain := Parent.first_alternative_of_refined_multiplicity hδ hδ1 hCtot hbudget hA.1
    (fun i => (hW' i).1) (fun i => (hW' i).2.trans ((hW i).2.trans (hC.1 i).2.1))
    hA.2.2.2.1 hretainY hmult'
  exact Parent.Interfaces.gain_mono hδ hδ1 le_rfl
    ((min_le_right _ _).trans (min_le_right _ _)) (inv_pos.mpr hCtot).le hgain

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
