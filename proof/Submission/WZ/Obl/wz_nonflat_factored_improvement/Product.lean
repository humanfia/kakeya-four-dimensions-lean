-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.Product.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.FiniteProduct
import Submission.WZ.Obl.wz_nonflat_factored_improvement.DirectEstimate
import Submission.WZ.Obl.wz_nonflat_factored_improvement.SaturationPacking
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Admissibility
import Submission.WZ.Obl.wz_nonflat_factored_improvement.ProductLoss
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Gain

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set

set_option maxHeartbeats 600000 in
/-- Uniform two-scale product estimate, with every parameter chosen before the family. -/
theorem has_two_scale_product {σ ω u : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2)
    (hgap : ω < u) (hD : EstimateD σ ω) (hE : EstimateE σ u) : HasTwoScaleProduct σ ω u := by
  intro ζ hζ e he
  have he4 : 0 < e / 4 := by positivity
  obtain ⟨AP, ηD, ηE, hAP, hηD, hηE, HP⟩ :=
    finite_two_scale_product hσ0 (by linarith : σ ≤ 1) hD hE he4
  obtain ⟨AS, ηS, hAS, hηS, HS⟩ := direct_retained_estimate hσ0 (by linarith : σ ≤ 2 / 3) hD he4
  obtain ⟨β, τ, t, η, d, K, hβ, hβζ, hτ, ht, hη, hd, hK, Hpar⟩ :=
    choose_product_parameters hζ he hηD hηE hηS
  have hK0 : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
  have hcf := coarseFraction_pos
  let A := min AS (AP * coarseFraction / K)
  have hA : 0 < A := lt_min hAS (by positivity)
  refine ⟨β, hβ, hβζ, A, hA, η, hη, d, hd, ?_⟩
  intro ν hν hνη δ hδ hδ100 hδd m hm n x v Y
    hn hv hball hover hYm hYT _hden _hconv hslab hind a b hδa hab _hb2 hfact hnonflat hvol
  have hδ1 : δ ≤ 1 := by linarith
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have hbδ := coarse_width_bound hδ hδ1 hb.le hβζ hvol hnonflat
  have hb1 : b ≤ 1 := hbδ.trans (Real.rpow_le_one hδ.le hδ1 (by positivity))
  obtain ⟨hνS, hloss, hcut, hcden, hccoeff, hscoeff, hfden, hcompact⟩ :=
    Hpar ν δ a b hν hνη hδ hδ1 hδd hδa hab hbδ hnonflat.le
  obtain ⟨k, g, hg, hk, hsize, c, hc1, hcm, hconv, q, hq, W, hW, hcover,
    hdegree, hbalance, hsaturation, hprism, hrelative⟩ := hfact
  choose R hR using hW
  have hWr : W = fun j => R j '' standardPrism a b := funext hR
  rw [hWr] at hcover hdegree hbalance hsaturation hprism hrelative
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hslabg := slabCount_subfamily_power hδ g hg hsize hslab
  have hvg : ∀ i, ‖v (g i)‖ = 1 := fun i => hv (g i)
  have hoverg : ∀ i j, i ≠ j → volume (tube δ (x (g i)) (v (g i)) ∩
      tube δ (x (g j)) (v (g j))) ≤ (1 / 2 : ENNReal) * volume (tube δ (x (g i)) (v (g i))) :=
    fun i j hij => hover (g i) (g j) (hg.ne hij)
  by_cases hscale : δ / b ≤ δ ^ t
  · have hD1 : 1 ≤ δ ^ (-ν) := by
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith : -ν ≤ 0)
    have hpos : ∀ j, 0 < Set.ncard {i | tube δ (x (g i)) (v (g i)) ⊆ R j '' standardPrism a b} := by
      intro j
      by_contra hnpos
      have hz := Nat.eq_zero_of_not_pos hnpos
      have hh := hsaturation j
      rw [hz, Nat.cast_zero, zero_mul] at hh
      have hp : 0 < δ ^ ν * c * a * b := by positivity
      linarith
    have hrel : ∀ j U, Convex ℝ U →
        ENNReal.ofReal ((Set.ncard {i | tube δ (x (g i)) (v (g i)) ⊆ R j '' standardPrism a b ∧
          tube δ (x (g i)) (v (g i)) ⊆ U} : ℝ) * (a * b)) ≤
        ENNReal.ofReal (δ ^ (-ν) * Set.ncard {i | tube δ (x (g i)) (v (g i)) ⊆ R j '' standardPrism a b}) * volume U := by
      intro j U hU
      simpa only [mul_assoc] using hrelative j U hU
    have hprod := HP a b δ (δ ^ ν) (δ ^ τ) c (δ ^ (-ν)) (δ ^ (-2 * ν))
      hδ hδa hab hb1 (Real.rpow_pos_of_pos hδ _) (Real.rpow_pos_of_pos hδ _) hc1 hD1 (by positivity)
      K hK hcut (hfden hscale) hcden hccoeff hscoeff k q
      (fun i => x (g i)) (fun i => v (g i)) (fun i => Y (g i)) R hk hq hvg
      (fun i => hball (g i)) hoverg (fun i => hYm (g i)) (fun i => hYT (g i)) (fun i => hind (g i))
      hconv hslabg hcover hdegree hpos hbalance hprism hrel
    have hf := Real.rpow_pos_of_pos hδ ν
    have hf1 : δ ^ ν ≤ 1 := Real.rpow_le_one hδ.le hδ1 hν.le
    have hw := realWeight_fraction hδ hc0 (Nat.cast_pos.mpr hn) hf hf1 hsize hσ0 (by linarith : σ ≤ 1)
    change δ ^ ν * weight σ δ c n ≤ weight σ δ c k at hw
    have hwm := weight_mono_coefficient hδ hc0 hcm (by linarith : σ ≤ 2 / 3) n
    have hW : 0 ≤ weight σ δ m n := weight_nonneg hδ.le (zero_le_one.trans hm) σ n
    have hWV : δ ^ ν * weight σ δ m n ≤ weight σ δ c k :=
      (mul_le_mul_of_nonneg_left hwm hf.le).trans hw
    have hcomp := product_loss_bound (ω := ω) (u := u) hδ hδ1 ha hb hb1 (by linarith : 0 ≤ ν + β)
      hσ0 (by linarith : σ ≤ 1) he.le hAP hK0 hW hnonflat.le hWV hloss
    apply le_trans _ (hprod.trans (subfamily_union_volume Y g))
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (AP * coarseFraction / K) * δ ^ (u + e) * b ^ (ω - u + e) * weight σ δ m n := by
        gcongr
        exact min_le_right _ _
      _ ≤ _ := hcomp
  · have hcsmall : c ≤ δ ^ (-ηS) := by
      have hh := saturation_coefficient_bound ha hab hδ (Real.rpow_pos_of_pos hδ ν)
        (R ⟨0, hq⟩) (fun i => x (g i)) (fun i => v (g i)) hvg hoverg (hsaturation ⟨0, hq⟩)
      exact hh.trans (hcompact (not_le.mp hscale).le)
    have hbound := HS ν δ m c hν hνS hδ hδ100 hm hcsmall n k x v Y g hn hg hsize
      hv hball hover hYm hYT hind hconv hslabg
    apply le_trans (ENNReal.ofReal_le_ofReal _) hbound
    have hpow := product_scalar_le_direct hδ hδ1 (hδa.trans hab) hb1 hgap.le he.le
      (show e / 4 + ν ≤ e by linarith)
    calc
      _ = A * (δ ^ (u + e) * b ^ (ω - u + e)) * weight σ δ m n := by ring
      _ ≤ AS * δ ^ (ω + (e / 4 + ν)) * weight σ δ m n := by
        apply mul_le_mul_of_nonneg_right _ (weight_nonneg hδ.le (zero_le_one.trans hm) σ n)
        exact mul_le_mul (min_le_left _ _) hpow (by positivity) hAS.le
      _ = _ := by rw [show ω + (e / 4 + ν) = ω + e / 4 + ν by ring]

end WangZahlLot.Obl.wz_nonflat_factored_improvement
