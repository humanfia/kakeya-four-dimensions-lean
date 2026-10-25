-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.ProjectionNumerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.ProjectionParameters
import Submission.WZ.Obl.wz_separated_projection_dichotomy.RadialFrostman

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

noncomputable def projectionFrostman (δ θ ζ : ℝ) : ℝ := 27648 * δ ^ (-(4 * θ + ζ))
noncomputable def projectionLine (δ θ ζ β : ℝ) : ℝ := 13824 * δ ^ (-(2 * θ + β * ζ))

theorem localization_frostman_identity {δ : ℝ} (hδ : 0 < δ) (θ ζ : ℝ) :
    δ ^ (-θ) / ((δ ^ θ) ^ (3 : ℕ) * δ ^ ζ / 27648) = projectionFrostman δ θ ζ := by
  rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_add hδ]
  norm_num only [Nat.cast_ofNat]
  have hid : δ ^ (-θ) / (δ ^ (θ * 3 + ζ) / 27648) =
      27648 * (δ ^ (-θ) / δ ^ (θ * 3 + ζ)) := by ring
  rw [hid, ← Real.rpow_sub hδ]
  unfold projectionFrostman
  congr 2
  ring

theorem ProjectionScaleBudget.rescaled {δ ε ℓ α β η ζ θ t dNC τ : ℝ}
    (hb : ProjectionScaleBudget δ ε ℓ α β η ζ θ t dNC)
    (hp : ProjectionParameterBounds ε ℓ α β η ζ θ t) (hδ : 0 < δ)
    (hτ : 0 < τ) (hτbound : τ ≤ δ ^ t) :
    2 * projectionFrostman δ θ ζ ≤ τ ^ (-ℓ) ∧
      projectionLine δ θ ζ β / (δ ^ β) ^ ζ ≤ (τ ^ (-ℓ)) ^ ζ ∧
      τ ^ α ≤ δ ^ θ / 1728 ∧
      10 * projectionFrostman δ θ ζ * δ ^ β ≤ δ ^ ζ ∧
      δ ≤ δ ^ β ∧ δ ^ β ≤ 1 / 2 ∧
      δ ^ (-θ) * τ ≤ 50 ∧ (50 / τ) ^ (1 - ε) ≤ τ ^ (ε / 2 - 1) := by
  have hC : 2 * projectionFrostman δ θ ζ ≤ τ ^ (-ℓ) := by
    calc 2 * projectionFrostman δ θ ζ = 55296 * δ ^ (-(4 * θ + ζ)) := by unfold projectionFrostman; ring
      _ ≤ δ ^ (-(t * ℓ)) := hb.frostman
      _ = (δ ^ t) ^ (-ℓ) := by rw [← Real.rpow_mul hδ.le]; congr 1; ring
      _ ≤ τ ^ (-ℓ) := Real.rpow_le_rpow_of_nonpos hτ hτbound (by linarith [hp.ell_pos])
  have hK : projectionLine δ θ ζ β / (δ ^ β) ^ ζ ≤ (τ ^ (-ℓ)) ^ ζ := by
    calc projectionLine δ θ ζ β / (δ ^ β) ^ ζ = 13824 * δ ^ (-(2 * θ + 2 * β * ζ)) := by
          unfold projectionLine
          rw [← Real.rpow_mul hδ.le, mul_div_assoc, ← Real.rpow_sub hδ]
          congr 2
          ring
      _ ≤ δ ^ (-(t * ℓ * ζ)) := hb.line_count
      _ = ((δ ^ t) ^ (-ℓ)) ^ ζ := by rw [← Real.rpow_mul hδ.le, ← Real.rpow_mul hδ.le]; congr 1; ring
      _ ≤ (τ ^ (-ℓ)) ^ ζ := Real.rpow_le_rpow (by positivity)
        (Real.rpow_le_rpow_of_nonpos hτ hτbound (by linarith [hp.ell_pos])) hp.zeta_pos.le
  have hd : τ ^ α ≤ δ ^ θ / 1728 := by
    have ht : τ ^ α ≤ δ ^ (t * α) := by
      simpa only [Real.rpow_mul hδ.le] using Real.rpow_le_rpow hτ.le hτbound hp.alpha_pos.le
    linarith [hb.density]
  have hs : 10 * projectionFrostman δ θ ζ * δ ^ β ≤ δ ^ ζ := by
    have heq : 10 * projectionFrostman δ θ ζ * δ ^ β = 276480 * δ ^ (β - 4 * θ - ζ) := by
      unfold projectionFrostman
      rw [show 10 * (27648 * δ ^ (-(4 * θ + ζ))) * δ ^ β =
        276480 * (δ ^ (-(4 * θ + ζ)) * δ ^ β) by ring, ← Real.rpow_add hδ]
      congr 2
      ring
    rw [heq]
    exact hb.small_normal
  have hδβ : δ ≤ δ ^ β := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hδ hb.scale_le_one hp.beta_le_one
  have hlen : δ ^ (-θ) * τ ≤ 50 := by
    have hτθ : τ ≤ δ ^ θ := hτbound.trans
      (Real.rpow_le_rpow_of_exponent_ge hδ hb.scale_le_one hp.theta_le_t)
    calc δ ^ (-θ) * τ ≤ δ ^ (-θ) * δ ^ θ := mul_le_mul_of_nonneg_left hτθ (by positivity)
      _ = 1 := by rw [← Real.rpow_add hδ]; simp
      _ ≤ 50 := by norm_num
  have hpower : (50 / τ) ^ (1 - ε) ≤ τ ^ (ε / 2 - 1) := by
    have heps : 0 ≤ 1 - ε := by linarith [hp.epsilon_le_one]
    have h50 : (50 : ℝ) ^ (1 - ε) ≤ 50 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 50)
        (show 1 - ε ≤ 1 by linarith [hp.epsilon_pos])
    have hτpow : τ ^ (ε / 2) ≤ δ ^ (t * ε / 2) := by
      calc τ ^ (ε / 2) ≤ (δ ^ t) ^ (ε / 2) := Real.rpow_le_rpow hτ.le hτbound (by linarith [hp.epsilon_pos])
        _ = _ := by rw [← Real.rpow_mul hδ.le]; congr 1; ring
    have hprod : (50 : ℝ) ^ (1 - ε) * τ ^ (ε / 2) ≤ 1 :=
      (mul_le_mul h50 hτpow (by positivity) (by norm_num)).trans hb.projection_power
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hτ (1 - ε / 2))).mp
    rw [← Real.rpow_add hτ, show ε / 2 - 1 + (1 - ε / 2) = 0 by ring, Real.rpow_zero]
    calc (50 / τ) ^ (1 - ε) * τ ^ (1 - ε / 2) =
          (50 : ℝ) ^ (1 - ε) * τ ^ (ε / 2) := by
            rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 50) hτ.le]
            have heq : (50 : ℝ) ^ (1 - ε) / τ ^ (1 - ε) * τ ^ (1 - ε / 2) =
                (50 : ℝ) ^ (1 - ε) * (τ ^ (1 - ε / 2) / τ ^ (1 - ε)) := by ring
            rw [heq, ← Real.rpow_sub hτ]
            congr 2
            ring
      _ ≤ 1 := hprod
  exact ⟨hC, hK, hd, hs, hδβ, by linarith [hb.angular_small], hlen, hpower⟩

theorem ClosedFiniteFrostman.nonempty_count {δ C : ℝ} {S : Finset Plane}
    (h : ClosedFiniteFrostman δ C S) (hδ : 0 ≤ δ) (hne : S.Nonempty) :
    1 ≤ C * δ * (S.card : ℝ) := by
  classical
  obtain ⟨x, hx⟩ := hne
  have hmem : x ∈ S.filter (fun y => dist y x ≤ δ) := Finset.mem_filter.mpr ⟨hx, by simpa using hδ⟩
  have hc : (1 : ℝ) ≤ ((S.filter (fun y => dist y x ≤ δ)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨x, hmem⟩
  exact hc.trans (h.filter_closedBall x δ le_rfl)

theorem ProjectionScaleBudget.narrow_cardinal {δ ε ℓ α β η ζ θ t dNC W n : ℝ}
    (hb : ProjectionScaleBudget δ ε ℓ α β η ζ θ t dNC) (hδ : 0 < δ)
    (hW : 0 < W) (hWsmall : W ≤ δ ^ (1 - t))
    (hn : 1 ≤ projectionFrostman δ θ ζ * δ * n) :
    δ ^ (ε - 1) ≤ δ / (150 * W) * n := by
  have hC : 0 < projectionFrostman δ θ ζ := by unfold projectionFrostman; positivity
  have hid : δ ^ (4 * θ + ζ + t - 1) * δ ^ (-(4 * θ + ζ)) * δ ^ (1 - t) = 1 := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
    convert Real.rpow_zero δ using 1 <;> congr 1 <;> ring
  have hraw := mul_le_mul_of_nonneg_right hb.narrow_card (by positivity : 0 ≤ δ ^ (-(4 * θ + ζ)) * δ ^ (1 - t))
  have hN : δ ^ (ε - 1) * (150 * W) * projectionFrostman δ θ ζ ≤ 1 := by
    calc δ ^ (ε - 1) * (150 * W) * projectionFrostman δ θ ζ ≤
          δ ^ (ε - 1) * (150 * δ ^ (1 - t)) * projectionFrostman δ θ ζ := by gcongr
      _ = (4147200 * δ ^ (ε - 1)) * (δ ^ (-(4 * θ + ζ)) * δ ^ (1 - t)) := by
        unfold projectionFrostman
        ring
      _ ≤ _ := hraw
      _ = 1 := by simpa only [← mul_assoc] using hid
  apply (mul_le_mul_iff_left₀ (mul_pos (by positivity : 0 < 150 * W) hC)).mp
  have heq : (δ / (150 * W) * n) * (150 * W * projectionFrostman δ θ ζ) =
      projectionFrostman δ θ ζ * δ * n := by field_simp <;> ring
  rw [heq]
  simpa only [mul_assoc] using hN.trans hn

end WangZahlLot.Obl.wz_separated_projection_dichotomy
