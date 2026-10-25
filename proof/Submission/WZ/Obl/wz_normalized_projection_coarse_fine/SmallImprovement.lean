-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.SmallImprovement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.SmallIteration

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open MeasureTheory
open WangZahlLot.Obl.wz_normalized_projection_iteration

/-- Only a single small comparison exponent is needed for one affine gain in the
projection estimate. The geometric lifting theorem is an accepted dependency. -/
theorem projection_gain_at {θ s : ℝ} (hθ : 0 < θ) (hθsmall : θ < 1 / 4)
    (hs : 4 * θ ≤ s) (hs2 : s ≤ 2) (hcomp : ComparisonAt θ) (hEst : Estimate s) :
    Estimate ((1 - θ ^ 2 / 2) * s + 2 * θ ^ 3) := by
  obtain ⟨β, hβ, dB, hdB, hB⟩ := hEst
  obtain ⟨C, hC, lift⟩ := coarse_lifting
  have hCpos : 0 < C := one_pos.trans_le hC
  have hθone : θ < 1 := by linarith
  obtain ⟨κ, hκ, dL, hdL, lift⟩ := lift θ β hθ hθone hβ
  obtain ⟨η, hη, dF, hdF, compare⟩ := hcomp κ hκ
  obtain ⟨dS, hdS, small⟩ :=
    WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff hθ
      (lt_min hdB (by norm_num : (0 : ℝ) < 1 / 100))
  obtain ⟨dA, hdA, absorb⟩ :=
    WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
      (pow_pos hθ 3) (inv_pos.mpr hCpos)
  refine ⟨min η κ, lt_min hη hκ, min (min dF dL) (min dS dA),
    lt_min (lt_min hdF hdL) (lt_min hdS hdA), ?_⟩
  intro δ hδ hd hδsmall n x v Y hH htr hF f hf hf0
  have hdF' := (hd.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hdL' := (hd.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hdS' := (hd.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hdA' := (hd.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hδone : δ ≤ 1 := by linarith
  obtain ⟨ρ, hδρpow, hρone, Z, hZm, hZY, hZmass, hZarea⟩ :=
    compare δ hδ hdF' hδsmall n x v Y
      (family_mono hδ hδone (min_le_left η κ) hH) htr
      (frostman_mono hδ hδone (min_le_left η κ) hF) f hf hf0
  have hρ : 0 < ρ := (Real.rpow_pos_of_pos hδ _).trans hδρpow
  have hZnonempty := projection_nonempty f (shading_nonempty hδ hH.1 hZmass)
  have harea := hZarea.trans (measure_mono (projection_mono f (Set.iUnion_mono hZY)))
  let t := (1 - θ ^ 2 / 2) * s + 2 * θ ^ 3
  have hspos : 0 ≤ s := by linarith
  have hlarge : 3 * θ ≤ t := by
    have hq : 0 ≤ 1 - θ ^ 2 / 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hs hq
    dsimp [t]
    nlinarith
  by_cases hend : δ ^ θ ≤ ρ
  · apply (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hδ hδone hlarge)).trans
    have hh := terminal_area_bound hδ hρ hρone.le hθ.le hend hZnonempty
    have he : θ + 2 * θ = 3 * θ := by ring
    rw [he] at hh
    exact hh.trans harea
  have hρsmall : ρ ≤ δ ^ θ := (not_le.mp hend).le
  have hδρ : δ ≤ ρ := by
    have he : 1 - θ ^ 2 ≤ 1 := by nlinarith
    have hh := Real.rpow_le_rpow_of_exponent_ge hδ hδone he
    rw [Real.rpow_one] at hh
    exact hh.trans hδρpow.le
  have hsmall := small δ hδ hdS'
  have hZfamily : Family κ δ n x v Z :=
    ⟨hH.1, hH.2.1, hH.2.2.1, hH.2.2.2.1, hZm,
      fun i => (hZY i).trans (hH.2.2.2.2.2.1 i), hZmass⟩
  obtain ⟨m, z, w, W, hW, hwt, hWF, hWa⟩ :=
    lift δ ρ hδ hdL' hδsmall hδρ hρsmall
      (hρsmall.trans (hsmall.trans (min_le_right _ _))) n x v Z hZfamily htr
      (frostman_mono hδ hδone (min_le_right η κ) hF) f hf hf0
  have hb := hB ρ hρ (hρsmall.trans (hsmall.trans (min_le_left _ _)))
    (hρsmall.trans (hsmall.trans (min_le_right _ _))) m z w W hW hwt hWF f hf hf0
  let u := (1 - θ ^ 2) * s + θ ^ 3
  have hscale : δ ^ u ≤ (δ / ρ) ^ θ * ρ ^ s := by
    have hst : 0 ≤ s - θ := by linarith
    calc
      δ ^ u = δ ^ θ * (δ ^ (1 - θ ^ 2)) ^ (s - θ) := by
        rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
        congr 1
        dsimp [u]
        ring
      _ ≤ δ ^ θ * ρ ^ (s - θ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Real.rpow_nonneg hδ.le _) hδρpow.le hst)
        (Real.rpow_nonneg hδ.le _)
      _ = _ := by
        rw [Real.div_rpow hδ.le hρ.le, Real.rpow_sub hρ]
        ring
  have hgap : u + θ ^ 3 ≤ t := by
    have hm := mul_nonneg (sq_nonneg θ) hspos
    dsimp [u, t]
    nlinarith
  have habsorb : C * δ ^ t ≤ δ ^ u := by
    calc
      C * δ ^ t ≤ C * δ ^ (u + θ ^ 3) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hδ hδone hgap) hCpos.le
      _ = (C * δ ^ (θ ^ 3)) * δ ^ u := by rw [Real.rpow_add hδ]; ring
      _ ≤ 1 * δ ^ u := mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left (absorb δ hδ hdA') hCpos.le).trans_eq
          (mul_inv_cancel₀ hCpos.ne')) (Real.rpow_nonneg hδ.le _)
      _ = _ := one_mul _
  have hbound : ENNReal.ofReal C * ENNReal.ofReal (δ ^ t) ≤
      ENNReal.ofReal C * volume (Projection f (⋃ i, Y i)) := by
    calc
      _ = ENNReal.ofReal (C * δ ^ t) := (ENNReal.ofReal_mul hCpos.le).symm
      _ ≤ ENNReal.ofReal ((δ / ρ) ^ θ * ρ ^ s) :=
        ENNReal.ofReal_le_ofReal (habsorb.trans hscale)
      _ = ENNReal.ofReal ((δ / ρ) ^ θ) * ENNReal.ofReal (ρ ^ s) :=
        ENNReal.ofReal_mul (by positivity)
      _ ≤ ENNReal.ofReal ((δ / ρ) ^ θ) *
          (ENNReal.ofReal C * volume (Metric.thickening ρ (Projection f (⋃ i, Z i)))) :=
        mul_le_mul' le_rfl (hb.trans hWa)
      _ = ENNReal.ofReal C * (ENNReal.ofReal ((δ / ρ) ^ θ) *
          volume (Metric.thickening ρ (Projection f (⋃ i, Z i)))) := by ring
      _ ≤ _ := mul_le_mul' le_rfl harea
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hCpos).ne'
    ENNReal.ofReal_ne_top).mp hbound

/-- Comparisons for arbitrarily small positive exponents already give every normalized
projection-volume exponent, by the accepted coarse lifting and affine bootstrap. -/
theorem projection_estimate_of_small_comparisons
    (hsmall : ∀ θ : ℝ, 0 < θ → θ < 1 / 100 → ComparisonAt θ) :
    ∀ ε : ℝ, 0 < ε → Estimate ε := by
  intro ε hε
  let θ : ℝ := min (ε / 8) (1 / 200)
  have hθ : 0 < θ := lt_min (by positivity) (by norm_num)
  have hθsmall : θ < 1 / 100 := (min_le_right _ _).trans_lt (by norm_num)
  have hθquarter : θ < 1 / 4 := hθsmall.trans (by norm_num)
  have hb : 4 * θ < 2 := by linarith
  have hbε : 4 * θ < ε := by
    have hh : θ ≤ ε / 8 := min_le_left _ _
    linarith
  have hq0 : 0 < 1 - θ ^ 2 / 2 := by nlinarith
  have hq1 : 1 - θ ^ 2 / 2 < 1 := by nlinarith
  apply estimate_of_affine_gain hb hbε hq0 hq1 elementary_projection_estimate
  intro s hs hs2 hEst
  have hh := projection_gain_at hθ hθquarter hs.le hs2 (hsmall θ hθ hθsmall) hEst
  convert hh using 1
  ring

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
