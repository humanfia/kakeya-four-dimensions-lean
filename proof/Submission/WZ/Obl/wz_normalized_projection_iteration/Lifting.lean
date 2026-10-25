-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_iteration.Lifting.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_iteration.Bootstrap
import Submission.WZ.Obl.wz_separated_cover_refinement

namespace WangZahlLot.Obl.wz_normalized_projection_iteration

open MeasureTheory

/-- Geometric coarse lifting, with a uniform loss in projected outer area. -/
def CoarseLifting : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ a β : ℝ, 0 < a → a < 1 → 0 < β →
    ∃ κ : ℝ, 0 < κ ∧ ∃ d0 : ℝ, 0 < d0 ∧
    ∀ δ ρ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1 / 100 : ℝ) →
      δ ≤ ρ → ρ ≤ δ ^ a → ρ ≤ (1 / 100 : ℝ) →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Family κ δ n x v Y → (∀ i, (1 / 2 : ℝ) ≤ |v i 2|) →
      Frostman κ δ n x v → ∀ f : ℝ → ℝ, Slope f → |f 0| ≤ 1 →
    ∃ (m : ℕ) (z w : Fin m → Space) (Z : Fin m → Set Space),
      Family β ρ m z w Z ∧ (∀ i, (1 / 2 : ℝ) ≤ |w i 2|) ∧ Frostman β ρ m z w ∧
      volume (Projection f (⋃ i, Z i)) ≤
        ENNReal.ofReal C * volume (Metric.thickening ρ (Projection f (⋃ i, Y i)))

/-- One coarse/fine comparison and one lifting step improve any exponent above `4θ`. -/
theorem estimate_improvement (hL : CoarseLifting) (hCF : CoarseFine)
    {θ s : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1 / 4) (hs : 4 * θ ≤ s) (hs2 : s ≤ 2)
    (hEst : Estimate s) : Estimate ((1 - θ ^ 2) * s + 4 * θ ^ 3) := by
  obtain ⟨C, hC, hL⟩ := hL
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  have hθone : θ < 1 := by linarith
  obtain ⟨β, hβ, dB, hdB, hB⟩ := hEst
  obtain ⟨κ, hκ, dL, hdL, hL⟩ := hL θ β hθ hθone hβ
  obtain ⟨η, hη, dF, hdF, hCF⟩ := hCF θ κ hθ hθone hκ
  have hgap : 0 < 3 * θ ^ 3 := by positivity
  obtain ⟨dS, hdS, hS⟩ :=
    WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff hθ
      (lt_min hdB (by norm_num : (0 : ℝ) < 1 / 100))
  obtain ⟨dC, hdC, hAbs⟩ :=
    WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff hgap (inv_pos.mpr hC0)
  refine ⟨min η κ, lt_min hη hκ, min dF (min dL (min dS dC)),
    lt_min hdF (lt_min hdL (lt_min hdS hdC)), ?_⟩
  intro δ hδ hd hδsmall n x v Y hY hv hF f hf hf0
  have hδ1 : δ ≤ 1 := by linarith
  have hdF' : δ ≤ dF := hd.trans (min_le_left _ _)
  have hdL' : δ ≤ dL := hd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdS' : δ ≤ dS := hd.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hdC' : δ ≤ dC := hd.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hsmall := hS δ hδ hdS'
  have hconstant := hAbs δ hδ hdC'
  have hYη := family_mono hδ hδ1 (min_le_left η κ) hY
  have hFη := frostman_mono hδ hδ1 (min_le_left η κ) hF
  obtain ⟨ρ, hρδ, hρ1, Z, hZm, hZY, hmass, harea⟩ :=
    hCF δ hδ hdF' hδsmall n x v Y hYη hv hFη f hf hf0
  have hρ : 0 < ρ := (Real.rpow_pos_of_pos hδ _).trans hρδ
  have hZnonempty := projection_nonempty f (shading_nonempty hδ hY.1 hmass)
  have hmono : volume (Projection f (⋃ i, Z i)) ≤ volume (Projection f (⋃ i, Y i)) :=
    measure_mono (projection_mono f (Set.iUnion_mono hZY))
  by_cases hterminal : δ ^ θ ≤ ρ
  · have hterminalBound := terminal_area_bound hδ hρ hρ1.le hθ.le hterminal hZnonempty
    have hexp : 3 * θ ≤ (1 - θ ^ 2) * s + 4 * θ ^ 3 := by
      have hq : 0 ≤ 1 - θ ^ 2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_left hs hq
      nlinarith [pow_pos hθ 3]
    have hpow := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hexp
    have hleft : ENNReal.ofReal (δ ^ ((1 - θ ^ 2) * s + 4 * θ ^ 3)) ≤
        ENNReal.ofReal (δ ^ (θ + 2 * θ)) := by
      simpa only [show θ + 2 * θ = 3 * θ by ring] using ENNReal.ofReal_le_ofReal hpow
    exact hleft.trans (hterminalBound.trans (harea.trans hmono))
  · have hρsmall : ρ ≤ δ ^ θ := (lt_of_not_ge hterminal).le
    have hδρ : δ ≤ ρ := by
      have hp := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (show 1 - θ ^ 2 ≤ 1 by nlinarith)
      simpa only [Real.rpow_one] using hp.trans hρδ.le
    have hZfamily : Family κ δ n x v Z := by
      refine ⟨hY.1, hY.2.1, hY.2.2.1, hY.2.2.2.1, hZm,
        fun i => (hZY i).trans (hY.2.2.2.2.2.1 i), hmass⟩
    have hFκ := frostman_mono hδ hδ1 (min_le_right η κ) hF
    obtain ⟨m, z, w, W, hW, hw, hWF, hWarea⟩ :=
      hL δ ρ hδ hdL' hδsmall hδρ hρsmall
        (hρsmall.trans (hsmall.trans (min_le_right _ _))) n x v Z hZfamily hv hFκ f hf hf0
    have hcoarse := hB ρ hρ (hρsmall.trans (hsmall.trans (min_le_left _ _)))
      (hρsmall.trans (hsmall.trans (min_le_right _ _))) m z w W hW hw hWF f hf hf0
    have hsθ : 0 ≤ s - θ := by linarith
    have hscale : δ ^ ((1 - θ ^ 2) * s + θ ^ 3) ≤ (δ / ρ) ^ θ * ρ ^ s := by
      calc
        _ = δ ^ θ * (δ ^ (1 - θ ^ 2)) ^ (s - θ) := by
          rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
          congr 1
          ring
        _ ≤ δ ^ θ * ρ ^ (s - θ) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Real.rpow_nonneg hδ.le _) hρδ.le hsθ)
            (Real.rpow_nonneg hδ.le _)
        _ = (δ / ρ) ^ θ * ρ ^ s := by
          rw [Real.div_rpow hδ.le hρ.le, Real.rpow_sub hρ]
          ring
    have habsorb : C * δ ^ ((1 - θ ^ 2) * s + 4 * θ ^ 3) ≤
        δ ^ ((1 - θ ^ 2) * s + θ ^ 3) := by
      have hid : (1 - θ ^ 2) * s + 4 * θ ^ 3 =
          3 * θ ^ 3 + ((1 - θ ^ 2) * s + θ ^ 3) := by ring
      rw [hid, Real.rpow_add hδ, ← mul_assoc]
      apply mul_le_of_le_one_left (Real.rpow_nonneg hδ.le _)
      exact (mul_le_mul_of_nonneg_left hconstant hC0.le).trans_eq (mul_inv_cancel₀ hC0.ne')
    have hprod : ENNReal.ofReal (C * δ ^ ((1 - θ ^ 2) * s + 4 * θ ^ 3)) ≤
        ENNReal.ofReal C * volume (Projection f (⋃ i, Y i)) := by
      calc
        _ ≤ ENNReal.ofReal ((δ / ρ) ^ θ * ρ ^ s) :=
          ENNReal.ofReal_le_ofReal (habsorb.trans hscale)
        _ = ENNReal.ofReal ((δ / ρ) ^ θ) * ENNReal.ofReal (ρ ^ s) := by
          rw [ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal ((δ / ρ) ^ θ) *
            (ENNReal.ofReal C * volume (Metric.thickening ρ (Projection f (⋃ i, Z i)))) :=
          mul_le_mul_right (hcoarse.trans hWarea) _
        _ = ENNReal.ofReal C * (ENNReal.ofReal ((δ / ρ) ^ θ) *
            volume (Metric.thickening ρ (Projection f (⋃ i, Z i)))) := by ring
        _ ≤ _ := mul_le_mul_right (harea.trans hmono) _
    rw [ENNReal.ofReal_mul hC0.le] at hprod
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hC0).ne'
      ENNReal.ofReal_ne_top).mp hprod

/-- Conditional iteration: all geometric content is isolated in coarse lifting. -/
theorem estimate_of_coarse_lifting (hL : CoarseLifting) (hCF : CoarseFine) :
    ∀ ε : ℝ, 0 < ε → Estimate ε := by
  intro ε hε
  let θ : ℝ := min (ε / 8) (1 / 8)
  have hθ : 0 < θ := lt_min (by positivity) (by norm_num)
  have hθ1 : θ < 1 / 4 := (min_le_right _ _).trans_lt (by norm_num)
  have hb : 4 * θ < 2 := by linarith
  have hbε : 4 * θ < ε := by
    have h := min_le_left (ε / 8) (1 / 8)
    dsimp [θ]
    linarith
  have hq0 : 0 < 1 - θ ^ 2 := by nlinarith
  have hq1 : 1 - θ ^ 2 < 1 := by nlinarith
  apply estimate_of_affine_gain hb hbε hq0 hq1 (estimate_two hCF)
  intro s hs hs2 hEst
  have hi := estimate_improvement hL hCF hθ hθ1 hs.le hs2 hEst
  convert hi using 1
  ring

end WangZahlLot.Obl.wz_normalized_projection_iteration
