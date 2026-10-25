-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.SmallParams.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.SmallQuantitative
import Submission.WZ.Obl.wz_coarse_grains_assembly.FibreSize
import Submission.WZ.Obl.wz_coarse_grains_assembly.Core
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.ColorBudget

/-!
# The small-radius case: choice of the parameters

x0448's `small_radius_quantitative` proves the small-radius case (`ρ ≤ 1/2`, new scale `2ρ`)
under explicit scalar hypotheses.  Here they are met for all small `δ`:

* the single-tube theorem at error `e = ε/20` (`tube_packets_of`) gives `η` and its cutoff;
* `θ = min (η/10) (ε/100)`;
* one cutoff `8 (10^40+1) ≤ δ^(-θ)` absorbs every constant;
* the size coloring of ratio `4/3 ≤ 2` with `K ≤ δ^(-ε/10)` colors comes from the accepted
  `regularization_color_budget` (`B = 1`), which needs `n ≤ δ^(-7)`
  (`fine_count_power_seven`, a packing bound; no Katz–Tao hypothesis).
-/

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open MeasureTheory

/-- The small-radius case of o178, from the single-tube theorem. -/
theorem small_radius_grains (hTG : TubeGrains) {ω ζ ε : ℝ}
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hζ : 0 < ζ) (hζω : ζ ≤ ω / 1000)
    (hε : 0 < ε) (hεζ : ε ≤ ζ / 100) : SmallRadiusGrains ω ζ ε := by
  classical
  have hζ1 : ζ ≤ 1 := hζω.trans (by linarith)
  have he : 0 < ε / 20 := by positivity
  obtain ⟨η, dT, hη, hdT, hTP⟩ :=
    tube_packets_of hTG (by positivity : 0 < ω * ζ / 100) (by positivity : 0 < ζ / 2) he
  set θ := min (η / 10) (ε / 100) with hθdef
  have hθ : 0 < θ := lt_min (by positivity) (by positivity)
  have hθη : θ ≤ η / 10 := min_le_left _ _
  have hθε : θ ≤ ε / 100 := min_le_right _ _
  set D : ℝ := 8 * (10 ^ 40 + 1) with hD
  obtain ⟨dB, hdB, hdB1, hB⟩ :=
    WangZahlLot.Obl.wz_terminal_grains_restoration.const_le_rpow_neg hθ D
  obtain ⟨dC, hdC, hcolor⟩ :=
    WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.regularization_color_budget
      (show 0 < ε / 10 by positivity) 1
  refine ⟨θ, min (min dT dB) dC, hθ, hθε.trans (by linarith),
    lt_min (lt_min hdT hdB) hdC, ?_⟩
  intro δ hδ hδd n x v Y hA ρ hρlo hρh S Z N y w f hC hbr hreg
  have hδT : δ ≤ dT := hδd.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδB : δ ≤ dB := hδd.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδC : δ ≤ dC := hδd.trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := hδB.trans hdB1
  -- the single cutoff and its consequences
  have hDθ : D ≤ δ ^ (-θ) := hB δ hδ hδB
  have hDge (c : ℝ) (hc : c ≤ D) : c ≤ δ ^ (-θ) := hc.trans hDθ
  have hmono {a b : ℝ} (hab : a ≤ b) : δ ^ (-a) ≤ δ ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  obtain ⟨hn, hgeo, hX, hmassY, -⟩ := hA
  have hv : ∀ i, ‖v i‖ = 1 := fun i => (hgeo i).1
  have hball : ∀ i, T δ (x i) (v i) ⊆ I := fun i => (hgeo i).2.1
  -- the fine family is polynomially bounded
  have h12 : (1000000000000 : ℝ) ≤ δ ^ (-3 : ℝ) :=
    (hDge _ (by norm_num [hD])).trans (hmono (by linarith : θ ≤ 3))
  have hn7 : (n : ℝ) ≤ δ ^ (-7 : ℝ) := fine_count_power_seven hδ h12 hv hball hX
  obtain ⟨K, hK, hKpow, color, hcol⟩ := hcolor δ n hδ hδ1 hδC hn hn7
  have hKle : (K : ℝ) ≤ δ ^ (-(ε / 10)) := by simpa only [pow_one] using hKpow
  have hcol2 : ∀ a b : ℕ, 0 < a → a ≤ n → 0 < b → b ≤ n →
      color a = color b → (a : ℝ) ≤ 2 * b := by
    intro a b ha han hb hbn hab
    have h := hcol a b ha han hb hbn hab
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    linarith
  -- scalar hypotheses of `small_radius_quantitative`
  have hsmall : 2 * δ ^ (4 * θ) ≤ δ ^ (2 * θ) :=
    rpow_absorb hδ hδ1 (p := 2 * θ) (hDge 2 (by norm_num [hD]) |>.trans (hmono (by linarith)))
      (by linarith)
  have hloss : 2 * δ ^ (-θ) ≤ δ ^ (-η) :=
    rpow_absorb hδ hδ1 (hDge 2 (by norm_num [hD])) (by linarith)
  have htwo : 2 ≤ δ ^ (-η) := (hDge 2 (by norm_num [hD])).trans (hmono (by linarith))
  have hwidth : 16 * δ ≤ δ ^ (1 - ζ / 2) := by
    have hh := rpow_absorb hδ hδ1 (hDge 16 (by norm_num [hD])) (a := 1) (b := 1 - ζ / 2)
      (by linarith)
    simpa only [Real.rpow_one] using hh
  have hlevel : 4 * δ ^ (-(ε / 20)) ≤ δ ^ (-ε) :=
    rpow_absorb hδ hδ1 (hDge 4 (by norm_num [hD])) (by linarith)
  have h56 : 56 ≤ δ ^ (-(ε / 4)) := (hDge 56 (by norm_num [hD])).trans (hmono (by linarith))
  have hcontain : 10 ^ 15 ≤ δ ^ (-ε) :=
    (hDge (10 ^ 15) (by norm_num [hD])).trans (hmono (by linarith))
  have hbudget : (8 * (K : ℝ) * (10 ^ 40 + 1)) * δ ^ (ε / 2) ≤ δ ^ (θ + ε / 20) := by
    have h1 : (8 * (K : ℝ) * (10 ^ 40 + 1)) * δ ^ (ε / 2) ≤
        D * (δ ^ (-(ε / 10)) * δ ^ (ε / 2)) := by
      have hKn : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      have hp : 0 ≤ δ ^ (ε / 2) := Real.rpow_nonneg hδ.le _
      calc (8 * (K : ℝ) * (10 ^ 40 + 1)) * δ ^ (ε / 2)
          = D * ((K : ℝ) * δ ^ (ε / 2)) := by rw [hD]; ring
        _ ≤ D * (δ ^ (-(ε / 10)) * δ ^ (ε / 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num [hD])
          exact mul_le_mul_of_nonneg_right hKle hp
    have h2 : δ ^ (-(ε / 10)) * δ ^ (ε / 2) = δ ^ (2 * ε / 5) := by
      rw [← Real.rpow_add hδ]; congr 1; ring
    rw [h2] at h1
    exact h1.trans (rpow_absorb hδ hδ1 hDθ (by linarith))
  have hfinite : ∀ i, μ (Z i) ≠ ⊤ := by
    intro i
    have hsub : Z i ⊆ I := ((hC.1 i).2.1.trans (hgeo i).2.2.2).trans (hball i)
    exact ne_top_of_le_ne_top (measure_ball_lt_top (μ := volume)).ne (measure_mono hsub)
  have hδρ : δ ≤ ρ := by
    refine le_trans ?_ hρlo
    have h := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (show 1 - ω / 100 ≤ 1 by linarith)
    simpa only [Real.rpow_one] using h
  obtain ⟨S', Z', N', y', w', f', c, g, hC', hg, hbr', hH', hlen⟩ :=
    small_radius_quantitative hTP hω hω1 hζ hζ1 hε hθ (by linarith) hδ hδ1 hδT hδρ hρh
      hsmall (by linarith) hloss htwo (by linarith) (by linarith) hwidth hlevel h56 hcontain
      hK color hcol2 hbudget hn (fun i => ⟨hv i, (hgeo i).2.2.2⟩) hX hfinite hmassY hC hbr hreg
  have hρ : 0 < ρ := hδ.trans_le hδρ
  exact ⟨2 * ρ, S', Z', N', y', w', f', 16 * δ, c, g, by linarith, hC', hg, hbr', hH', hlen⟩

end WangZahlLot.Obl.wz_coarse_grains_assembly
