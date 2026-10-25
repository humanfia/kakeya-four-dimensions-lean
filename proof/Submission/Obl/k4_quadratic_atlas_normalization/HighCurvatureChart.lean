import Submission.Obl.k4_quadratic_atlas_normalization.Interface
import Submission.Obl.k4_quadratic_atlas_normalization.Curvature
import Submission.Obl.k4_quadratic_atlas_normalization.ChartMonotonicity

-- Adapted from this LOT tree, o104, session x0350, commit 0e2b59568680,
-- Submission/Obl/k4_terminal_time_extension/HighCurvatureChart.lean.

namespace Submission.Obl.k4_quadratic_atlas_normalization

open Set

/-- Convert a high-curvature rough chart to an exact chart, retaining the entire
original assignment and selected incidence set and all old observation knowledge. -/
theorem high_curvature_chart
    {N κ κ' j L a r B c₀ : ℝ} {M M' D T : ℕ}
    {E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))}
    {F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex : Prop}
    (hN : 1 ≤ N) (hM : M ≤ M') (hκ : 1 ≤ κ) (hκκ' : κ ≤ κ')
    (hB : 0 < B) (hc₀ : 0 < c₀) (hc : c₀ ≤ |curvature R (3 : Fin 4)|)
    (hthick : B ^ 2 * N ^ a / c₀ ≤ δ N r)
    (hcoef : 2 * B * N ^ M / c₀ ≤ N ^ M')
    (h : rough N M D κ T j L a B E c u Q R A F ex) :
    chart N M' D κ' T j r B E c u Q (criticalCenterTest R 3 B) A F ex := by
  have hpow : N ^ M ≤ N ^ M' := pow_le_pow_right₀ hN hM
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hκ' : 1 ≤ κ' := hκ.trans hκκ'
  have hδ : 0 < δ N r := by unfold δ; positivity
  have hcne : curvature R (3 : Fin 4) ≠ 0 :=
    abs_pos.mp (hc₀.trans_le hc)
  rcases h with ⟨hdet, hcu, hframe, hsize, hdeg, hcoeff, hA, hF,
    hformat, hwhole, hselected, _hdiscriminant, hext⟩
  have hd := criticalCenterTest_pderiv R hdeg 3 B hcne
  have hdd := criticalCenterTest_second_pderiv R hdeg 3 B hcne
  refine ⟨hdet, hcu.trans hpow, hframe.trans hpow,
    hsize.trans (div_le_div_of_nonneg_right hκκ' (by positivity)),
    (criticalCenterTest_totalDegree R hdeg 3 B).trans (by norm_num),
    ?_, hA, hF, ?_, ?_, ?_, hext⟩
  · intro e
    exact (criticalCenterTest_coeff_bound R hdeg 3 hB.le hc₀ hc
      (by positivity) hcoeff e).trans hcoef
  · intro i
    exact ⟨Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono (hformat i).1 hpow le_rfl,
      Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono (hformat i).2 hpow le_rfl⟩
  · intro l hl
    obtain ⟨htag, hcoords, hfits⟩ := hwhole l hl
    refine ⟨htag.trans hpow, fun e => (hcoords e).trans hpow, ?_⟩
    intro t ht
    obtain ⟨hspatial, _hvalue, hderiv, _hcurv⟩ := hfits t ht
    refine ⟨hspatial.trans hκκ', ?_, ?_, ?_⟩
    · calc
        |MvPolynomial.eval (x l t) (criticalCenterTest R 3 B)| ≤
            B * (κ * B * N ^ a) / c₀ :=
          criticalCenterTest_eval_bound R 3 hB.le hc₀ hc _ hderiv
        _ = κ * (B ^ 2 * N ^ a / c₀) := by ring
        _ ≤ κ * δ N r := mul_le_mul_of_nonneg_left hthick hκpos.le
        _ ≤ κ' * δ N r := mul_le_mul_of_nonneg_right hκκ' hδ.le
    · simp only [hd, MvPolynomial.eval_C, abs_of_pos hB]
      exact le_mul_of_one_le_left hB.le hκ'
    · simp only [hdd, map_zero, abs_zero]
      positivity
  · intro p hp
    obtain ⟨hpE, hpA, htime⟩ := hselected p hp
    refine ⟨hpE, hpA, htime, ?_⟩
    simp only [hd, MvPolynomial.eval_C, abs_of_pos hB]
    exact div_le_self hB.le hκ'

end Submission.Obl.k4_quadratic_atlas_normalization
