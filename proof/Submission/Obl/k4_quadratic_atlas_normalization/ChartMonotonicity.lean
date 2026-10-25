import Submission.Obl.k4_quadratic_atlas_normalization.Interface
import Submission.Obl.k4_dyadic_crop_worlds.BooleanFormat

-- Adapted from this LOT tree, o104, session x0350, commit 0e2b59568680,
-- Submission/Obl/k4_terminal_time_extension/ChartMonotonicity.lean.

namespace Submission.Obl.k4_quadratic_atlas_normalization

open Set

/-- Enlarging the polynomial format and the common subpower slack preserves
all chart conditions, including the selected-incidence derivative floor. -/
theorem chart_mono
    {N κ κ' j r B : ℝ} {M M' D D' T : ℕ}
    {E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))}
    {F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex ex' : Prop}
    (hN : 1 ≤ N) (hM : M ≤ M') (hD : D ≤ D')
    (hκ : 0 < κ) (hκκ' : κ ≤ κ') (hB : 0 ≤ B)
    (h : chart N M D κ T j r B E c u Q R A F ex) (hex : ex → ex') :
    chart N M' D' κ' T j r B E c u Q R A F ex' := by
  have hpow : N ^ M ≤ N ^ M' := pow_le_pow_right₀ hN hM
  have hδ : 0 < δ N r := by unfold δ; positivity
  rcases h with ⟨hdet, hcu, hframe, hsize, hdeg, hcoeff, hA, hF,
    hformat, hwhole, hselected, hext⟩
  refine ⟨hdet, hcu.trans hpow, hframe.trans hpow,
    hsize.trans ?_, hdeg, fun e => (hcoeff e).trans hpow, hA, hF, ?_, ?_, ?_, hex hext⟩
  · exact div_le_div_of_nonneg_right hκκ' (by positivity)
  · intro i
    exact ⟨Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono
        (hformat i).1 hpow hD,
      Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono
        (hformat i).2 hpow hD⟩
  · intro l hl
    obtain ⟨htag, hcoords, hfits⟩ := hwhole l hl
    refine ⟨htag.trans hpow, fun e => (hcoords e).trans hpow, ?_⟩
    intro t ht
    obtain ⟨hspatial, hvalue, hderiv, hcurv⟩ := hfits t ht
    refine ⟨hspatial.trans hκκ', hvalue.trans ?_, hderiv.trans ?_, hcurv.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right hκκ' hδ.le
    · exact mul_le_mul_of_nonneg_right hκκ' hB
    · apply div_le_div_of_nonneg_right _ hδ.le
      exact mul_le_mul_of_nonneg_right hκκ' (sq_nonneg B)
  · intro p hp
    obtain ⟨hE, hpA, htime, hderiv⟩ := hselected p hp
    refine ⟨hE, hpA, htime, ?_⟩
    exact (div_le_div_of_nonneg_left hB hκ hκκ').trans hderiv

end Submission.Obl.k4_quadratic_atlas_normalization
