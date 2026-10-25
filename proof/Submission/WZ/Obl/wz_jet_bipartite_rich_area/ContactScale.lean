-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.ContactScale.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

/-- Above the natural slope scale, this time separation makes both errors
small enough for the geometric rank descent. -/
theorem contact_scale_separation {δ D σ : ℝ}
    (hδ : 0 < δ) (hD : 0 < D) (hσ : 0 < σ) (hnatural : δ * D ≤ σ ^ 2) :
    0 < 10000 * σ / D ∧
      4 * σ ≤ (D / 120) * (10000 * σ / D) ∧
      8 * (2 * δ) < (D / 120) * (10000 * σ / D) ^ 2 := by
  have hcancel : (D / 120) * (10000 * σ / D) = (250 / 3 : ℝ) * σ := by
    field_simp
    ring
  refine ⟨by positivity, ?_, ?_⟩
  · rw [hcancel]
    nlinarith
  · have heq : (D / 120) * (10000 * σ / D) ^ 2 = (2500000 / 3 : ℝ) * σ ^ 2 / D := by
      field_simp
      ring
    rw [heq]
    apply (lt_div_iff₀ hD).mpr
    nlinarith

/-- The contact separation remains above the original resolution for the
coefficient scales appearing in the frozen theorem. -/
theorem resolution_le_contact_separation {δ D σ : ℝ}
    (hδ : 0 < δ) (hδD : δ ≤ D) (hD : D ≤ 20)
    (hσ : 0 < σ) (hnatural : δ * D ≤ σ ^ 2) : δ ≤ 10000 * σ / D := by
  have hD0 : 0 < D := hδ.trans_le hδD
  have hδσ : δ ≤ σ := by
    have hh := mul_le_mul_of_nonneg_left hδD hδ.le
    nlinarith
  apply (le_div_iff₀ hD0).mpr
  nlinarith

/-- The square-root crowding loss is canceled by the short patch length.
The hypotheses are multiplicative so no denominator clearing is needed by
clients. -/
theorem contact_patch_sqrt_crowding {δ D σ ell H C : ℝ}
    (hδ : 0 < δ) (hD : 0 < D) (hσ : 0 < σ) (hell : 0 ≤ ell)
    (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hstep : ell * σ ≤ δ) (hcrowd : H * δ * D ≤ C * σ ^ 2) :
    δ * ell * Real.sqrt H ≤ Real.sqrt C * δ * Real.sqrt (δ / D) := by
  have hstep2 : ell ^ 2 * σ ^ 2 ≤ δ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (mul_nonneg hell hσ.le) hstep 2
  have hmul := mul_le_mul_of_nonneg_left hcrowd (sq_nonneg ell)
  have hmul' := mul_le_mul_of_nonneg_left hstep2 hC
  have hbound : ell ^ 2 * H * D ≤ C * δ := by
    apply (mul_le_mul_iff_right₀ hδ).mp
    nlinarith only [hmul, hmul']
  have hbound' : ell ^ 2 * H ≤ C * (δ / D) := by
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hD).mpr hbound
  have hsquare : (δ * ell * Real.sqrt H) ^ 2 ≤
      (Real.sqrt C * δ * Real.sqrt (δ / D)) ^ 2 := by
    simp only [mul_pow, Real.sq_sqrt hH, Real.sq_sqrt hC,
      Real.sq_sqrt (div_nonneg hδ.le hD.le)]
    nlinarith only [mul_le_mul_of_nonneg_left hbound' (sq_nonneg δ)]
  exact le_of_sq_le_sq hsquare (by positivity)

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
