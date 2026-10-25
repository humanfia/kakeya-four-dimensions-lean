/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file WorldCaps.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldCapNumerics
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalParameterCaps

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice

namespace Zoom

noncomputable section

/-- The exact original palette cap and prior floor give `BC` inside the
unchanged full coarse prior. The palette cancels before interpolation. -/
theorem interpolated_piece_spatial_cap
    (θ : Measure ScalarLine) (E : Set ScalarIncidence) (t : ℝ)
    {ρ β δ r a H A η d : ℝ}
    (hρ : 0 < ρ) (hβ : 0 < β) (hδ : 0 < δ) (hr : 0 < r) (ha : 0 < a)
    (hH : 0 < H) (hA : 1 ≤ A) (hη : 0 < η) (hd : 0 ≤ d) (hd₁ : d ≤ 1)
    (hδle : δ ≤ ρ * a) (hδge : ρ * a ≤ A * δ) (hβge : ρ * r ≤ A * β)
    (q b : Fin 5 → ℤ) (π : ℝ≥0∞)
    (hcap : ∀ z, θ {l | (l, t) ∈ E ∧ cell β l.2 = b ∧ cell δ (spatial l t) = z} ≤
      ENNReal.ofReal (H * δ ^ (1 + d)) * π)
    (hfloor : ENNReal.ofReal (β ^ (1 + d) / H) * π ≤ θ {l | cell β l.2 = b})
    (hintersection : ENNReal.ofReal η * θ {l | cell β l.2 = b} ≤
      θ {l | cell β l.2 = b ∧ cell ρ l.2 = q}) (v : Fin 2 → ℝ) :
    prior θ ρ q {l | cell β l.2 = b ∧ (l, t) ∈ E ∧
      ∀ e, zoomSpatial ρ q l t e ∈ Ico (v e) (v e + a)} ≤
      ENNReal.ofReal ((9 * H ^ 2 * A ^ 4 / η) * (a / r) ^ (1 + d)) *
        prior θ ρ q {l | cell β l.2 = b} := by
  have hβpow : 0 < β ^ (1 + d) := Real.rpow_pos_of_pos hβ _
  have hraw := prior_piece_spatial_cap θ E t hρ hδ ha.le q b
    (ENNReal.ofReal (H * δ ^ (1 + d))) (ENNReal.ofReal (β ^ (1 + d) / H))
    (ENNReal.ofReal η) π
    (ne_of_gt (ENNReal.ofReal_pos.mpr (div_pos hβpow hH))) ENNReal.ofReal_ne_top
    (ne_of_gt (ENNReal.ofReal_pos.mpr hη)) ENNReal.ofReal_ne_top hcap hfloor hintersection v
  have hconst := interpolated_spatial_cap_constant_ennreal hρ hβ hδ hr ha hH hA hη hd hd₁
    hδle hδge hβge
  exact hraw.trans (mul_le_mul_of_nonneg_right hconst zero_le)

/-- The coarse coefficient bin supplies `AC` by the same original-palette
cancellation, with its FULL prior unchanged. -/
theorem interpolated_absolute_spatial_cap
    (θ : Measure ScalarLine) [IsFiniteMeasure θ] (E : Set ScalarIncidence) (t : ℝ)
    {ρ δ a H A d : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (ha : 0 < a)
    (hH : 0 < H) (hA : 1 ≤ A) (hd : 0 ≤ d) (hd₁ : d ≤ 1)
    (hδle : δ ≤ ρ * a) (hδge : ρ * a ≤ A * δ)
    (q : Fin 5 → ℤ) (hpositive : θ {l | cell ρ l.2 = q} ≠ 0)
    (hworld : ∀ p ∈ E, cell ρ p.1.2 = q) (π : ℝ≥0∞)
    (hcap : ∀ z, θ {l | (l, t) ∈ E ∧ cell ρ l.2 = q ∧ cell δ (spatial l t) = z} ≤
      ENNReal.ofReal (H * δ ^ (1 + d)) * π)
    (hfloor : ENNReal.ofReal (ρ ^ (1 + d) / H) * π ≤ θ {l | cell ρ l.2 = q})
    (v : Fin 2 → ℝ) :
    prior θ ρ q {l | (l, t) ∈ E ∧ ∀ e, zoomSpatial ρ q l t e ∈ Ico (v e) (v e + a)} ≤
      ENNReal.ofReal ((9 * H ^ 2 * A ^ 4) * a ^ (1 + d)) := by
  have hβge : ρ * 1 ≤ A * ρ := by nlinarith
  have hintersection : ENNReal.ofReal (1 : ℝ) * θ {l | cell ρ l.2 = q} ≤
      θ {l | cell ρ l.2 = q ∧ cell ρ l.2 = q} := by simp
  have hh := interpolated_piece_spatial_cap θ E t hρ hρ hδ (by norm_num) ha hH hA
    (by norm_num) hd hd₁ hδle hδge hβge q q π hcap hfloor hintersection v
  have hsame : {l : ScalarLine | cell ρ l.2 = q ∧ (l, t) ∈ E ∧
      ∀ e, zoomSpatial ρ q l t e ∈ Ico (v e) (v e + a)} =
      {l | (l, t) ∈ E ∧ ∀ e, zoomSpatial ρ q l t e ∈ Ico (v e) (v e + a)} := by
    ext l
    exact ⟨fun hl => hl.2, fun hl => ⟨hworld (l, t) hl.1, hl⟩⟩
  have hblock : prior θ ρ q {l | cell ρ l.2 = q} = 1 := by
    simp only [prior, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply' (measurableSet_block ρ q), inter_self]
    exact ENNReal.inv_mul_cancel hpositive (measure_ne_top θ _)
  simpa only [hsame, div_one, hblock, mul_one] using hh

end

end Zoom

namespace ScalarData

open Filter

/-- The frozen preparation hypotheses give the interpolated conditional
cap directly, retaining their canonical mesh, full prior, and original
positive-incidence and prior-intersection requirements. -/
theorem prepData.original_zoom_interpolated_caps {D : ScalarData}
    {H : ℕ → ℝ} {θ : (k : ℕ) → Fin (D.W k) → Measure ScalarLine}
    {E₀ : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence}
    (hprep : D.prepData H θ E₀) (hN : ∀ k, 2 ≤ D.N k)
    (hd : 0 ≤ D.d) (hd₁ : D.d ≤ 1) :
    ∃ M : ℕ → ℕ, (∀ k, 1 ≤ M k ∧ D.N k ^ ((1 : ℝ) / (M k : ℝ)) ≤ H k) ∧
      M = D.prepMesh hprep ∧
      ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ g : Fin (D.W k), ∀ r s : ℝ,
        R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R →
        (∃ m : ℕ, r = (m : ℝ) / (M k : ℝ)) →
        (∃ m : ℕ, s = (m : ℝ) / (M k : ℝ)) →
        ∀ ρ w a A η : ℝ, 0 < ρ → 0 < w → 0 < a → 1 ≤ A → 0 < η →
        D.N k ^ (-s) ≤ ρ * a → ρ * a ≤ A * D.N k ^ (-s) →
        ρ * w ≤ A * D.N k ^ (-r) →
        ∀ (q b : Fin 5 → ℤ) (t : ℝ) (E' : Set ScalarIncidence), E' ⊆ E₀ k g →
        (D.ρ k g).restrict (E₀ k g) {p | D.coeff k r p.1 = b} ≠ 0 →
        ENNReal.ofReal η * θ k g {l | cell (D.N k ^ (-r)) l.2 = b} ≤
          θ k g {l | cell (D.N k ^ (-r)) l.2 = b ∧ cell ρ l.2 = q} →
        ∀ v : Fin 2 → ℝ,
          Zoom.prior (θ k g) ρ q {l | cell (D.N k ^ (-r)) l.2 = b ∧ (l, t) ∈ E' ∧
            ∀ e, Zoom.zoomSpatial ρ q l t e ∈ Ico (v e) (v e + a)} ≤
          ENNReal.ofReal ((9 * H k ^ 2 * A ^ 4 / η) * (a / w) ^ (1 + D.d)) *
            Zoom.prior (θ k g) ρ q {l | cell (D.N k ^ (-r)) l.2 = b} := by
  obtain ⟨M, hM, hMeq, hraw⟩ := hprep.original_zoom_spatial_caps hN
  refine ⟨M, hM, hMeq, ?_⟩
  intro R hR
  filter_upwards [hraw R hR] with k hk
  intro g r s hrlo hrhi hslo hshi hrmesh hsmesh ρ w a A η
    hρ hw ha hA hη hδle hδge hβge q b t E' hE' hpositive hintersection v
  have hN₀ : 0 < D.N k := by linarith [hN k]
  have hH : 0 < H k := lt_of_lt_of_le zero_lt_one (hprep.1.1 k)
  have hnum : D.N k ^ (-s - D.d * s) = (D.N k ^ (-s)) ^ (1 + D.d) := by
    rw [← Real.rpow_mul hN₀.le]
    congr 1
    ring
  have hden : D.N k ^ (-(1 + D.d) * r) = (D.N k ^ (-r)) ^ (1 + D.d) := by
    rw [← Real.rpow_mul hN₀.le]
    congr 1
    ring
  have hh := hk g r s hrlo hrhi hslo hshi hrmesh hsmesh ρ a hρ ha.le q b t E' hE'
    (ENNReal.ofReal η) (ne_of_gt (ENNReal.ofReal_pos.mpr hη)) ENNReal.ofReal_ne_top
    hpositive hintersection v
  rw [hnum, hden] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (interpolated_spatial_cap_constant_ennreal hρ (Real.rpow_pos_of_pos hN₀ _)
      (Real.rpow_pos_of_pos hN₀ _) hw ha hH hA hη hd hd₁ hδle hδge hβge) zero_le)

end ScalarData

end Submission.Obl.k4_scalar_graph_residual_discovery
