/- Adapted from: here:o222, session x0774, commit 0d01aa57.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/RowAffineRefinement.lean. -/
import Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation.StableRowPalette
import Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation.ContactSheetSelection

/-! One original affine hidden sheet on a refined dense row parent. -/

namespace Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation

open MeasureTheory Set MvPolynomial Filter
open Submission.Lib.K4ContactNormalization (point affineBase)
open Submission.Obl.k4_scalar_marked_coefficient_smoothing
  (subpower_max subpower_polynomial)

noncomputable section

/-- Every eligible late row parent has a refinement fitted by one affine
sheet on its whole original time block. The mass still uses the original
prior and block length. -/
theorem eventually_row_affine_refinement {α : Type} [MeasurableSpace α]
    (p : Submission.Obl.k4_general_parent_projected_layers.Parameters) (hp : p.Valid) (a : Submission.Obl.k4_general_parent_projected_layers.PreparedModel α) (hcommon : a.Common p)
    (hcaps : a.Caps p) (hatlases : a.Atlases p) {r e₀ : ℝ}
    (hr : 0 < r) (hrU : r ≤ p.U) (he₀ : 0 < e₀)
    (M : ℕ → ℝ) (hM : ∀ k, 1 ≤ M k)
    (hMsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, M k ≤ p.N k ^ ε) :
    ∃ M' : ℕ → ℝ, (∀ k, 1 ≤ M' k) ∧ (∀ k, M k ≤ M' k) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, M' k ≤ p.N k ^ ε) ∧
      ∀ᶠ k in atTop,
        ∀ RP : CoarseRowParent p a k r (M k * p.N k ^ (-e₀)) (M k),
          RP.lam ≠ 0 → |RP.lam⁻¹| ≤ M k →
          ∃ RP' : CoarseRowParent p a k r (M' k * p.N k ^ (-e₀)) (M' k),
            ∃ L : Fin 4 → ℝ, RP'.lam ≠ 0 ∧ |RP'.lam⁻¹| ≤ M' k ∧
              ∀ z ∈ RP'.G, ∀ t ∈ a.block k r RP'.Q,
                |eval (point (a.b k z.1) t) (affineBase L) - point (a.b k z.1) t 3| ≤
                  M' k * Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width p k r := by
  obtain ⟨B, hB, hsource⟩ := eventually_stable_row_sources p hp a hcommon hcaps hatlases
    hr hrU M hM hMsub
  obtain ⟨H, hH, hHsub, hpalette⟩ := exists_stable_row_palette p hp a hcommon hcaps hatlases
    hr hrU he₀ hB.le M hM hMsub
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [hp.1 k]
  have h6M : Submission.Obl.k4_scalar_marked_coefficient_smoothing.Subpower p.N (fun k => 6 * M k) := by
    simpa only [pow_one] using
      subpower_polynomial hN1 hp.2.1 (show Submission.Obl.k4_scalar_marked_coefficient_smoothing.Subpower p.N M from ⟨hM, hMsub⟩)
        (show (1 : ℝ) ≤ 6 by norm_num) 1
  have hM' := subpower_max h6M (show Submission.Obl.k4_scalar_marked_coefficient_smoothing.Subpower p.N H from ⟨hH, hHsub⟩)
  let M' : ℕ → ℝ := fun k => max (6 * M k) (H k)
  have hMM' : ∀ k, M k ≤ M' k := fun k =>
    (show M k ≤ 6 * M k by linarith [hM k]).trans (le_max_left _ _)
  refine ⟨M', hM'.1, hMM', hM'.2, ?_⟩
  filter_upwards [hsource, hpalette] with k hksource hkpalette
  intro RP hlam hinv
  obtain ⟨S, hSRP⟩ := hksource RP hlam hinv
  subst RP
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have ha : 0 < Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width p k r := Real.rpow_pos_of_pos hN _
  have hq : 0 < a.q k r := by unfold Submission.Obl.k4_general_parent_projected_layers.PreparedModel.q; positivity
  have hMpos : 0 < M k := zero_lt_one.trans_le (hM k)
  letI : IsProbabilityMeasure (a.nu k) := (hcommon k).2.1
  obtain ⟨L, hL⟩ := S.rowParent.chart.cover_pullback S.law (a.pi k)
    (fun z : α × ℝ => a.b k z.1) Prod.snd (a.F k r S.rowParent.Q)
    (S.rowParent.chart_ok hp) S.lam_ne hq (hkpalette S)
  have hInv : (ENNReal.ofReal S.weight)⁻¹ ≠ 0 := by
    simp only [ne_eq, ENNReal.inv_eq_zero]
    exact ENNReal.ofReal_ne_top
  have hLsrc := (Measure.ae_ennreal_smul_measure_iff (μ := S.source) hInv).mp hL
  rw [StableRowSource.source, ae_restrict_iff' S.measurable_keep] at hLsrc
  have horig : ∀ᵐ z ∂a.rho k, z ∈ S.keep → ∃ i : Fin 3,
      z.1 ∈ affineSheetLines (a.b k) (a.block k r S.rowParent.Q) (L i)
        (H k * Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width p k r) := by
    filter_upwards [hLsrc] with z hz hzkeep
    obtain ⟨i, hi⟩ := hz hzkeep
    refine ⟨i, ?_⟩
    intro t ht
    have ht' := parentAffineZoom_block p a k r S.rowParent.Q ▸ ht
    have h := hi t ht'
    simpa only [CoarseRowParent.chart, parentAffineZoom, abs_of_pos ha,
      mul_comm (Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width p k r) (H k)] using h
  have hmass : ENNReal.ofReal (S.weight / (2 * M k)) ≤ a.rho k S.keep := by
    calc
      _ = ENNReal.ofReal (a.q k r / (2 * M k)) * a.nu k (a.A k r S.rowParent.Q) := by
        calc
          _ = ENNReal.ofReal ((a.q k r / (2 * M k)) *
              (a.nu k (a.A k r S.rowParent.Q)).toReal) := by
            congr 1
            dsimp [StableRowSource.weight]
            ring
          _ = _ := by
            rw [ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ _ := S.mass
  obtain ⟨i, G', hG'm, hG'sub, hG'mass, hG'fit⟩ := select_full_time_affine_sheet
    (a.rho k) (a.b k) (hcommon k).1 S.keep S.measurable_keep
    (a.block k r S.rowParent.Q) L hmass horig
  have h6mass : ENNReal.ofReal (a.q k r / (6 * M k)) *
      a.nu k (a.A k r S.rowParent.Q) ≤ a.rho k G' := by
    convert hG'mass using 1
    calc
      _ = ENNReal.ofReal ((a.q k r / (6 * M k)) *
          (a.nu k (a.A k r S.rowParent.Q)).toReal) := by
        rw [ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ = _ := by
        congr 1
        dsimp [StableRowSource.weight]
        field_simp [hMpos.ne']
        ring
  have hmass' : ENNReal.ofReal (a.q k r / M' k) *
      a.nu k (a.A k r S.rowParent.Q) ≤ a.rho k G' := by
    refine le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl) h6mass
    exact div_le_div_of_nonneg_left hq.le (by positivity : 0 < 6 * M k) (le_max_left _ _)
  let RP' : CoarseRowParent p a k r (M' k * p.N k ^ (-e₀)) (M' k) := {
    Q := S.rowParent.Q
    B := S.rowParent.B
    lam := S.rowParent.lam
    G := G'
    measurable_G := hG'm
    G_sub := fun z hz => S.rowParent.G_sub (hG'sub hz).1
    mass := hmass'
    B_le := S.rowParent.B_le.trans (hMM' k)
    lam_le := S.rowParent.lam_le.trans (hMM' k)
    row := fun z hz => (S.rowParent.row z (hG'sub hz).1).trans
      (mul_le_mul_of_nonneg_right (hMM' k) (by positivity)) }
  refine ⟨RP', L i, S.lam_ne, S.inv_le.trans (hMM' k), ?_⟩
  intro z hz t ht
  exact (hG'fit z hz t ht).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) ha.le)

/-- The frequent row-parent input expected by the contact back end. -/
theorem frequently_row_affine_refinement {α : Type} [MeasurableSpace α]
    (p : Submission.Obl.k4_general_parent_projected_layers.Parameters) (hp : p.Valid) (a : Submission.Obl.k4_general_parent_projected_layers.PreparedModel α) (hcommon : a.Common p)
    (hcaps : a.Caps p) (hatlases : a.Atlases p) {r e₀ : ℝ}
    (hr : 0 < r) (hrU : r ≤ p.U) (he₀ : 0 < e₀)
    (M : ℕ → ℝ) (hM : ∀ k, 1 ≤ M k)
    (hMsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, M k ≤ p.N k ^ ε)
    (hfreq : ∃ᶠ k in atTop,
      ∃ RP : CoarseRowParent p a k r (M k * p.N k ^ (-e₀)) (M k),
        RP.lam ≠ 0 ∧ |RP.lam⁻¹| ≤ M k) :
    ∃ M' : ℕ → ℝ, (∀ k, 1 ≤ M' k) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, M' k ≤ p.N k ^ ε) ∧
      ∃ᶠ k in atTop,
        ∃ RP : CoarseRowParent p a k r (M' k * p.N k ^ (-e₀)) (M' k),
          ∃ L : Fin 4 → ℝ, RP.lam ≠ 0 ∧ |RP.lam⁻¹| ≤ M' k ∧
            ∀ z ∈ RP.G, ∀ t ∈ a.block k r RP.Q,
              |eval (point (a.b k z.1) t) (affineBase L) - point (a.b k z.1) t 3| ≤
                M' k * Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width p k r := by
  obtain ⟨M', hM', _hMM', hM'sub, hlate⟩ := eventually_row_affine_refinement
    p hp a hcommon hcaps hatlases hr hrU he₀ M hM hMsub
  refine ⟨M', hM', hM'sub, ?_⟩
  apply (hfreq.and_eventually hlate).mono
  rintro k ⟨⟨RP, hlam, hinv⟩, hk⟩
  exact hk RP hlam hinv

end

end Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation
