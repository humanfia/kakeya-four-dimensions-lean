-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.ClippedWidthEnclosure.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/ClippedWidthEnclosure.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 5604560, ClippedWidthEnclosure.lean.
This is workspace collaboration code; existing local and accepted dependencies are imported. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.InverseWidthEnclosure
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.CarrierMap
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.PacketData

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_flat_factored_improvement (coordinateAffine_dist_upper)
open WangZahlLot.Obl.wz_regular_transverse_affine_cells
  (affineEquiv_dist_bound affine_preimage_density affineEquiv_jacobian_pos affineEquiv_volume)

/-- The clipped chart has explicit forward and inverse distance bounds. -/
theorem carrierAffine_dist_bounds {S c ρ : ℝ}
    (hS : 0 < S) (hc : 0 < c) (hρ : 0 < ρ) (hSc : S ≤ ρ*c)
    (z₀ z' : V) (g : V ≃ₗᵢ[ℝ] V) :
    let f := carrierAffine hS hc hρ z₀ z' g
    (∀ p q, dist (f p) (f q) ≤ (ρ/(4*S))*dist p q) ∧
    (∀ p q, dist (f.symm p) (f.symm q) ≤ (4*c)*dist p q) := by
  dsimp only
  constructor
  · apply coordinateAffine_dist_upper _ _ (by positivity : 0 ≤ ρ/(4*S))
    intro i
    have ht : (4*c)⁻¹ ≤ ρ/(4*S) := by
      apply (le_div_iff₀ (by positivity : 0 < 4*S)).mpr
      have hh := (div_le_iff₀ hc).mpr hSc
      convert hh using 1 <;> field_simp
    fin_cases i
    · change |ρ/(4*S)| ≤ ρ/(4*S)
      rw [abs_of_pos (by positivity : 0 < ρ/(4*S))]
    · change |(4*c)⁻¹| ≤ ρ/(4*S)
      rwa [abs_of_pos (by positivity : 0 < (4*c)⁻¹)]
    · change |(4*c)⁻¹| ≤ ρ/(4*S)
      rwa [abs_of_pos (by positivity : 0 < (4*c)⁻¹)]
  · apply affineEquiv_dist_bound
    have hh := carrier_linear_inverse hS hc hSc g
      (carrierAffine hS hc hρ z₀ z' g).linear
      (carrierAffine_linear _ _ _ _ _ _)
    simpa only [AffineEquiv.linear_symm] using hh

/-- The middle side of a pulled-back packet prism is at most a constant
times its normalized middle side times the old grain length. The clipping
parameter cancels between the Jacobian and the interior-ball estimate. -/
theorem carrierAffine_middle_enclosure {a ρ c S A₀ B₀ C₀ : ℝ}
    (ha : 0 < a) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hc : 0 < c)
    (hac : a ≤ ρ*c) (hS : 0 < S) (hSc : S ≤ ρ*c)
    (hA₀ : 0 < A₀) (hAB₀ : A₀ ≤ B₀) (hBC₀ : B₀ ≤ C₀)
    (z z₀ z' p : V) (e g E : V ≃ₗᵢ[ℝ] V) :
    let f := carrierAffine hS hc hρ z₀ z' g
    f '' P a (ρ*c) c z e ⊆ P A₀ B₀ C₀ p E →
    ∃ (A B : ℝ) (e' : V ≃ₗᵢ[ℝ] V),
      a ≤ A ∧ A ≤ B ∧ B ≤ 96*C₀*c ∧ B ≤ 262144*B₀*C₀*c ∧
      f.symm '' P A₀ B₀ C₀ p E ⊆ P A B (96*C₀*c) (f.symm p) e' ∧
      μ (P A B (96*C₀*c) (f.symm p) e') ≤
        O (786432*C₀)*μ (f.symm '' P A₀ B₀ C₀ p E) := by
  dsimp only
  intro hwhole
  let f := carrierAffine hS hc hρ z₀ z' g
  obtain ⟨hLip,hInv⟩ := carrierAffine_dist_bounds hS hc hρ hSc z₀ z' g
  obtain ⟨A,B,e',haA,hAB,hB,hBwidth,hbox,hvol⟩ :=
    inverse_prism_middle_fixed ha hac (by nlinarith) hA₀ hAB₀ hBC₀
      (by norm_num : (0 : ℝ) < 4) (by positivity : 0 < ρ/(4*S))
      (by positivity : 0 < ρ/(64*S*c^2)) z p e E f hLip hInv
      (carrierAffine_volume hS hc hρ z₀ z' g) hwhole
  have hfactor : 16384*((ρ/(4*S))/(ρ/(64*S*c^2)))*B₀*C₀/c =
      262144*B₀*C₀*c := by field_simp <;> ring
  rw [hfactor] at hBwidth
  norm_num only [show (24 : ℝ)*4=96 by norm_num,
    show (196608 : ℝ)*4=786432 by norm_num] at hB hbox hvol
  exact ⟨A,B,e',haA,hAB,hB,hBwidth,hbox,hvol⟩

/-- Filled normalized density survives the width-controlled enclosure. -/
theorem carrierAffine_dense_enclosure {a ρ c S A₀ B₀ C₀ D : ℝ}
    (ha : 0 < a) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hc : 0 < c)
    (hac : a ≤ ρ*c) (hS : 0 < S) (hSc : S ≤ ρ*c)
    (hA₀ : 0 < A₀) (hAB₀ : A₀ ≤ B₀) (hBC₀ : B₀ ≤ C₀) (hD : 0 ≤ D)
    (z z₀ z' p : V) (e g E : V ≃ₗᵢ[ℝ] V) (H : Set V) :
    let f := carrierAffine hS hc hρ z₀ z' g
    f '' P a (ρ*c) c z e ⊆ P A₀ B₀ C₀ p E →
    H ⊆ P A₀ B₀ C₀ p E → O D*μ (P A₀ B₀ C₀ p E) ≤ μ H →
    ∃ (A B : ℝ) (e' : V ≃ₗᵢ[ℝ] V),
      a ≤ A ∧ A ≤ B ∧ B ≤ 96*C₀*c ∧ B ≤ 262144*B₀*C₀*c ∧
      f.symm '' P A₀ B₀ C₀ p E ⊆ P A B (96*C₀*c) (f.symm p) e' ∧
      f.symm '' H ⊆ P A B (96*C₀*c) (f.symm p) e' ∧
      μ (P A B (96*C₀*c) (f.symm p) e') ≤
        O (786432*C₀)*μ (f.symm '' P A₀ B₀ C₀ p E) ∧
      O (D/(786432*C₀))*μ (P A B (96*C₀*c) (f.symm p) e') ≤ μ (f.symm '' H) := by
  dsimp only
  intro hwhole hH hden
  let f := carrierAffine hS hc hρ z₀ z' g
  have hC₀ : 0 < C₀ := hA₀.trans_le (hAB₀.trans hBC₀)
  obtain ⟨A,B,e',haA,hAB,hB,hwidth,hbox,hvol⟩ :=
    carrierAffine_middle_enclosure ha hρ hρ1 hc hac hS hSc hA₀ hAB₀ hBC₀
      z z₀ z' p e g E hwhole
  have hden' : O D*μ (f.symm '' P A₀ B₀ C₀ p E) ≤ μ (f.symm '' H) := by
    have hh := affine_preimage_density f (affineEquiv_jacobian_pos f)
      (affineEquiv_volume f) (O D) hden
    have he (U : Set V) : f.symm '' U = f ⁻¹' U := by
      ext q
      constructor
      · rintro ⟨r,hr,rfl⟩
        simpa only [mem_preimage,f.apply_symm_apply] using hr
      · intro hq
        exact ⟨f q,hq,f.symm_apply_apply q⟩
    simpa only [he] using hh
  refine ⟨A,B,e',haA,hAB,hB,hwidth,hbox,(image_mono hH).trans hbox,hvol,?_⟩
  calc
    _ ≤ O (D/(786432*C₀))*(O (786432*C₀)*μ (f.symm '' P A₀ B₀ C₀ p E)) :=
      mul_le_mul' le_rfl hvol
    _ = O D*μ (f.symm '' P A₀ B₀ C₀ p E) := by
      rw [← mul_assoc,← ENNReal.ofReal_mul (by positivity : 0 ≤ D/(786432*C₀)),
        div_mul_cancel₀ _ (by positivity : 786432*C₀ ≠ 0)]
    _ ≤ _ := hden'

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
