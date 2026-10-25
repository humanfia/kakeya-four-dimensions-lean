-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.InverseWidthEnclosure.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/InverseWidthEnclosure.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 5604560, InverseWidthEnclosure.lean.
This is workspace collaboration code; existing local and accepted dependencies are imported. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.WidthEnclosure
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CoarseAffine

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (boxAxis boxAxis_norm frozen_prism_compact frozen_prism_convex frozen_prism_norm
    frozen_prism_ends ball_subset_frozen_prism inverse_affine_volume)
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (ball_subset_affine_preimage)

/-- An affine inverse prism has a comparable orthogonal enclosure whose
middle width also remembers the normalized middle width. -/
theorem inverse_prism_middle_enclosure {a b c A₀ B₀ C₀ K L J : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hA₀ : 0 < A₀) (hAB₀ : A₀ ≤ B₀) (hBC₀ : B₀ ≤ C₀)
    (hK : 0 < K) (hL : 0 < L) (hJ : 0 < J)
    (z z₀ : V) (e e₀ : V ≃ₗᵢ[ℝ] V) (f : V ≃ᵃ[ℝ] V)
    (hLip : ∀ p q, dist (f p) (f q) ≤ L*dist p q)
    (hInv : ∀ p q, dist (f.symm p) (f.symm q) ≤ (K*c)*dist p q)
    (hJac : ∀ U : Set V, μ (f '' U) = O J*μ U)
    (hwhole : f '' P a b c z e ⊆ P A₀ B₀ C₀ z₀ e₀) :
    ∃ (A B C : ℝ) (e' : V ≃ₗᵢ[ℝ] V),
      a ≤ A ∧ A ≤ B ∧ B ≤ C ∧ C ≤ 24*K*C₀*c ∧ c ≤ 2*C ∧
      B ≤ 16384*(L/J)*B₀*C₀/c ∧
      f.symm '' P A₀ B₀ C₀ z₀ e₀ ⊆ P A B C (f.symm z₀) e' ∧
      μ (P A B C (f.symm z₀) e') ≤ O 4096*μ (f.symm '' P A₀ B₀ C₀ z₀ e₀) := by
  have hc : 0 < c := ha.trans_le (hab.trans hbc)
  have hB₀ : 0 < B₀ := hA₀.trans_le hAB₀
  have hC₀ : 0 < C₀ := hB₀.trans_le hBC₀
  let U := f.symm '' P A₀ B₀ C₀ z₀ e₀
  have hpre : U = f ⁻¹' P A₀ B₀ C₀ z₀ e₀ := by
    ext p
    simp only [U, mem_image, mem_preimage]
    exact ⟨fun ⟨q,hq,he⟩ => he ▸ by simpa using hq,
      fun hp => ⟨f p,hp,f.symm_apply_apply p⟩⟩
  have hball : ball (f.symm z₀) (A₀/(2*L)) ⊆ U := by
    rw [hpre]
    have hh := (ball_subset_affine_preimage f hL hLip z₀ (r := A₀/2)).trans
      (preimage_mono (ball_subset_frozen_prism hAB₀ hBC₀ z₀ e₀))
    convert hh using 1 <;> congr 1 <;> ring
  have hbound : U ⊆ closedBall (f.symm z₀) (K*C₀*c) := by
    rintro _ ⟨p,hp,rfl⟩
    rw [mem_closedBall]
    calc
      _ ≤ (K*c)*dist p z₀ := hInv p z₀
      _ ≤ (K*c)*C₀ := mul_le_mul_of_nonneg_left
        (frozen_prism_norm hA₀.le hAB₀ hBC₀ z₀ e₀ hp) (by positivity)
      _ = _ := by ring
  have hbody : P a b c z e ⊆ U := by
    intro p hp
    exact ⟨f p,hwhole (mem_image_of_mem f hp),f.symm_apply_apply p⟩
  have hdiam : ∃ p ∈ U, ∃ q ∈ U, c ≤ dist p q := by
    obtain ⟨hp,hq⟩ := frozen_prism_ends ha.le (ha.le.trans hab) hc.le z e
    refine ⟨_,hbody hp,_,hbody hq,?_⟩
    have heq : (z+(c/2) • boxAxis e 2)-(z-(c/2) • boxAxis e 2) = c • boxAxis e 2 := by module
    rw [dist_eq_norm,heq,norm_smul,boxAxis_norm,mul_one,Real.norm_eq_abs,abs_of_pos hc]
  have hvolume : μ U = O (J⁻¹*A₀*B₀*C₀) := by
    have hPvol : μ (P A₀ B₀ C₀ z₀ e₀) = O (A₀*B₀*C₀) :=
      WangZahlLot.Obl.wz_move_three_thick_grains_gain.volume_P hA₀.le hB₀.le hC₀.le _ _
    change μ (f.symm '' P A₀ B₀ C₀ z₀ e₀) = _
    have hinverse : μ (f.symm '' P A₀ B₀ C₀ z₀ e₀) = O J⁻¹*μ (P A₀ B₀ C₀ z₀ e₀) :=
      inverse_affine_volume hJ f hJac _
    rw [hinverse,hPvol,
      ← ENNReal.ofReal_mul (inv_pos.mpr hJ).le]
    congr 1
    ring
  obtain ⟨A,B,C,e',_,hAB,hBC,hC,hcC,hB,hbox,hvol⟩ :=
    convex_prism_middle_bound
      ((frozen_prism_compact hA₀.le hAB₀ hBC₀ z₀ e₀).image
        f.symm.toContinuousAffineEquiv.continuous)
      ((frozen_prism_convex A₀ B₀ C₀ z₀ e₀).affine_image f.symm.toAffineMap)
      (by positivity : 0 < A₀/(2*L)) hc hball hbound hdiam hvolume.le
  refine ⟨A,B,C,e',prism_short_le_of_subset ha.le hab (hab.trans hbc)
    z (f.symm z₀) e e' (hbody.trans hbox),hAB,hBC,?_,hcC,?_,hbox,hvol⟩
  · nlinarith only [hC]
  · convert hB using 1 <;> field_simp <;> ring

/-- Fixing the enclosing long side to a common multiple of the old length
preserves the middle-width bound, at a constant volume cost. -/
theorem inverse_prism_middle_fixed {a b c A₀ B₀ C₀ K L J : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hA₀ : 0 < A₀) (hAB₀ : A₀ ≤ B₀) (hBC₀ : B₀ ≤ C₀)
    (hK : 0 < K) (hL : 0 < L) (hJ : 0 < J)
    (z z₀ : V) (e e₀ : V ≃ₗᵢ[ℝ] V) (f : V ≃ᵃ[ℝ] V)
    (hLip : ∀ p q, dist (f p) (f q) ≤ L*dist p q)
    (hInv : ∀ p q, dist (f.symm p) (f.symm q) ≤ (K*c)*dist p q)
    (hJac : ∀ U : Set V, μ (f '' U) = O J*μ U)
    (hwhole : f '' P a b c z e ⊆ P A₀ B₀ C₀ z₀ e₀) :
    ∃ (A B : ℝ) (e' : V ≃ₗᵢ[ℝ] V),
      a ≤ A ∧ A ≤ B ∧ B ≤ 24*K*C₀*c ∧ B ≤ 16384*(L/J)*B₀*C₀/c ∧
      f.symm '' P A₀ B₀ C₀ z₀ e₀ ⊆ P A B (24*K*C₀*c) (f.symm z₀) e' ∧
      μ (P A B (24*K*C₀*c) (f.symm z₀) e') ≤
        O (196608*K*C₀)*μ (f.symm '' P A₀ B₀ C₀ z₀ e₀) := by
  obtain ⟨A,B,C,e',haA,hAB,hBC,hC,hcC,hB,hbox,hvol⟩ :=
    inverse_prism_middle_enclosure ha hab hbc hA₀ hAB₀ hBC₀ hK hL hJ
      z z₀ e e₀ f hLip hInv hJac hwhole
  have hA : 0 < A := ha.trans_le haA
  have hBpos : 0 < B := hA.trans_le hAB
  have hCpos : 0 < C := hBpos.trans_le hBC
  have hc : 0 < c := ha.trans_le (hab.trans hbc)
  have hC₀ : 0 < C₀ := hA₀.trans_le (hAB₀.trans hBC₀)
  have hlen : 0 < 24*K*C₀*c := by positivity
  have hP : P A B C (f.symm z₀) e' ⊆ P A B (24*K*C₀*c) (f.symm z₀) e' := by
    intro p hp
    exact ⟨hp.1,hp.2.1,hp.2.2.trans (by linarith)⟩
  refine ⟨A,B,e',haA,hAB,hBC.trans hC,hB,hbox.trans hP,?_⟩
  have hPV : μ (P A B C (f.symm z₀) e') = O (A*B*C) :=
    WangZahlLot.Obl.wz_move_three_thick_grains_gain.volume_P hA.le hBpos.le hCpos.le _ _
  have hPV' : μ (P A B (24*K*C₀*c) (f.symm z₀) e') = O (A*B*(24*K*C₀*c)) :=
    WangZahlLot.Obl.wz_move_three_thick_grains_gain.volume_P hA.le hBpos.le hlen.le _ _
  have hscale : μ (P A B (24*K*C₀*c) (f.symm z₀) e') ≤
      O (48*K*C₀)*μ (P A B C (f.symm z₀) e') := by
    rw [hPV',hPV,← ENNReal.ofReal_mul (by positivity : 0 ≤ 48*K*C₀)]
    apply ENNReal.ofReal_le_ofReal
    have hh := mul_le_mul_of_nonneg_left hcC (by positivity : 0 ≤ (A*B)*(24*K*C₀))
    nlinarith only [hh]
  calc
    _ ≤ O (48*K*C₀)*(O 4096*μ (f.symm '' P A₀ B₀ C₀ z₀ e₀)) :=
      hscale.trans (mul_le_mul' le_rfl hvol)
    _ = _ := by
      rw [← mul_assoc,← ENNReal.ofReal_mul (by positivity : 0 ≤ 48*K*C₀)]
      congr 2
      ring

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
