-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.PreparationFinite.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Preparation
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.RegularityFinite

/-! Residual preparation at an entire finite palette of extension lengths. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set Metric MeasureTheory
open scoped ENNReal

/-- Preserve one strongly regular shading while separately retaining the
original fibre multiplicities up to the fixed factor thirty-two. -/
theorem prepare_residual_shading_finite {n N J : ℕ} (hJ : 0 < J) {d R q t : ℝ}
    (r : Fin J → ℝ)
    (hd : 0 < d) (hr : ∀ j, 0 < r j) (hr1 : ∀ j, r j ≤ 1) (hdr : ∀ j, d ≤ r j/8)
    (hdR : d ≤ R) (hendpoint : 4608*R ≤ q) (ht : 0 ≤ t)
    (x v : Fin n → V) (hv : ∀ i, ‖v i‖ = 1) (f : Fin n → Fin N)
    (Z Y : Fin n → Set V) (hZm : ∀ i, MeasurableSet (Z i))
    (hYm : ∀ i, MeasurableSet (Y i)) (hZT : ∀ i, Z i ⊆ T d (x i) (v i))
    (hYZ : ∀ i, Y i ⊆ Z i)
    (hretain : (1/2 : ENNReal) * (∑ i, volume (Z i)) ≤ ∑ i, volume (Y i))
    (hmin : O (4*(n : ℝ)*t) ≤ ∑ i, volume (Y i))
    (hdense : O (q*(n : ℝ)*d^2) ≤ ∑ i, volume (Y i)) :
    ∃ U W : Fin n → Set V,
      (∀ i, MeasurableSet (U i) ∧ U i ⊆ Y i) ∧
      (∀ i, MeasurableSet (W i) ∧ W i ⊆ U i) ∧
      (∀ i p, p ∈ U i → R < dist p (x i) ∧ R < dist p (x i+v i)) ∧
      (∀ i p, p ∈ U i → ∀ j, O (r j*t/(32*J)) ≤ volume (U i ∩ ball p (r j))) ∧
      O (1/32) * (∑ i, volume (Z i)) ≤ ∑ i, volume (W i) ∧
      ∀ k p, (∃ i, f i = k ∧ p ∈ W i) →
        wz_clustered_cover_volume_gain.fiberBodyCount f Z k p ≤
          32*wz_clustered_cover_volume_gain.fiberBodyCount f W k p := by
  have hZfin (i) : volume (Z i) ≠ ∞ := measure_ne_top_of_subset (hZT i)
    ((isBounded_closedBall.subset (segment_subset_closedBall_left (x i) (x i+v i))).thickening.measure_lt_top).ne
  obtain ⟨E, hE, hEend, hEmass⟩ := shading_away_from_endpoints hd hdR hendpoint
    x v Y hv hYm (fun i => (hYZ i).trans (hZT i)) hdense
  have hEfin (i) : volume (E i) ≠ ∞ :=
    measure_ne_top_of_subset ((hE i).2.trans (hYZ i)) (hZfin i)
  have hbudget : O ((n : ℝ)*t) ≤ (1/2 : ENNReal) * ∑ i, volume (E i) := by
    calc
      _ = (1/4 : ENNReal) * O (4*(n : ℝ)*t) := by
        change ENNReal.ofReal ((n : ℝ)*t) = (1/4 : ENNReal) * ENNReal.ofReal (4*(n : ℝ)*t)
        rw [show 4*(n : ℝ)*t = 4*((n : ℝ)*t) by ring,
          ENNReal.ofReal_mul (by norm_num)]
        norm_num [← mul_assoc, ENNReal.inv_mul_cancel]
      _ ≤ (1/4 : ENNReal) * ∑ i, volume (Y i) := mul_le_mul_right hmin _
      _ = (1/2 : ENNReal) * ((1/2 : ENNReal) * ∑ i, volume (Y i)) := by
        norm_num [← mul_assoc, ← ENNReal.mul_inv]
      _ ≤ _ := mul_le_mul_right hEmass _
  obtain ⟨Q, hQ, hQmass⟩ := prune_small_tubes E (fun i => (hE i).1) hEfin ht hbudget
  obtain ⟨U, hU, hUmass, hUreg⟩ := regular_shading_family_finite hJ r hr hr1 hdr ht x v hv Q
    (fun i => (hQ i).1) (fun i => (hQ i).2.1.trans ((hE i).2.trans ((hYZ i).trans (hZT i))))
    (fun i => (hQ i).2.2)
  have hUold : O (1/16) * (∑ i, volume (Z i)) ≤ ∑ i, volume (U i) := by
    calc
      _ = (1/2 : ENNReal) * ((1/2 : ENNReal) * ((1/2 : ENNReal) *
          ((1/2 : ENNReal) * ∑ i, volume (Z i)))) := by
        change ENNReal.ofReal (1/16) * _ = _
        norm_num [← mul_assoc, ← ENNReal.mul_inv, ENNReal.ofReal_div_of_pos]
      _ ≤ (1/2 : ENNReal) * ((1/2 : ENNReal) * ((1/2 : ENNReal) * ∑ i, volume (Y i))) := by
        gcongr
      _ ≤ (1/2 : ENNReal) * ((1/2 : ENNReal) * ∑ i, volume (E i)) := by gcongr
      _ ≤ (1/2 : ENNReal) * ∑ i, volume (Q i) := by gcongr
      _ ≤ _ := hUmass
  have hUZ (i) : U i ⊆ Z i :=
    (hU i).2.trans ((hQ i).2.1.trans ((hE i).2.trans (hYZ i)))
  obtain ⟨W, hW, hWmass, hWcount⟩ := retain_fibre_incidence_ratio f hZm
    (fun i => (hU i).1) hZfin hUZ (by norm_num : (0:ℝ) ≤ 1/16) hUold
  refine ⟨U, W, fun i => ⟨(hU i).1, (hU i).2.trans ((hQ i).2.1.trans (hE i).2)⟩,
    hW, ?_, hUreg, ?_, ?_⟩
  · intro i p hp
    exact hEend i p ((hQ i).2.1 ((hU i).2 hp))
  · convert hWmass using 1 <;> norm_num
  · intro k p hp
    have hh := hWcount k p hp
    linarith


/-- A logarithmic palette is paid by the gap between two small density powers. -/
theorem prepare_dense_residual_finite {n N J : ℕ} (hJ : 0 < J) {d R lam lam₀ : ℝ}
    (r : Fin J → ℝ) (hd : 0 < d) (hr : ∀ j, 0 < r j) (hr1 : ∀ j, r j ≤ 1)
    (hdr : ∀ j, d ≤ r j/8) (hdR : d ≤ R) (hendpoint : 4608*R ≤ lam₀)
    (hlam : 0 < lam) (hlam₀ : 0 < lam₀) (hpalette : (J:ℝ)*lam ≤ lam₀)
    (x v : Fin n → V) (hv : ∀ i, ‖v i‖ = 1) (f : Fin n → Fin N)
    (Z Y : Fin n → Set V) (hZm : ∀ i, MeasurableSet (Z i))
    (hYm : ∀ i, MeasurableSet (Y i)) (hZT : ∀ i, Z i ⊆ T d (x i) (v i))
    (hYZ : ∀ i, Y i ⊆ Z i)
    (hretain : (1/2 : ENNReal)*(∑ i, volume (Z i)) ≤ ∑ i, volume (Y i))
    (hmin : O (32*lam₀*(n:ℝ)*d^2) ≤ ∑ i, volume (Z i)) :
    ∃ U W : Fin n → Set V,
      (∀ i, MeasurableSet (U i) ∧ U i ⊆ Y i) ∧
      (∀ i, MeasurableSet (W i) ∧ W i ⊆ U i) ∧
      (∀ i p, p ∈ U i → R < dist p (x i) ∧ R < dist p (x i+v i)) ∧
      (∀ i p, p ∈ U i → ∀ j, O (lam*r j*d^2/32) ≤ volume (U i ∩ ball p (r j))) ∧
      O (lam*(n:ℝ)*d^2) ≤ ∑ i, volume (W i) ∧
      ∀ k p, (∃ i, f i = k ∧ p ∈ W i) →
        wz_clustered_cover_volume_gain.fiberBodyCount f Z k p ≤
          32*wz_clustered_cover_volume_gain.fiberBodyCount f W k p := by
  have hJr : (0:ℝ) < J := Nat.cast_pos.mpr hJ
  have hlam_le : lam ≤ lam₀ := by
    have hh : (1:ℝ) ≤ J := by exact_mod_cast hJ
    nlinarith
  have hhalf : ENNReal.ofReal (1/2:ℝ) = (1/2:ENNReal) := by
    norm_num [ENNReal.ofReal_div_of_pos]
  have hYmass : O (16*lam₀*(n:ℝ)*d^2) ≤ ∑ i, volume (Y i) := by
    calc
      _ = (1/2:ENNReal)*O (32*lam₀*(n:ℝ)*d^2) := by
        rw [← hhalf, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
      _ ≤ (1/2:ENNReal)*(∑ i, volume (Z i)) := mul_le_mul_right hmin _
      _ ≤ _ := hretain
  obtain ⟨U, W, hU, hW, hends, hreg, hmass, hcount⟩ := prepare_residual_shading_finite
    hJ r hd hr hr1 hdr hdR hendpoint (by positivity : 0 ≤ lam₀*d^2)
    x v hv f Z Y hZm hYm hZT hYZ hretain
    ((ENNReal.ofReal_le_ofReal (show 4*(n:ℝ)*(lam₀*d^2) ≤ 16*lam₀*(n:ℝ)*d^2 by
      have hp : 0 ≤ lam₀*(n:ℝ)*d^2 := by positivity
      nlinarith)).trans hYmass)
    ((ENNReal.ofReal_le_ofReal (show lam₀*(n:ℝ)*d^2 ≤ 16*lam₀*(n:ℝ)*d^2 by
      have hp : 0 ≤ lam₀*(n:ℝ)*d^2 := by positivity
      nlinarith)).trans hYmass)
  refine ⟨U, W, hU, hW, hends, ?_, ?_, hcount⟩
  · intro i p hp j
    refine (ENNReal.ofReal_le_ofReal ?_).trans (hreg i p hp j)
    apply (le_div_iff₀ (by positivity : (0:ℝ) < 32*J)).mpr
    have hh := mul_le_mul_of_nonneg_right hpalette (mul_nonneg (hr j).le (sq_nonneg d))
    nlinarith
  · calc
      _ ≤ O (lam₀*(n:ℝ)*d^2) := ENNReal.ofReal_le_ofReal (by gcongr)
      _ = O (1/32)*O (32*lam₀*(n:ℝ)*d^2) := by
        rw [← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
      _ ≤ O (1/32)*(∑ i, volume (Z i)) := mul_le_mul_right hmin _
      _ ≤ _ := hmass

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
