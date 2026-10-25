-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.CarrierLinear.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/CarrierLinear.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0708 commit 170d089, CarrierLinear.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.UniformGrains
import Submission.WZ.Obl.wz_flat_factored_improvement.Diagonal

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (boxAxis boxAxis_norm norm_le_coord_sum unit_sub_norm_le unit_pos_smul)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit)
open WangZahlLot.Obl.wz_flat_factored_improvement
  (diagonalMap diagonalMap_apply diagonalMap_norm_lower)

/-- Whole-prism containment controls the normal displacement along each of
its three axes, weighted by the corresponding side length. -/
theorem contained_prism_axis_extent {a b c A B C : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (z z' : V) (e g : V ≃ₗᵢ[ℝ] V)
    (hsub : P a b c z e ⊆ P A B C z' g) (j : Fin 3) :
    (![a,b,c] : Fin 3 → ℝ) j * |g (boxAxis e j) 0| ≤ A := by
  let d : Fin 3 → ℝ := ![a,b,c]
  have hd (i : Fin 3) : 0 ≤ d i := by fin_cases i <;> assumption
  have hmem (t : ℝ) (ht : |t| ≤ d j/2) : z+t • boxAxis e j ∈ P a b c z e := by
    have he : e (z+t • boxAxis e j-z) = t • EuclideanSpace.basisFun (Fin 3) ℝ j := by
      simp only [add_sub_cancel_left, map_smul, boxAxis, e.apply_symm_apply]
    change |e (z+t • boxAxis e j-z) 0| ≤ a/2 ∧
      |e (z+t • boxAxis e j-z) 1| ≤ b/2 ∧ |e (z+t • boxAxis e j-z) 2| ≤ c/2
    rw [he]
    fin_cases j <;> simp_all [d, EuclideanSpace.basisFun_apply] <;> constructor <;> positivity
  have hp := (hsub (hmem (d j/2) (by rw [abs_of_nonneg (div_nonneg (hd j) (by norm_num))]))).1
  have hm := (hsub (hmem (-(d j/2)) (by rw [abs_neg, abs_of_nonneg (div_nonneg (hd j) (by norm_num))]))).1
  have he : g (z+(d j/2) • boxAxis e j-z') 0 -
      g (z+(-(d j/2)) • boxAxis e j-z') 0 = d j * g (boxAxis e j) 0 := by
    rw [← PiLp.sub_apply, ← map_sub,
      show (z+(d j/2) • boxAxis e j-z')-(z+(-(d j/2)) • boxAxis e j-z') =
        d j • boxAxis e j by module, map_smul, PiLp.smul_apply, smul_eq_mul]
  have hh := (abs_sub _ _).trans (add_le_add hp hm)
  rw [he, abs_mul, abs_of_nonneg (hd j)] at hh
  change d j * |g (boxAxis e j) 0| ≤ A
  linarith only [hh]

/-- Stretch just the short direction of a capped physical carrier. Its
inverse is uniformly bounded if the target radius exceeds `A/c`. -/
theorem carrier_linear_inverse {A c r : ℝ} (hA : 0 < A) (hc : 0 < c)
    (hAc : A ≤ r*c) (g : V ≃ₗᵢ[ℝ] V) (L : V ≃ₗ[ℝ] V)
    (hcoord : ∀ v i, L v i = (![r/(4*A),(4*c)⁻¹,(4*c)⁻¹] : Fin 3 → ℝ) i * g v i) :
    ∀ v, ‖L.symm v‖ ≤ (4*c)*‖v‖ := by
  have he (v : V) : L v = diagonalMap ![r/(4*A),(4*c)⁻¹,(4*c)⁻¹] (g v) := by
    ext i
    exact hcoord v i
  have hs (i : Fin 3) : (4*c)⁻¹ ≤
      |(![r/(4*A),(4*c)⁻¹,(4*c)⁻¹] : Fin 3 → ℝ) i| := by
    have hr : 0 < r := (mul_pos_iff_of_pos_right hc).mp (hA.trans_le hAc)
    fin_cases i
    · change (4*c)⁻¹ ≤ |r/(4*A)|
      rw [abs_of_pos (by positivity : 0 < r/(4*A))]
      apply (le_div_iff₀ (by positivity : 0 < 4*A)).mpr
      have h := (div_le_iff₀ hc).mpr hAc
      convert h using 1 <;> field_simp
    · change (4*c)⁻¹ ≤ |(4*c)⁻¹|
      rw [abs_of_pos (by positivity : 0 < (4*c)⁻¹)]
    · change (4*c)⁻¹ ≤ |(4*c)⁻¹|
      rw [abs_of_pos (by positivity : 0 < (4*c)⁻¹)]
  intro v
  have hh := diagonalMap_norm_lower (by positivity : 0 ≤ (4*c)⁻¹) hs (g (L.symm v))
  rw [← he, L.apply_symm_apply, g.norm_map] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 4*c)
  simpa only [← mul_assoc, mul_inv_cancel₀ (by positivity : 4*c ≠ 0), one_mul] using hh'

/-- Whole containment makes the anisotropic image of each old grain round,
including when its short face is tilted relative to the enclosing slab. -/
theorem carrier_grain_linear_bounds {a ρ c A B C r : ℝ}
    (ha : 0 ≤ a) (hρ : 0 < ρ) (hc : 0 < c) (hac : a ≤ ρ*c)
    (hA : 0 < A) (hρr : ρ ≤ r) (hr1 : r ≤ 1)
    (z z' : V) (e g : V ≃ₗᵢ[ℝ] V) (L : V ≃ₗ[ℝ] V)
    (hsub : P a (ρ*c) c z e ⊆ P A B C z' g)
    (hcoord : ∀ v i, L v i = (![r/(4*A),(4*c)⁻¹,(4*c)⁻¹] : Fin 3 → ℝ) i * g v i) :
    a*‖L (boxAxis e 0)‖ ≤ r ∧ (ρ*c)*‖L (boxAxis e 1)‖ ≤ r ∧
      ‖L (boxAxis e 2)‖ ≤ c⁻¹ := by
  have hr : 0 < r := hρ.trans_le hρr
  let d : Fin 3 → ℝ := ![a,ρ*c,c]
  have hd (j : Fin 3) : 0 ≤ d j := by fin_cases j <;> dsimp [d] <;> positivity
  have hnormal (j : Fin 3) : d j * |g (boxAxis e j) 0| ≤ A :=
    contained_prism_axis_extent ha (mul_pos hρ hc).le hc.le z z' e g hsub j
  have hunit (j i : Fin 3) : |g (boxAxis e j) i| ≤ 1 := by
    simpa only [Real.norm_eq_abs, g.norm_map, boxAxis_norm] using
      PiLp.norm_apply_le (g (boxAxis e j)) i
  have h0 (j : Fin 3) : d j * |L (boxAxis e j) 0| ≤ r/4 := by
    rw [hcoord]
    change d j * |r/(4*A)*g (boxAxis e j) 0| ≤ r/4
    rw [abs_mul, abs_of_pos (by positivity : 0 < r/(4*A))]
    calc
      _ = (r/(4*A))*(d j*|g (boxAxis e j) 0|) := by ring
      _ ≤ (r/(4*A))*A := mul_le_mul_of_nonneg_left (hnormal j) (by positivity)
      _ = r/4 := by field_simp
  have hrest (j i : Fin 3) (hi : i ≠ 0) : |L (boxAxis e j) i| ≤ (4*c)⁻¹ := by
    rw [hcoord]
    have hs : (![r/(4*A),(4*c)⁻¹,(4*c)⁻¹] : Fin 3 → ℝ) i = (4*c)⁻¹ := by
      fin_cases i <;> simp_all
    rw [hs, abs_mul, abs_of_pos (by positivity : 0 < (4*c)⁻¹)]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hunit j i) (by positivity : 0 ≤ (4*c)⁻¹)
  have hn (j : Fin 3) : d j * ‖L (boxAxis e j)‖ ≤ r/4 + d j/(2*c) := by
    have hh := mul_le_mul_of_nonneg_left (norm_le_coord_sum (L (boxAxis e j))) (hd j)
    have hh1 := mul_le_mul_of_nonneg_left (hrest j 1 (by decide)) (hd j)
    have hh2 := mul_le_mul_of_nonneg_left (hrest j 2 (by decide)) (hd j)
    have he : d j * (4*c)⁻¹ + d j * (4*c)⁻¹ = d j/(2*c) := by ring
    nlinarith [h0 j]
  have hn0 := hn 0
  have hn1 := hn 1
  have hn2 := hn 2
  change a*‖L (boxAxis e 0)‖ ≤ r/4+a/(2*c) at hn0
  change (ρ*c)*‖L (boxAxis e 1)‖ ≤ r/4+(ρ*c)/(2*c) at hn1
  change c*‖L (boxAxis e 2)‖ ≤ r/4+c/(2*c) at hn2
  have hcfrac : c/(2*c) = (1/2 : ℝ) := by field_simp
  have hρfrac : (ρ*c)/(2*c) = ρ/2 := by field_simp
  have haρ : a/(2*c) ≤ ρ/2 := by apply (div_le_iff₀ (by positivity : 0 < 2*c)).mpr; nlinarith
  rw [hcfrac] at hn2
  rw [hρfrac] at hn1
  refine ⟨by linarith, by linarith, ?_⟩
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hc).mpr
  nlinarith only [hn2, hr1]

/-- On the old long directions, the re-normalization changes projective
directions by only `2r`, despite its potentially large operator norm. -/
theorem carrier_unit_direction_error {A c r : ℝ}
    (hA : 0 < A) (hc : 0 < c) (hAc : A ≤ r*c)
    (g : V ≃ₗᵢ[ℝ] V) (L : V ≃ₗ[ℝ] V)
    (hcoord : ∀ v i, L v i = (![r/(4*A),(4*c)⁻¹,(4*c)⁻¹] : Fin 3 → ℝ) i * g v i)
    {v : V} (hv : ‖v‖ = 1) (hsmall : |g v 0| ≤ A/c) :
    ‖unit (L v) - g v‖ ≤ 2*r := by
  have hv0 : v ≠ 0 := by intro h; simp only [h, norm_zero] at hv; norm_num at hv
  have hLv : L v ≠ 0 := fun h => hv0 (L.injective (h.trans (map_zero L).symm))
  have hgv : g v ≠ 0 := fun h => hv0 (g.injective (h.trans (map_zero g).symm))
  have hcoef : 0 ≤ r*c/A-1 := by
    have hh : 1 ≤ r*c/A := (le_div_iff₀ hA).mpr (by simpa using hAc)
    linarith
  have he : (4*c) • L v - g v = ((r*c/A-1)*g v 0) •
      EuclideanSpace.basisFun (Fin 3) ℝ 0 := by
    ext i
    rw [PiLp.sub_apply, PiLp.smul_apply, hcoord]
    fin_cases i <;> simp [EuclideanSpace.basisFun_apply] <;> field_simp <;> ring
  have herror : ‖(4*c) • L v - g v‖ ≤ r := by
    rw [he, norm_smul, Real.norm_eq_abs]
    have hnorm : ‖(EuclideanSpace.basisFun (Fin 3) ℝ 0 : V)‖ = 1 := by simp
    rw [hnorm, mul_one, abs_mul, abs_of_nonneg hcoef]
    calc
      _ ≤ (r*c/A-1)*(A/c) := mul_le_mul_of_nonneg_left hsmall hcoef
      _ = r-A/c := by field_simp
      _ ≤ r := sub_le_self _ (by positivity)
  have hh := unit_sub_norm_le hgv
    (smul_ne_zero (by positivity : 4*c ≠ 0) hLv)
  rw [unit_pos_smul (by positivity : 0 < 4*c), g.norm_map, hv, div_one,
    show unit (g v) = g v by
      simp only [WangZahlLot.Obl.wz_affine_robust_cluster_estimate.unit, g.norm_map, hv,
        inv_one, one_smul], norm_sub_rev (g v)] at hh
  rw [norm_sub_rev (g v)] at hh
  exact hh.trans (by nlinarith only [herror])

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
