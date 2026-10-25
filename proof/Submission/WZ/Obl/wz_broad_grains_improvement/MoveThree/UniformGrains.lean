-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.UniformGrains.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/UniformGrains.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0708 commit 170d089, UniformGrains.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NaturalTubes
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoarseNormalize
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.UnitTransport

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis boxAxis_norm inner_boxAxis)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent (uniformMap)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit)

/-- Uniformly normalize a physical block at its original grain length. -/
def blockSimilarity {c : ℝ} (hc : 0 < c) (z₀ : V) : V ≃ᵃ[ℝ] V :=
  (AffineEquiv.constVAdd ℝ V (-z₀)).trans
    (uniformMap (by positivity : 0 < (4*c)⁻¹)).toAffineEquiv

theorem blockSimilarity_apply {c : ℝ} (hc : 0 < c) (z₀ p : V) :
    blockSimilarity hc z₀ p = (4*c)⁻¹ • (p-z₀) := by
  change (4*c)⁻¹ • (-z₀+p) = (4*c)⁻¹ • (p-z₀)
  congr 1
  abel

theorem blockSimilarity_linear {c : ℝ} (hc : 0 < c) (z₀ v : V) :
    (blockSimilarity hc z₀).linear v = (4*c)⁻¹ • v := rfl

theorem blockSimilarity_linear_inv {c : ℝ} (hc : 0 < c) (z₀ v : V) :
    (blockSimilarity hc z₀).linear.symm v = (4*c) • v := by
  apply (blockSimilarity hc z₀).linear.injective
  rw [LinearEquiv.apply_symm_apply, blockSimilarity_linear, smul_smul,
    inv_mul_cancel₀ (by positivity : 4*c ≠ 0), one_smul]

theorem blockSimilarity_direction {c : ℝ} (hc : 0 < c) (z₀ v : V)
    (hv : ‖v‖ = 1) : unit ((blockSimilarity hc z₀).linear v) = v := by
  rw [blockSimilarity_linear,
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.unit_pos_smul (by positivity)]
  simp only [WangZahlLot.Obl.wz_affine_robust_cluster_estimate.unit, hv, inv_one, one_smul]

theorem blockSimilarity_ball {c : ℝ} (hc : 0 < c) (z₀ : V) :
    blockSimilarity hc z₀ '' ball z₀ (4*c) ⊆ ball (0 : V) 1 := by
  rintro _ ⟨p, hp, rfl⟩
  rw [mem_ball, dist_eq_norm] at hp
  rw [mem_ball, dist_zero_right, blockSimilarity_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < (4*c)⁻¹)]
  have hh := mul_lt_mul_of_pos_left hp (by positivity : 0 < (4*c)⁻¹)
  simpa only [inv_mul_cancel₀ (by positivity : 4*c ≠ 0)] using hh

/-- The whole old grain, rather than its shading alone, supplies the short
normal component of its original long axis. -/
theorem contained_prism_normal_bound {a b c A B C : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c)
    (z z' : V) (e g : V ≃ₗᵢ[ℝ] V)
    (hsub : P a b c z e ⊆ P A B C z' g) :
    |inner ℝ (boxAxis g 0) (boxAxis e 2)| ≤ A/c := by
  obtain ⟨hp, hm⟩ := WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_prism_ends
    ha hb hc.le z e
  have hh := (abs_sub _ _).trans (add_le_add (hsub hp).1 (hsub hm).1)
  have he : g (z+(c/2) • boxAxis e 2-z') 0 -
      g (z-(c/2) • boxAxis e 2-z') 0 = c * g (boxAxis e 2) 0 := by
    rw [← PiLp.sub_apply, ← map_sub,
      show (z+(c/2) • boxAxis e 2-z')-(z-(c/2) • boxAxis e 2-z') =
        c • boxAxis e 2 by module, map_smul, PiLp.smul_apply, smul_eq_mul]
  rw [he, abs_mul, abs_of_pos hc] at hh
  rw [inner_boxAxis, le_div_iff₀ hc]
  nlinarith only [hh]

/-- After uniform normalization, every whole old grain has its original unit
axis as the direction of a round tube. -/
theorem uniform_grain_unit_tube {a ρ c : ℝ} (ha : 0 ≤ a) (hρ : 0 < ρ)
    (hc : 0 < c) (hac : a ≤ ρ*c) (z z₀ : V) (e : V ≃ₗᵢ[ℝ] V) :
    blockSimilarity hc z₀ '' P a (ρ*c) c z e ⊆
      T (2*ρ) (blockSimilarity hc z₀ z - (1/2 : ℝ) • boxAxis e 2) (boxAxis e 2) := by
  let f := blockSimilarity hc z₀
  have hnorm (j : Fin 3) : ‖f.linear (boxAxis e j)‖ = (4*c)⁻¹ := by
    rw [blockSimilarity_linear, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < (4*c)⁻¹), boxAxis_norm, mul_one]
  have h0 : a * ‖f.linear (boxAxis e 0)‖ ≤ ρ := by
    rw [hnorm]
    have hh := mul_le_mul_of_nonneg_right hac (by positivity : 0 ≤ (4*c)⁻¹)
    have he : (ρ*c)*(4*c)⁻¹ = ρ/4 := by field_simp
    rw [he] at hh
    linarith
  have h1 : (ρ*c) * ‖f.linear (boxAxis e 1)‖ ≤ ρ := by
    rw [hnorm]
    have he : (ρ*c)*(4*c)⁻¹ = ρ/4 := by field_simp
    rw [he]
    linarith
  have hsub := affine_prism_tube ha (mul_pos hρ hc).le hc hρ z e f h0 h1
  have hvec : c • f.linear (boxAxis e 2) = (1/4 : ℝ) • boxAxis e 2 := by
    rw [blockSimilarity_linear, smul_smul]
    congr 1
    field_simp
  have hmid : f z - (c/2) • f.linear (boxAxis e 2) +
      (1/2 : ℝ) • (c • f.linear (boxAxis e 2)) = f z := by module
  have hh := WangZahlLot.Obl.wz_affine_robust_cluster_estimate.image_tube_extend
    (AffineEquiv.refl ℝ V).toContinuousAffineEquiv
    (f z - (c/2) • f.linear (boxAxis e 2)) (c • f.linear (boxAxis e 2)) (boxAxis e 2)
    (δ := 2*ρ) (l := 1/4) (A := 1) (by norm_num) (by norm_num) (by norm_num)
    (by simpa using hvec) (by intro p q; simp)
  have hcarrier : T (2*ρ) (f z-(c/2) • f.linear (boxAxis e 2))
      (c • f.linear (boxAxis e 2)) ⊆ T (2*ρ) (f z-(1/2 : ℝ) • boxAxis e 2) (boxAxis e 2) := by
    simpa only [AffineEquiv.coe_toContinuousAffineEquiv, AffineEquiv.coe_refl,
      Set.image_id, id_eq, one_mul, hmid, T,
      WangZahlLot.Obl.wz_affine_robust_cluster_estimate.tube] using hh
  exact hsub.trans hcarrier

/-- The short physical enclosure gives exactly the slab and normal bounds
required by the packet prism construction after uniform normalization. -/
theorem uniform_grain_slab {a ρ c A B C : ℝ} (ha : 0 ≤ a) (hρ : 0 ≤ ρ)
    (hc : 0 < c) (z z₀ z' : V) (e g : V ≃ₗᵢ[ℝ] V)
    (hsub : P a (ρ*c) c z e ⊆ P A B C z' g) :
    blockSimilarity hc z₀ '' P a (ρ*c) c z e ⊆
      {p | |inner ℝ (boxAxis g 0) p -
        inner ℝ (boxAxis g 0) (blockSimilarity hc z₀ z')| ≤ (A/(4*c))/2} ∧
    |inner ℝ (boxAxis g 0) (boxAxis e 2)| ≤ 4*(A/(4*c)) := by
  constructor
  · rintro _ ⟨p, hp, rfl⟩
    have he : blockSimilarity hc z₀ p - blockSimilarity hc z₀ z' = (4*c)⁻¹ • (p-z') := by
      rw [blockSimilarity_apply, blockSimilarity_apply, ← smul_sub]
      congr 1
      abel
    change |inner ℝ (boxAxis g 0) (blockSimilarity hc z₀ p) -
      inner ℝ (boxAxis g 0) (blockSimilarity hc z₀ z')| ≤ _
    rw [← inner_sub_right, he, inner_smul_right, inner_boxAxis, abs_mul,
      abs_of_pos (by positivity : 0 < (4*c)⁻¹)]
    calc
      _ ≤ (4*c)⁻¹*(A/2) :=
        mul_le_mul_of_nonneg_left (hsub hp).1 (by positivity)
      _ = _ := by ring
  · have hh := contained_prism_normal_bound ha (mul_nonneg hρ hc.le) hc z z' e g hsub
    convert hh using 1
    field_simp

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
