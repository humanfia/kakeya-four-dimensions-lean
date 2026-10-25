-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_small_twist_projection_estimate.Slab.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_small_twist_projection_estimate.Geometry
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.SlabVolume

/-!
# Slabs of the fixed coordinate

`Xc c p = p 0 / c + p 1` is the fixed linear coordinate of the argument.  The sets
`slabW c α β ρ` are the unit ball intersected with a slab `|Xc c p - β p₂ - α| ≤ ρ`; they are
convex and have volume at most `8ρ`, so the convex count bounds the number of tubes inside.
-/

namespace WangZahlLot.Obl.wz_small_twist_projection_estimate

open Set Metric MeasureTheory
open scoped ENNReal

/-- The fixed linear coordinate. -/
noncomputable def Xc (c : ℝ) (p : Space) : ℝ := p 0 / c + p 1

lemma Xc_sub (c : ℝ) (p q : Space) : Xc c p - Xc c q = Xc c (p - q) := by
  simp only [Xc, PiLp.sub_apply]
  ring

lemma Xc_add (c : ℝ) (p q : Space) : Xc c (p + q) = Xc c p + Xc c q := by
  simp only [Xc, PiLp.add_apply]
  ring

lemma Xc_smul (c t : ℝ) (p : Space) : Xc c (t • p) = t * Xc c p := by
  simp only [Xc, PiLp.smul_apply, smul_eq_mul]
  ring

lemma abs_Xc_le {c : ℝ} (hc : 100 < |c|) (p : Space) : |Xc c p| ≤ (101 / 100) * ‖p‖ := by
  have h0 := coord_abs_le p 0
  have h1 := coord_abs_le p 1
  have hc0 : 0 < |c| := by linarith
  have hdiv : |p 0 / c| ≤ ‖p‖ / 100 := by
    rw [abs_div, div_le_div_iff₀ hc0 (by norm_num)]
    nlinarith [norm_nonneg p, abs_nonneg (p 0)]
  calc |Xc c p| ≤ |p 0 / c| + |p 1| := abs_add_le _ _
    _ ≤ ‖p‖ / 100 + ‖p‖ := add_le_add hdiv h1
    _ = (101 / 100) * ‖p‖ := by ring

/-- The normal vector of the slab. -/
noncomputable def slabN (c β : ℝ) : Space := WithLp.toLp 2 ![1 / c, 1, -β]

lemma inner_slabN (c β : ℝ) (p : Space) :
    inner ℝ (slabN c β) p = Xc c p - β * p 2 := by
  simp [slabN, Xc, PiLp.inner_apply, Fin.sum_univ_three]
  ring

lemma one_le_norm_slabN (c β : ℝ) : 1 ≤ ‖slabN c β‖ := by
  have h := coord_abs_le (slabN c β) 1
  simpa [slabN] using h

/-- The slab of the counting argument. -/
def slabW (c α β ρ : ℝ) : Set Space :=
  ball (0 : Space) 1 ∩ {p | |Xc c p - β * p 2 - α| ≤ ρ}

lemma convex_slabW (c α β ρ : ℝ) : Convex ℝ (slabW c α β ρ) := by
  apply (convex_ball _ _).inter
  have he : {p : Space | |Xc c p - β * p 2 - α| ≤ ρ} =
      (innerSL ℝ (slabN c β)) ⁻¹' Icc (α - ρ) (α + ρ) := by
    ext p
    simp only [mem_ofPred_eq, mem_preimage, innerSL_apply_apply, inner_slabN, mem_Icc, abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [he]
  exact (convex_Icc _ _).linear_preimage (innerSL ℝ (slabN c β)).toLinearMap

lemma volume_slabW_le {c α β ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume (slabW c α β ρ) ≤ ENNReal.ofReal (8 * ρ) := by
  set N := slabN c β with hNdef
  have hN : 1 ≤ ‖N‖ := one_le_norm_slabN c β
  have hNpos : 0 < ‖N‖ := by linarith
  set ν : Space := ‖N‖⁻¹ • N with hνdef
  have hν : ‖ν‖ = 1 := by
    rw [hνdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hNpos.ne']
  have hsub : slabW c α β ρ ⊆ closedBall (0 : Space) 1 ∩
      WangZahlLot.Obl.wz_regular_transverse_affine_cells.slab (innerSL ℝ ν)
        (α / ‖N‖) (ρ / ‖N‖) := by
    rintro p ⟨hp1, hp2⟩
    refine ⟨ball_subset_closedBall hp1, ?_⟩
    simp only [WangZahlLot.Obl.wz_regular_transverse_affine_cells.slab, mem_ofPred_eq,
      innerSL_apply_apply]
    rw [hνdef, real_inner_smul_left, inner_slabN]
    have hp2' : |Xc c p - β * p 2 - α| ≤ ρ := hp2
    have heq : ‖N‖⁻¹ * (Xc c p - β * p 2) - α / ‖N‖ = (Xc c p - β * p 2 - α) / ‖N‖ := by
      field_simp
    rw [heq, abs_div, abs_of_pos hNpos]
    exact div_le_div_of_nonneg_right hp2' hNpos.le
  calc volume (slabW c α β ρ)
      ≤ volume (closedBall (0 : Space) 1 ∩
          WangZahlLot.Obl.wz_regular_transverse_affine_cells.slab (innerSL ℝ ν)
            (α / ‖N‖) (ρ / ‖N‖)) := measure_mono hsub
    _ ≤ ENNReal.ofReal (8 * (ρ / ‖N‖) * 1 ^ 2) :=
        WangZahlLot.Obl.wz_regular_transverse_affine_cells.volume_ball_inter_slab_le hν _
          (by positivity) zero_le_one
    _ ≤ ENNReal.ofReal (8 * ρ) := by
        apply ENNReal.ofReal_le_ofReal
        rw [one_pow, mul_one]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [div_le_iff₀ hNpos]
        nlinarith

/-- The convex count bounds the number of tubes inside a slab. -/
lemma card_le_of_subset_slabW {η δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    (hF : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (Set.ncard {i | tube δ (x i) (v i) ⊆ W} : ℝ) ≤
        ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume W)
    (hδ : 0 < δ) {c α β ρ : ℝ} (hρ : 0 ≤ ρ) (S : Finset (Fin n))
    (hS : ∀ j ∈ S, tube δ (x j) (v j) ⊆ slabW c α β ρ) :
    (S.card : ℝ) ≤ δ ^ (-η) * n * (8 * ρ) := by
  have hcount := hF _ (convex_slabW c α β ρ)
  have hsub : (S : Set (Fin n)) ⊆ {i | tube δ (x i) (v i) ⊆ slabW c α β ρ} :=
    fun j hj => hS j hj
  have hcard : S.card ≤ Set.ncard {i | tube δ (x i) (v i) ⊆ slabW c α β ρ} := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hvol := volume_slabW_le (c := c) (α := α) (β := β) hρ
  have h1 : ENNReal.ofReal (Set.ncard {i | tube δ (x i) (v i) ⊆ slabW c α β ρ} : ℝ) ≤
      ENNReal.ofReal (δ ^ (-η) * n * (8 * ρ)) := by
    calc _ ≤ ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume (slabW c α β ρ) := hcount
      _ ≤ ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * ENNReal.ofReal (8 * ρ) := by gcongr
      _ = ENNReal.ofReal (δ ^ (-η) * n * (8 * ρ)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
  have h2 : (Set.ncard {i | tube δ (x i) (v i) ⊆ slabW c α β ρ} : ℝ) ≤
      δ ^ (-η) * n * (8 * ρ) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  calc (S.card : ℝ) ≤ (Set.ncard {i | tube δ (x i) (v i) ⊆ slabW c α β ρ} : ℝ) := by
        exact_mod_cast hcard
    _ ≤ δ ^ (-η) * n * (8 * ρ) := h2

end WangZahlLot.Obl.wz_small_twist_projection_estimate
