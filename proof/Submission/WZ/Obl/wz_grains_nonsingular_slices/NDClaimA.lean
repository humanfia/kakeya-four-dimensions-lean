-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_grains_nonsingular_slices.NDClaimA.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_grains_nonsingular_slices.Defs

/-!
# Nondegeneracy, step 3: the local plane contains the grain direction

At a point `ofTwist f u y0 z` of a grain that is locally full at scale `ℓ`, a unit vector `P`
whose projection of `E` near the point is a `(ℓ^2, 1-σ)`-AD set is almost orthogonal to the grain
direction `(-f z, 1, 0)`: `|P 1 - P 0 * f z| ≤ 1/4`.
-/

namespace WangZahlLot.Obl.wz_grains_nonsingular_slices

open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_separated_cover_refinement
open scoped ENNReal

/-- The inner product of `P` with a point of a grain is affine in the grain parameter. -/
private lemma ndca_inner_ofTwist (f : ℝ → ℝ) (P : Space) (u y z : ℝ) :
    inner ℝ P (ofTwist f u y z) = P 0 * u + P 2 * z + (P 1 - P 0 * f z) * y := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, ofTwist]
  ring

/-- Points of a grain within `ℓ / 2` of `y0` lie in the open `ℓ`-ball around the grain point
at `y0`, as long as the grain slope satisfies `|f z| ≤ 1`. -/
private lemma ndca_ofTwist_mem_ball {f : ℝ → ℝ} {u y y0 z ℓ : ℝ} (hℓ : 0 < ℓ)
    (hfz : |f z| ≤ 1) (hy : |y - y0| ≤ ℓ / 2) :
    ofTwist f u y z ∈ ball (ofTwist f u y0 z) ℓ := by
  rw [mem_ball, EuclideanSpace.dist_eq, Real.sqrt_lt' hℓ]
  simp [Fin.sum_univ_three, Real.dist_eq, sq_abs]
  have hf2 : f z ^ 2 ≤ 1 := by nlinarith [abs_nonneg (f z), sq_abs (f z)]
  have hy2 : (y - y0) ^ 2 ≤ (ℓ / 2) ^ 2 := by
    nlinarith [abs_nonneg (y - y0), sq_abs (y - y0)]
  nlinarith [sq_nonneg (y - y0)]

theorem nd_claimA {σ η δ ℓ κ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (hη : 0 < η) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hℓ : 0 < ℓ) (hδℓ : δ ≤ ℓ ^ 2) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hℓsmall : 2 * δ ^ (-η) * ℓ ^ σ ≤ κ * (1 / 4) ^ σ)
    {E : Set Space} {f : ℝ → ℝ} {u y0 z : ℝ} (hfz : |f z| ≤ 1) {P : Space} (hP : ‖P‖ = 1)
    (hLG : AD (ℓ ^ 2) (1 - σ) (δ ^ (-η))
      ((fun q : Space => inner ℝ P q) '' (E ∩ ball (ofTwist f u y0 z) ℓ)))
    (hfull : LocFull (grainFib f E u z) ℓ κ y0) :
    |P 1 - P 0 * f z| ≤ 1 / 4 := by
  set s : ℝ := P 1 - P 0 * f z with hs_def
  set c0 : ℝ := P 0 * u + P 2 * z with hc0_def
  set D : ℝ := δ ^ (-η) with hD_def
  have hD1 : 1 ≤ D := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hℓσ : 0 < ℓ ^ σ := Real.rpow_pos_of_pos hℓ σ
  have hq : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ σ := by positivity
  -- the scale `ℓ` is below `1/4`
  have hℓlt : ℓ < 1 / 4 := by
    have h1 : ℓ ^ σ < (1 / 4 : ℝ) ^ σ := by
      have h2 : 2 * ℓ ^ σ ≤ κ * (1 / 4 : ℝ) ^ σ := by
        calc 2 * ℓ ^ σ ≤ 2 * D * ℓ ^ σ := by nlinarith
          _ ≤ _ := hℓsmall
      have h3 : κ * (1 / 4 : ℝ) ^ σ ≤ (1 / 4 : ℝ) ^ σ := mul_le_of_le_one_left hq hκ1
      linarith
    exact (Real.rpow_lt_rpow_iff hℓ.le (by norm_num) hσ).mp h1
  by_cases hsℓ : |s| < ℓ
  · linarith
  rw [not_lt] at hsℓ
  have hs0 : 0 < |s| := hℓ.trans_le hsℓ
  set r : ℝ := ℓ ^ 2 with hr_def
  set R : ℝ := |s| * ℓ with hR_def
  have hr0 : 0 < r := by positivity
  have hrR : r ≤ R := by
    rw [hr_def, hR_def, sq]
    exact mul_le_mul_of_nonneg_right hsℓ hℓ.le
  obtain ⟨m, c, hc, hm⟩ := hLG r R (c0 + s * y0 - |s| * ℓ / 2) le_rfl hrR
  -- the fibre near `y0` maps into the covered part of the projection
  have hsub : grainFib f E u z ∩ Icc (y0 - ℓ / 2) (y0 + ℓ / 2) ⊆
      (fun y => s * y) ⁻¹' ((fun h => c0 + h) ⁻¹' ⋃ j, closedBall (c j) r) := by
    rintro y ⟨hyE, hyI⟩
    have hy : |y - y0| ≤ ℓ / 2 := abs_le.mpr ⟨by linarith [hyI.1], by linarith [hyI.2]⟩
    apply hc
    refine ⟨⟨ofTwist f u y z, ⟨hyE, ndca_ofTwist_mem_ball hℓ hfz hy⟩,
      ndca_inner_ofTwist f P u y z⟩, ?_⟩
    have h1 : |s * (y - y0)| ≤ |s| * ℓ / 2 := by
      rw [abs_mul]
      nlinarith [abs_nonneg s]
    obtain ⟨h2, h3⟩ := abs_le.mp h1
    constructor <;> nlinarith
  have hU : volume (⋃ j, closedBall (c j) r) ≤ ENNReal.ofReal (2 * r * (m : ℝ)) := by
    calc volume (⋃ j, closedBall (c j) r) ≤ ∑ j, volume (closedBall (c j) r) :=
          measure_iUnion_fintype_le volume _
      _ = ENNReal.ofReal (2 * r * (m : ℝ)) := by
        simp only [Real.volume_closedBall, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        rw [mul_comm, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  have hvol : ENNReal.ofReal (κ * ℓ) ≤ ENNReal.ofReal (|s|⁻¹ * (2 * r * (m : ℝ))) := by
    calc ENNReal.ofReal (κ * ℓ)
        ≤ volume (grainFib f E u z ∩ Icc (y0 - ℓ / 2) (y0 + ℓ / 2)) := hfull
      _ ≤ volume ((fun y => s * y) ⁻¹' ((fun h => c0 + h) ⁻¹' ⋃ j, closedBall (c j) r)) :=
          measure_mono hsub
      _ = ENNReal.ofReal |s⁻¹| * volume (⋃ j, closedBall (c j) r) := by
        rw [Real.volume_preimage_mul_left (abs_pos.mp hs0), measure_preimage_add]
      _ ≤ ENNReal.ofReal |s⁻¹| * ENNReal.ofReal (2 * r * (m : ℝ)) := by gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_inv]
  have hreal : κ * ℓ ≤ |s|⁻¹ * (2 * r * (m : ℝ)) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hvol
  have h2 : |s| * (κ * ℓ) ≤ 2 * r * (D * (R / r) ^ (1 - σ)) :=
    ((le_inv_mul_iff₀ hs0).mp hreal).trans (mul_le_mul_of_nonneg_left hm (by positivity))
  -- solving the power inequality
  have hRr : R / r = |s| / ℓ := by
    rw [hR_def, hr_def]
    field_simp
  have hA : 0 < |s| ^ σ := Real.rpow_pos_of_pos hs0 σ
  have hpow : (R / r) ^ (1 - σ) = (|s| / ℓ) * ℓ ^ σ / |s| ^ σ := by
    rw [hRr, Real.rpow_sub (by positivity), Real.rpow_one,
      Real.div_rpow hs0.le hℓ.le]
    field_simp
  rw [hpow] at h2
  have h3 : (κ * |s| ^ σ) * (|s| * ℓ) ≤ (2 * D * ℓ ^ σ) * (|s| * ℓ) := by
    have h4 : 2 * r * (D * (|s| / ℓ * ℓ ^ σ / |s| ^ σ)) =
        (2 * D * ℓ ^ σ) * (|s| * ℓ) / |s| ^ σ := by
      rw [hr_def]
      field_simp
    rw [h4, le_div_iff₀ hA] at h2
    linarith
  have h5 : κ * |s| ^ σ ≤ 2 * D * ℓ ^ σ :=
    le_of_mul_le_mul_right h3 (by positivity)
  have h6 : |s| ^ σ ≤ (1 / 4 : ℝ) ^ σ :=
    le_of_mul_le_mul_left (h5.trans hℓsmall) hκ
  exact (Real.rpow_le_rpow_iff (abs_nonneg _) (by norm_num) hσ).mp h6

end WangZahlLot.Obl.wz_grains_nonsingular_slices
