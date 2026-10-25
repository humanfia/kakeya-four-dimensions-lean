-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_refined_induction_on_scales.LocalScale.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_refined_induction_on_scales.FiniteScales
import Submission.WZ.Obl.wz_direction_density_transfer.Geometry

namespace WangZahlLot.Obl.wz_refined_induction_on_scales

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- A uniform upper volume bound for every capsule of unit segment length. -/
theorem tube_volume_upper {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (x v : Space) (hv : ‖v‖ = 1) :
    volume (Tube ρ x v) ≤ ENNReal.ofReal (384 * ρ ^ 2) := by
  have hdiam : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, dist s t ≤ 1 := by
    intro s hs t ht
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hu := wz_direction_density_transfer.segment_piece_volume_upper x v hv
    (T := Set.Icc 0 1) Set.Subset.rfl hρ (by norm_num : (0 : ℝ) ≤ 1) hdiam
  have hsegment : (fun t : ℝ => x + t • v) '' Set.Icc 0 1 = segment ℝ x (x + v) := by
    rw [segment_eq_image']
    simp
  rw [hsegment] at hu
  exact hu.trans (ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg ρ]))

/-- The convex-count hypothesis also controls the cardinality inside a covering capsule. -/
theorem count_bound_in_tube {δ ρ m : ℝ} {n : ℕ} {x v : Fin n → Space}
    (hK : Katz δ m x v) (_hδ : 0 < δ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hm : 0 ≤ m) {y w : Space} (hw : ‖w‖ = 1)
    (hcover : ∀ i, Tube δ (x i) (v i) ⊆ Tube ρ y w) :
    (n : ℝ) * δ ^ 2 ≤ m * (384 * ρ ^ 2) := by
  have hk := hK (Tube ρ y w) ((convex_segment y (y + w)).thickening ρ)
  have hset : {i : Fin n | Tube δ (x i) (v i) ⊆ Tube ρ y w} = Set.univ :=
    Set.eq_univ_of_forall hcover
  change ENNReal.ofReal (({i : Fin n | Tube δ (x i) (v i) ⊆ Tube ρ y w}.ncard : ℝ) *
    δ ^ 2) ≤ ENNReal.ofReal m * volume (Tube ρ y w) at hk
  rw [hset] at hk
  simp only [Set.ncard_univ, Nat.card_fin] at hk
  have hbound := hk.trans (mul_le_mul_right (tube_volume_upper hρ hρ1 y w hw) _)
  rw [← ENNReal.ofReal_mul hm] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbound

/-- The close-scale part of the rescaled E estimate needs only density and the
convex count; the inequality on exponents accounts for all its losses. -/
theorem local_estimate_of_close_scales {δ ρ σ ω η ε θ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ1 : ρ ≤ 1)
    (hσ : 0 ≤ σ) (hω : 0 ≤ ω)
    (hscale : δ ^ θ ≤ δ / ρ) (hbudget : 2 * η + θ * (2 + σ) ≤ ε)
    {n : ℕ} (hn : 0 < n) {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hdense : Dense δ η Y) (hK : Katz δ (δ ^ (-η)) x v)
    {y w : Space} (hw : ‖w‖ = 1)
    (hcover : ∀ i, Tube δ (x i) (v i) ⊆ Tube ρ y w) :
    ENNReal.ofReal ((1 / 384 : ℝ) * δ ^ ε * (δ / ρ) ^ ω * (n * δ ^ 2) *
      (n * (δ / ρ)) ^ (-σ)) ≤ volume (⋃ i, Y i) := by
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hδ1 : δ ≤ 1 := hδρ.trans hρ1
  let s := δ / ρ
  have hs : 0 < s := div_pos hδ hρ
  have hs1 : s ≤ 1 := (div_le_one hρ).mpr hδρ
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hc := count_bound_in_tube hK hδ hρ hρ1 (Real.rpow_nonneg hδ.le _) hw hcover
  have hωbound : s ^ ω ≤ 1 := Real.rpow_le_one hs.le hs1 hω
  have hσbound : ((n : ℝ) * s) ^ (-σ) ≤ s ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos hs (by nlinarith) (neg_nonpos.mpr hσ)
  have hscale_bound : s ^ (-(2 + σ)) ≤ δ ^ (-θ * (2 + σ)) := by
    have h := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hδ θ) hscale
      (by linarith : -(2 + σ) ≤ 0)
    rw [← Real.rpow_mul hδ.le] at h
    rwa [show θ * -(2 + σ) = -θ * (2 + σ) by ring] at h
  have hshape : ρ ^ 2 * s ^ (-σ) = δ ^ 2 * s ^ (-(2 + σ)) := by
    have heq : δ = ρ * s := by dsimp [s]; field_simp
    rw [heq, mul_pow, show -(2 + σ) = (-2 : ℝ) + (-σ) by ring,
      Real.rpow_add hs, Real.rpow_neg hs.le (2 : ℝ), Real.rpow_two]
    field_simp
  have hcoef :
      (1 / 384 : ℝ) * δ ^ ε * s ^ ω * (n * δ ^ 2) * (n * s) ^ (-σ) ≤
      δ ^ η * δ ^ 2 := by
    calc
      _ ≤ (1 / 384 : ℝ) * δ ^ ε * 1 *
          (δ ^ (-η) * (384 * ρ ^ 2)) * s ^ (-σ) := by
        apply mul_le_mul
        · exact mul_le_mul
            (mul_le_mul_of_nonneg_left hωbound (by positivity)) hc
            (by positivity) (by positivity)
        · exact hσbound
        · positivity
        · positivity
      _ = (δ ^ ε * δ ^ (-η)) * (ρ ^ 2 * s ^ (-σ)) := by ring
      _ = (δ ^ ε * δ ^ (-η)) * δ ^ 2 * s ^ (-(2 + σ)) := by rw [hshape]; ring
      _ ≤ (δ ^ ε * δ ^ (-η)) * δ ^ 2 * δ ^ (-θ * (2 + σ)) :=
        mul_le_mul_of_nonneg_left hscale_bound (by positivity)
      _ = δ ^ (ε - η - θ * (2 + σ)) * δ ^ 2 := by
        rw [show ε - η - θ * (2 + σ) = (ε + -η) + (-θ * (2 + σ)) by ring,
          Real.rpow_add hδ, Real.rpow_add hδ]
        ring
      _ ≤ δ ^ η * δ ^ 2 := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)) (sq_nonneg δ)
  exact (ENNReal.ofReal_le_ofReal hcoef).trans (average_bound_of_dense hn hdense)

end WangZahlLot.Obl.wz_refined_induction_on_scales
