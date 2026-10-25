-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_grains_nonsingular_slices.Nondegenerate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_grains_nonsingular_slices.NDCount
import Submission.WZ.Obl.wz_grains_nonsingular_slices.NDAnchor
import Submission.WZ.Obl.wz_grains_nonsingular_slices.NDClaimA
import Submission.WZ.Obl.wz_grains_nonsingular_slices.Projection

/-!
# Nondegeneracy of the slope (Assouad Lemma 6.6)

If the slope `f` is almost constant on a slab `J = [z1, z1 + L]` (Lipschitz constant `2L`), then
transversal tubes cannot carry a fair share of shading mass on full grains inside `J`.

Proof outline (`nondegenerate`):
1. `nd_count` gives a prism `{|twist f q - c| ≤ 4L/θ}` containing `≳ L^(1-σ) n` dense tubes `G`.
2. At the scale `ℓ = (lam δ^η / 40)^(1/σ) / 4` (`nd_ell`), `nd_anchor` gives a plane `{q 1 = y0}`
   anchoring a fixed fraction of the mass; the tubes `G4` keeping a fair anchored mass are
   many (`nd_card_G4`).
3. At an anchor point `p_S`, `nd_claimA` shows that the plane normal `P = P p_S` almost contains
   the grain direction, so `V = (P 0, P 0 * f zS, P 2)` has `1/2 ≤ ‖V‖ ≤ 2` (`nd_norm_vec`).
4. The projections `inner V` of the anchored parts are, up to `4 L²`, translates of the
   projection of `E` near `p_S`, hence AD (`nd_ad_affine`); Lemma 6.2
   (`projection_almost_orthogonal`, via `nd_angle`) makes every tube of `G4` almost orthogonal
   to `V`, so all of them lie in one thin slab (`nd_core`).
5. The global convex count of that slab (`nd_slab_volume_le`) contradicts the lower count
   (`nd_final`).
-/

namespace WangZahlLot.Obl.wz_grains_nonsingular_slices

open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_separated_cover_refinement
open scoped ENNReal

/-- Scaling by `s > 0`, translating by `K0` and closed `t`-thickening an AD set. -/
lemma nd_ad_affine {d α C s t K0 : ℝ} {S : Set ℝ} (hS : AD d α C S) (hd : 0 < d)
    (hs : 0 < s) (ht : 0 ≤ t) (htd : t ≤ d) (hC : 0 ≤ C) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    AD (s * d) α (6 * C) {y | ∃ b ∈ S, |y - s * (b - K0)| ≤ s * t} := by
  intro r R a hdr hrR
  have hr : 0 < r := lt_of_lt_of_le (mul_pos hs hd) hdr
  have hR : 0 < R := hr.trans_le hrR
  have hst : s * t ≤ r := (mul_le_mul_of_nonneg_left htd hs.le).trans hdr
  have hdr' : d ≤ r / s := (le_div_iff₀ hs).mpr (by linarith [mul_comm s d])
  have hrR' : r / s ≤ R / s + 2 * t := by
    have : r / s ≤ R / s := div_le_div_of_nonneg_right hrR hs.le
    linarith
  obtain ⟨m, c, hcov, hm⟩ := hS (r / s) (R / s + 2 * t) (a / s + K0 - t) hdr' hrR'
  refine ⟨m + m, Fin.append (fun j => s * (c j - K0) - r) (fun j => s * (c j - K0) + r),
    ?_, ?_⟩
  · rintro y ⟨⟨b, hb, hyb⟩, hya, hyR⟩
    obtain ⟨hyb1, hyb2⟩ := abs_le.mp hyb
    have hb' : b ∈ S ∩ Icc (a / s + K0 - t) (a / s + K0 - t + (R / s + 2 * t)) := by
      refine ⟨hb, ?_, ?_⟩
      · have h1 : a / s ≤ b - K0 + t := by
          rw [div_le_iff₀ hs]
          nlinarith
        linarith
      · have h1 : b - K0 - t ≤ (a + R) / s := by
          rw [le_div_iff₀ hs]
          nlinarith
        have h2 : (a + R) / s = a / s + R / s := add_div a R s
        linarith
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcov hb')
    rw [mem_closedBall, Real.dist_eq] at hj
    have hsj : s * |b - c j| ≤ r := by
      have := mul_le_mul_of_nonneg_left hj hs.le
      rwa [mul_div_cancel₀ _ hs.ne'] at this
    have h1 : |y - s * (c j - K0)| ≤ 2 * r := by
      have he : y - s * (c j - K0) = (y - s * (b - K0)) + s * (b - c j) := by ring
      rw [he]
      calc |(y - s * (b - K0)) + s * (b - c j)|
          ≤ |y - s * (b - K0)| + |s * (b - c j)| := abs_add_le _ _
        _ = |y - s * (b - K0)| + s * |b - c j| := by rw [abs_mul, abs_of_pos hs]
        _ ≤ s * t + r := add_le_add hyb hsj
        _ ≤ 2 * r := by linarith
    obtain ⟨h11, h12⟩ := abs_le.mp h1
    rcases le_total y (s * (c j - K0)) with hle | hle
    · refine mem_iUnion.mpr ⟨Fin.castAdd m j, ?_⟩
      rw [Fin.append_left, mem_closedBall, Real.dist_eq, abs_le]
      constructor <;> linarith
    · refine mem_iUnion.mpr ⟨Fin.natAdd m j, ?_⟩
      rw [Fin.append_right, mem_closedBall, Real.dist_eq, abs_le]
      constructor <;> linarith
  · have hX : (R / s + 2 * t) / (r / s) ≤ 3 * (R / r) := by
      rw [div_le_iff₀ (div_pos hr hs)]
      have e1 : 3 * (R / r) * (r / s) = 3 * R / s := by field_simp
      rw [e1]
      have e2 : 3 * R / s = R / s + 2 * (R / s) := by ring
      rw [e2]
      have : t ≤ R / s := by
        rw [le_div_iff₀ hs]
        nlinarith
      linarith
    have hX0 : 0 ≤ (R / s + 2 * t) / (r / s) := by positivity
    have hpow : ((R / s + 2 * t) / (r / s)) ^ α ≤ 3 * (R / r) ^ α := by
      calc ((R / s + 2 * t) / (r / s)) ^ α ≤ (3 * (R / r)) ^ α :=
            Real.rpow_le_rpow hX0 hX hα0
        _ = 3 ^ α * (R / r) ^ α := Real.mul_rpow (by norm_num) (by positivity)
        _ ≤ 3 * (R / r) ^ α := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            calc (3 : ℝ) ^ α ≤ 3 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
              _ = 3 := Real.rpow_one 3
    have hm' : (m : ℝ) ≤ C * (3 * (R / r) ^ α) :=
      hm.trans (mul_le_mul_of_nonneg_left hpow hC)
    push_cast
    linarith

/-- A slab of half-width `r` inside the unit ball has volume at most `8 r`. -/
lemma nd_slab_volume_le {u : Space} (hu : ‖u‖ = 1) (t r : ℝ) (hr : 0 ≤ r) :
    volume (ball (0 : Space) 1 ∩ {p | |inner ℝ u p - t| ≤ r}) ≤ ENNReal.ofReal (8 * r) := by
  obtain ⟨e, he⟩ := WangZahlLot.Obl.wz_affine_robust_cluster_estimate.exists_rotation hu
  rw [← WangZahlLot.Obl.wz_affine_robust_cluster_estimate.volume_rotation e]
  set a : Fin 3 → ℝ := ![t - r, -1, -1] with ha
  set b : Fin 3 → ℝ := ![t + r, 1, 1] with hb
  have hsub : e '' (ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r}) ⊆
      (WithLp.ofLp : Space → Fin 3 → ℝ) ⁻¹' Icc a b := by
    rintro _ ⟨p, ⟨hp, hpt⟩, rfl⟩
    have hnorm : ‖e p‖ < 1 := by
      rw [LinearIsometryEquiv.norm_map]; simpa using hp
    have h0 : (e p) 0 = inner ℝ u p := by
      rw [← LinearIsometryEquiv.inner_map_map e u p, he]
      simp [WangZahlLot.Obl.wz_affine_robust_cluster_estimate.axis, PiLp.inner_apply,
        Fin.sum_univ_three]
    have hc : ∀ i, |(e p) i| < 1 := fun i => (PiLp.norm_apply_le (e p) i).trans_lt hnorm
    change |inner ℝ u p - t| ≤ r at hpt
    obtain ⟨h1, h2⟩ := abs_le.mp hpt
    have hc1 := abs_lt.mp (hc 1)
    have hc2 := abs_lt.mp (hc 2)
    simp only [mem_preimage, mem_Icc, Pi.le_def]
    constructor
    · intro i
      fin_cases i <;> simp [ha] <;> linarith
    · intro i
      fin_cases i <;> simp [hb] <;> linarith
  calc volume (e '' (ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r}))
      ≤ volume ((WithLp.ofLp : Space → Fin 3 → ℝ) ⁻¹' Icc a b) := measure_mono hsub
    _ = volume (Icc a b) :=
      (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage measurableSet_Icc.nullMeasurableSet
    _ = ∏ i, ENNReal.ofReal (b i - a i) := Real.volume_Icc_pi
    _ = ENNReal.ofReal (8 * r) := by
      rw [Fin.prod_univ_three]
      simp only [ha, hb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by nlinarith)]
      congr 1
      ring

/-- A slab inside the unit ball is convex. -/
lemma nd_convex_slab (u : Space) (t r : ℝ) :
    Convex ℝ (ball (0 : Space) 1 ∩ {p | |inner ℝ u p - t| ≤ r}) := by
  refine (convex_ball 0 1).inter ?_
  intro p hp q hq a b ha hb hab
  change |inner ℝ u p - t| ≤ r at hp
  change |inner ℝ u q - t| ≤ r at hq
  change |inner ℝ u (a • p + b • q) - t| ≤ r
  have he : inner ℝ u (a • p + b • q) - t = a * (inner ℝ u p - t) + b * (inner ℝ u q - t) := by
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    linear_combination t * hab
  rw [he]
  calc |a * (inner ℝ u p - t) + b * (inner ℝ u q - t)|
      ≤ |a * (inner ℝ u p - t)| + |b * (inner ℝ u q - t)| := abs_add_le _ _
    _ = a * |inner ℝ u p - t| + b * |inner ℝ u q - t| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * r + b * r := by gcongr
    _ = r := by rw [← add_mul, hab, one_mul]

/-- The modified normal `(P 0, P 0 * c, P 2)`. -/
noncomputable def nd_vec (P : Space) (c : ℝ) : Space := WithLp.toLp 2 ![P 0, P 0 * c, P 2]

/-- `inner V q` agrees with the projection of the anchored grain point up to the slope error. -/
lemma nd_inner_vec_sub (P : Space) (f : ℝ → ℝ) (c y0 : ℝ) (q : Space) :
    inner ℝ (nd_vec P c) q
      - (inner ℝ P (ofTwist f (twist f q) y0 (q 2)) - y0 * (P 1 - P 0 * c))
      = P 0 * (c - f (q 2)) * (q 1 - y0) := by
  simp [nd_vec, PiLp.inner_apply, Fin.sum_univ_three, ofTwist, twist]
  ring

/-- At a point of the anchoring plane, `inner V` is the projection shifted by `K0`. -/
lemma nd_inner_vec_ofTwist (P : Space) (f : ℝ → ℝ) (u y0 z : ℝ) :
    inner ℝ (nd_vec P (f z)) (ofTwist f u y0 z)
      = inner ℝ P (ofTwist f u y0 z) - y0 * (P 1 - P 0 * f z) := by
  simp [nd_vec, PiLp.inner_apply, Fin.sum_univ_three, ofTwist]
  ring

/-- Distance between two grain points with the same second coordinate. -/
lemma nd_dist_ofTwist (f : ℝ → ℝ) (u u' y z z' : ℝ) :
    dist (ofTwist f u y z) (ofTwist f u' y z') ≤ |u - u'| + |f z - f z'| * |y| + |z - z'| := by
  rw [EuclideanSpace.dist_eq]
  simp only [Fin.sum_univ_three, Real.dist_eq, ofTwist_zero, ofTwist_one, ofTwist_two, sub_self,
    sq_abs]
  rw [Real.sqrt_le_iff]
  have h0 : |u - f z * y - (u' - f z' * y)| ≤ |u - u'| + |f z - f z'| * |y| := by
    have he : u - f z * y - (u' - f z' * y) = (u - u') - (f z - f z') * y := by ring
    rw [he, ← abs_mul]
    exact abs_sub _ _
  refine ⟨by positivity, ?_⟩
  have hA := abs_nonneg (u - f z * y - (u' - f z' * y))
  have hB := abs_nonneg (z - z')
  have hC : 0 ≤ |f z - f z'| * |y| := by positivity
  have hD := abs_nonneg (u - u')
  nlinarith [sq_abs (u - f z * y - (u' - f z' * y)), sq_abs (z - z')]

/-- If `P` almost contains the grain direction, the modified normal has size `≈ 1`. -/
lemma nd_norm_vec {P : Space} (hP : ‖P‖ = 1) {c : ℝ} (hc : |c| ≤ 1)
    (hA : |P 1 - P 0 * c| ≤ 1 / 4) :
    1 / 2 ≤ ‖nd_vec P c‖ ∧ ‖nd_vec P c‖ ≤ 2 := by
  have hP2 : P 0 ^ 2 + P 1 ^ 2 + P 2 ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq P
    rw [Fin.sum_univ_three, hP] at h
    linarith
  have hV : ‖nd_vec P c‖ ^ 2 = P 0 ^ 2 + (P 0 * c) ^ 2 + P 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    simp [nd_vec]
  have hc2 : c ^ 2 ≤ 1 := by nlinarith [abs_nonneg c, sq_abs c]
  have hA2 : (P 1 - P 0 * c) ^ 2 ≤ 1 / 16 := by
    nlinarith [abs_nonneg (P 1 - P 0 * c), sq_abs (P 1 - P 0 * c)]
  have hlow : 1 / 4 ≤ ‖nd_vec P c‖ ^ 2 := by
    rw [hV]
    nlinarith [sq_nonneg (P 1 + P 0 * c), sq_nonneg (P 0 * c)]
  have hup : ‖nd_vec P c‖ ^ 2 ≤ 4 := by
    rw [hV]
    nlinarith [sq_nonneg (P 0), sq_nonneg (P 1), mul_le_mul_of_nonneg_left hc2 (sq_nonneg (P 0))]
  have hn := norm_nonneg (nd_vec P c)
  constructor <;> nlinarith

/-- A point of a tube whose height lies in `[z1, z1 + L]` lies in a short sub-tube of
parameter length `(L + 2δ) / |v 2|`. -/
lemma nd_short_tube {δ L z1 : ℝ} {x v q : Space} (hs : v 2 ≠ 0)
    (hℓ : (L + 2 * δ) / |v 2| ≤ 1)
    (hq : q ∈ Tube δ x v) (hq2 : q 2 ∈ Icc z1 (z1 + L)) :
    q ∈ Tube δ (x + ((z1 + L / 2 - x 2) / v 2 - (L / 2 + δ) / |v 2|) • v) v ∧
    q ∈ thickening δ ((fun t : ℝ => (x + ((z1 + L / 2 - x 2) / v 2 - (L / 2 + δ) / |v 2|) • v)
      + t • v) '' Icc 0 ((L + 2 * δ) / |v 2|)) := by
  obtain ⟨t, ht, hqt⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hq
  set tl := (z1 + L / 2 - x 2) / v 2 - (L / 2 + δ) / |v 2| with htl
  set ℓ := (L + 2 * δ) / |v 2| with hℓdef
  have hv2 : 0 < |v 2| := abs_pos.mpr hs
  have h2 : |q 2 - (x 2 + t * v 2)| < δ := by
    have := (PiLp.norm_apply_le (q - (x + t • v)) 2).trans_lt hqt
    simpa using this
  have htc : |t - (z1 + L / 2 - x 2) / v 2| < (L / 2 + δ) / |v 2| := by
    have he : t - (z1 + L / 2 - x 2) / v 2 = (x 2 + t * v 2 - (z1 + L / 2)) / v 2 := by
      field_simp; ring
    rw [he, abs_div, div_lt_div_iff_of_pos_right hv2]
    obtain ⟨h21, h22⟩ := abs_lt.mp h2
    rw [abs_lt]
    constructor <;> linarith [hq2.1, hq2.2]
  obtain ⟨hc1, hc2⟩ := abs_lt.mp htc
  have hτ0 : 0 ≤ t - tl := by rw [htl]; linarith
  have hτ1 : t - tl ≤ ℓ := by
    have : ℓ = 2 * ((L / 2 + δ) / |v 2|) := by rw [hℓdef]; ring
    rw [htl, this]; linarith
  clear_value tl ℓ
  have hpt : x + t • v = (x + tl • v) + (t - tl) • v := by
    rw [sub_smul]; abel
  constructor
  · rw [mem_thickening_iff]
    refine ⟨(x + tl • v) + (t - tl) • v, ?_, ?_⟩
    · rw [segment_eq_image']
      exact ⟨t - tl, ⟨hτ0, hτ1.trans hℓ⟩, by simp⟩
    · rw [← hpt, dist_eq_norm]; exact hqt
  · rw [mem_thickening_iff]
    refine ⟨(x + tl • v) + (t - tl) • v, ⟨t - tl, ⟨hτ0, hτ1⟩, rfl⟩, ?_⟩
    rw [← hpt, dist_eq_norm]; exact hqt

/-- Lemma 6.2 applied to the part of a transversal tube inside a slab of height `L`. -/
lemma nd_angle {σ η δ θ L lam mu z1 r : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (hη : 0 < η)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hmu : 0 < mu) (hmu1 : mu ≤ 1) (hL : 0 < L)
    (hδL : 100 * δ ≤ L) (hLθ : 10 * L ≤ θ) (hδr : δ ≤ r)
    {x v U : Space} (hv : ‖v‖ = 1) (hU : ‖U‖ ≤ 1) (hθv : θ ≤ |v 2|)
    {F : Set Space} (hF : F ⊆ Tube δ x v) (hF2 : F ⊆ {q | q 2 ∈ Icc z1 (z1 + L)})
    (hmass : ENNReal.ofReal (lam * mu * L * δ ^ 2 / 32) ≤ volume F)
    (hAD : AD r (1 - σ) (6 * δ ^ (-η)) ((fun p : Space => inner ℝ U p) '' F)) :
    |inner ℝ U v| ≤ (2654208 / (lam * mu * θ * δ ^ η)) ^ σ⁻¹ * (r / L) := by
  have hv2 : 0 < |v 2| := hθ.trans_le hθv
  have hs : v 2 ≠ 0 := abs_pos.mp hv2
  have hv21 : |v 2| ≤ 1 := by
    have h := PiLp.norm_apply_le v 2
    rw [Real.norm_eq_abs, hv] at h
    exact h
  have hr : 0 < r := hδ.trans_le hδr
  have hℓ0 : 0 < (L + 2 * δ) / |v 2| := by positivity
  have hℓ1 : (L + 2 * δ) / |v 2| ≤ 1 := by rw [div_le_one hv2]; linarith
  have hℓL : L ≤ (L + 2 * δ) / |v 2| := by
    rw [le_div_iff₀ hv2]; nlinarith
  have hℓ3 : (L + 2 * δ) / |v 2| * θ ≤ 3 * L := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hv2]; nlinarith
  have hsub := fun q (hq : q ∈ F) => nd_short_tube hs hℓ1 (hF hq) (hF2 hq)
  set ℓ := (L + 2 * δ) / |v 2| with hℓ
  have hlam62 : 0 < lam * mu * L / (32 * ℓ) := by positivity
  have hmass' : ENNReal.ofReal (lam * mu * L / (32 * ℓ) * ℓ * δ ^ 2) ≤ volume F := by
    have e : lam * mu * L / (32 * ℓ) * ℓ * δ ^ 2 = lam * mu * L * δ ^ 2 / 32 := by
      field_simp
    rw [e]; exact hmass
  have hC : 0 < 6 * δ ^ (-η) := by positivity
  have hpa := projection_almost_orthogonal hδ hδr hℓ0 hlam62 hC (by linarith : 1 - σ < 1)
    _ v U hv hU (fun q hq => (hsub q hq).1) (fun q hq => (hsub q hq).2) hmass' hAD
  have hexp : (1 - (1 - σ))⁻¹ = σ⁻¹ := by ring_nf
  rw [hexp] at hpa
  have hD0 : 0 < δ ^ η := Real.rpow_pos_of_pos hδ η
  have hX : 4608 * (6 * δ ^ (-η)) / (lam * mu * L / (32 * ℓ)) ≤
      2654208 / (lam * mu * θ * δ ^ η) := by
    have e : 4608 * (6 * δ ^ (-η)) / (lam * mu * L / (32 * ℓ)) =
        884736 * ℓ / (lam * mu * L * δ ^ η) := by
      rw [Real.rpow_neg hδ.le]
      field_simp
      ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have hpos : 0 < lam * mu * δ ^ η := by positivity
    nlinarith
  have hx1 : 1 ≤ 2654208 / (lam * mu * θ * δ ^ η) := by
    rw [le_div_iff₀ (by positivity)]
    have hD1 : δ ^ η ≤ 1 := Real.rpow_le_one hδ.le hδ1 hη.le
    have h : lam * mu * θ * δ ^ η ≤ 1 * 1 * 1 * 1 := by gcongr
    linarith
  have hmax : max 1 ((4608 * (6 * δ ^ (-η)) / (lam * mu * L / (32 * ℓ))) ^ σ⁻¹) ≤
      (2654208 / (lam * mu * θ * δ ^ η)) ^ σ⁻¹ := by
    apply max_le
    · exact Real.one_le_rpow hx1 (by positivity)
    · exact Real.rpow_le_rpow (by positivity) hX (by positivity)
  calc |inner ℝ U v| ≤ max 1 ((4608 * (6 * δ ^ (-η)) / (lam * mu * L / (32 * ℓ))) ^ σ⁻¹) *
        (r / ℓ) := hpa
    _ ≤ (2654208 / (lam * mu * θ * δ ^ η)) ^ σ⁻¹ * (r / L) :=
        mul_le_mul hmax (div_le_div_of_nonneg_left hr.le hL hℓL) (by positivity)
          (by positivity)

/-- If one point `q'` of a tube satisfies `|inner U q' - c| ≤ w`, then every point of the tube
satisfies `|inner U q - c| ≤ 2δ + |inner U v| + w`. -/
lemma nd_tube_slab {δ w c : ℝ} {x v U q' q : Space} (hU : ‖U‖ ≤ 1)
    (hq' : q' ∈ Tube δ x v) (hw : |inner ℝ U q' - c| ≤ w) (hq : q ∈ Tube δ x v) :
    |inner ℝ U q - c| ≤ 2 * δ + |inner ℝ U v| + w := by
  obtain ⟨t, ht, hqt⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hq
  obtain ⟨t', ht', hqt'⟩ :=
    WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hq'
  have he : inner ℝ U q - c = inner ℝ U (q - (x + t • v)) - inner ℝ U (q' - (x + t' • v)) +
      (t - t') * inner ℝ U v + (inner ℝ U q' - c) := by
    simp only [inner_sub_right, inner_add_right, inner_smul_right]; ring
  have hb : ∀ p : Space, ‖p‖ < δ → |inner ℝ U p| ≤ δ := fun p hp =>
    (abs_real_inner_le_norm U p).trans (by nlinarith [norm_nonneg U, norm_nonneg p])
  have h1 := abs_le.mp (hb _ hqt)
  have h2 := abs_le.mp (hb _ hqt')
  have h3 : |(t - t') * inner ℝ U v| ≤ |inner ℝ U v| := by
    rw [abs_mul]
    have : |t - t'| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1, ht'.2], by linarith [ht.2, ht'.1]⟩
    nlinarith [abs_nonneg (inner ℝ U v), abs_nonneg (t - t')]
  have h3' := abs_le.mp h3
  have hw' := abs_le.mp hw
  rw [he, abs_le]
  constructor <;> linarith

/-- Pointwise estimates for points of anchored grains in the prism. -/
lemma nd_point_est {f : ℝ → ℝ} {L θ c y0 z1 : ℝ} {P : Space} (hP : ‖P‖ = 1) (hL : 0 < L)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hLθ : 10 * L ≤ θ)
    (hlip : ∀ z ∈ Icc z1 (z1 + L), ∀ z' ∈ Icc z1 (z1 + L), |f z - f z'| ≤ 2 * L * |z - z'|)
    (hy0 : y0 ∈ Icc (-1 : ℝ) 1)
    {q q0 : Space} (hq : ‖q‖ < 1) (hq2 : q 2 ∈ Icc z1 (z1 + L))
    (hq02 : q0 2 ∈ Icc z1 (z1 + L))
    (hqc : |twist f q - c| ≤ 4 * L / θ) (hq0c : |twist f q0 - c| ≤ 4 * L / θ) :
    dist (ofTwist f (twist f q) y0 (q 2)) (ofTwist f (twist f q0) y0 (q0 2)) < 10 * L / θ ∧
    |inner ℝ (nd_vec P (f (q0 2))) q -
      (inner ℝ P (ofTwist f (twist f q) y0 (q 2)) - y0 * (P 1 - P 0 * f (q0 2)))|
        ≤ 4 * L ^ 2 := by
  have hz : |q 2 - q0 2| ≤ L :=
    abs_le.mpr ⟨by linarith [hq2.1, hq02.2], by linarith [hq2.2, hq02.1]⟩
  have hf : |f (q 2) - f (q0 2)| ≤ 2 * L * L :=
    (hlip _ hq2 _ hq02).trans (by nlinarith [abs_nonneg (q 2 - q0 2)])
  have hy : |y0| ≤ 1 := abs_le.mpr ⟨hy0.1, hy0.2⟩
  constructor
  · refine (nd_dist_ofTwist f _ _ _ _ _).trans_lt ?_
    have ht : |twist f q - twist f q0| ≤ 8 * L / θ := by
      have h := abs_sub_le (twist f q) c (twist f q0)
      rw [abs_sub_comm c] at h
      have e : 8 * L / θ = 4 * L / θ + 4 * L / θ := by ring
      linarith
    have hfy : |f (q 2) - f (q0 2)| * |y0| ≤ 2 * L * L := by
      nlinarith [abs_nonneg (f (q 2) - f (q0 2)), abs_nonneg y0]
    have h2 : 2 * L ≤ 2 * L / θ := by rw [le_div_iff₀ hθ]; nlinarith
    have hL1 : L ≤ 1 / 10 := by linarith
    have e : 10 * L / θ = 8 * L / θ + 2 * L / θ := by ring
    nlinarith
  · rw [nd_inner_vec_sub]
    have hP0 : |P 0| ≤ 1 := by
      have h := PiLp.norm_apply_le P 0
      rwa [Real.norm_eq_abs, hP] at h
    have hq1 : |q 1| ≤ 1 := by
      have h := PiLp.norm_apply_le q 1
      rw [Real.norm_eq_abs] at h
      linarith
    have hqy : |q 1 - y0| ≤ 2 := (abs_sub _ _).trans (by linarith)
    have hfc : |f (q0 2) - f (q 2)| ≤ 2 * L * L := by rw [abs_sub_comm]; exact hf
    rw [abs_mul, abs_mul]
    calc |P 0| * |f (q0 2) - f (q 2)| * |q 1 - y0| ≤ 1 * (2 * L * L) * 2 := by gcongr
      _ = 4 * L ^ 2 := by ring

/-- Many tubes keep a fair share of anchored mass. -/
lemma nd_card_G4 {ι : Type*} (G : Finset ι) (a b : ι → ℝ≥0∞) {lam mu L δ θ : ℝ}
    (hlam : 0 < lam) (hmu : 0 < mu) (hL : 0 < L) (hδ : 0 < δ) (hθ : 0 < θ)
    (hab : ∀ i ∈ G, a i ≤ b i) (hb : ∀ i ∈ G, b i ≤ ENNReal.ofReal (576 * L * δ ^ 2 / θ))
    (hbG : ∀ i ∈ G, ENNReal.ofReal (mu * L * δ ^ 2 / 2) ≤ b i)
    (hsum : ENNReal.ofReal (lam / 8) * ∑ i ∈ G, b i ≤ ∑ i ∈ G, a i) :
    lam * mu * θ * G.card ≤
      18432 * (G.filter (fun i => ENNReal.ofReal (lam * mu * L * δ ^ 2 / 32) ≤ a i)).card := by
  classical
  set G4 := G.filter (fun i => ENNReal.ofReal (lam * mu * L * δ ^ 2 / 32) ≤ a i) with hG4
  set B := ENNReal.ofReal (576 * L * δ ^ 2 / θ) with hB
  set T := ENNReal.ofReal (lam * mu * L * δ ^ 2 / 32) with hT
  have h1 : ∑ i ∈ G, a i ≤ (G4.card : ℝ≥0∞) * B + (G.card : ℝ≥0∞) * T := by
    rw [← Finset.sum_filter_add_sum_filter_not G (fun i => T ≤ a i)]
    gcongr
    · calc ∑ i ∈ G with T ≤ a i, a i ≤ ∑ i ∈ G with T ≤ a i, B :=
            Finset.sum_le_sum (fun i hi =>
              (hab i (Finset.mem_filter.mp hi).1).trans (hb i (Finset.mem_filter.mp hi).1))
        _ = (G4.card : ℝ≥0∞) * B := by rw [Finset.sum_const, nsmul_eq_mul]
    · calc ∑ i ∈ G with ¬ T ≤ a i, a i ≤ ∑ i ∈ G with ¬ T ≤ a i, T :=
            Finset.sum_le_sum (fun i hi => (not_le.mp (Finset.mem_filter.mp hi).2).le)
        _ = ((G.filter (fun i : ι => ¬ T ≤ a i)).card : ℝ≥0∞) * T := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (G.card : ℝ≥0∞) * T := by
            gcongr
            exact Finset.filter_subset _ G
  have h2 : (G.card : ℝ≥0∞) * ENNReal.ofReal (mu * L * δ ^ 2 / 2) ≤ ∑ i ∈ G, b i := by
    calc (G.card : ℝ≥0∞) * ENNReal.ofReal (mu * L * δ ^ 2 / 2)
        = ∑ i ∈ G, ENNReal.ofReal (mu * L * δ ^ 2 / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ G, b i := Finset.sum_le_sum hbG
  have h3 : ENNReal.ofReal (lam / 8) * ((G.card : ℝ≥0∞) * ENNReal.ofReal (mu * L * δ ^ 2 / 2))
      ≤ (G4.card : ℝ≥0∞) * B + (G.card : ℝ≥0∞) * T := by
    calc ENNReal.ofReal (lam / 8) * ((G.card : ℝ≥0∞) * ENNReal.ofReal (mu * L * δ ^ 2 / 2))
        ≤ ENNReal.ofReal (lam / 8) * ∑ i ∈ G, b i := by gcongr
      _ ≤ _ := hsum.trans h1
  have e1 : ENNReal.ofReal (lam / 8) * ((G.card : ℝ≥0∞) * ENNReal.ofReal (mu * L * δ ^ 2 / 2))
      = ENNReal.ofReal (lam / 8 * ((G.card : ℝ) * (mu * L * δ ^ 2 / 2))) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast]
  have e2 : (G4.card : ℝ≥0∞) * B + (G.card : ℝ≥0∞) * T
      = ENNReal.ofReal ((G4.card : ℝ) * (576 * L * δ ^ 2 / θ) +
          (G.card : ℝ) * (lam * mu * L * δ ^ 2 / 32)) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  rw [e1, e2, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
  have hg : (0 : ℝ) ≤ G.card := Nat.cast_nonneg _
  have hg4 : (0 : ℝ) ≤ G4.card := Nat.cast_nonneg _
  have key : lam * mu * θ * G.card * (L * δ ^ 2) ≤ 18432 * G4.card * (L * δ ^ 2) := by
    have e : (G4.card : ℝ) * (576 * L * δ ^ 2 / θ) * θ = 576 * G4.card * (L * δ ^ 2) := by
      field_simp
    have h3' := mul_le_mul_of_nonneg_right h3 hθ.le
    rw [add_mul, e] at h3'
    nlinarith
  exact le_of_mul_le_mul_right key (by positivity)

private lemma nd_final_mid {θ lam mu K1 N g g4 D Q Ls Cb : ℝ}
    (hθ : 0 < θ) (hlam : 0 < lam)
    (hmu : 0 < mu) (hK1 : 1 ≤ K1) (hN : 0 < N) (hD0 : 0 < D) (hQ0 : 0 < Q) (hLs0 : 0 < Ls)
    (hCb0 : 0 < Cb)
    (h1 : mu ^ 2 * θ ^ 3 * N * Q * D ≤ K1 * g)
    (h4 : lam * mu * θ * g ≤ 18432 * g4)
    (h13 : g4 ≤ D⁻¹ * N * (1840 * Cb * (Q * Ls) / θ ^ 2)) :
    lam * mu ^ 3 * θ ^ 6 * D ^ 2 ≤ 33914880 * K1 * Cb * Ls := by
  have ha := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ lam * mu * θ)
  have h4' := mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ K1)
  have h13' := mul_le_mul_of_nonneg_left h13 (by positivity : (0:ℝ) ≤ 18432 * K1)
  have hchain : lam * mu * θ * (mu ^ 2 * θ ^ 3 * N * Q * D) ≤
      18432 * K1 * (D⁻¹ * N * (1840 * Cb * (Q * Ls) / θ ^ 2)) := by
    calc lam * mu * θ * (mu ^ 2 * θ ^ 3 * N * Q * D) ≤ lam * mu * θ * (K1 * g) := ha
      _ = K1 * (lam * mu * θ * g) := by ring
      _ ≤ K1 * (18432 * g4) := h4'
      _ = 18432 * K1 * g4 := by ring
      _ ≤ 18432 * K1 * (D⁻¹ * N * (1840 * Cb * (Q * Ls) / θ ^ 2)) := h13'
  have e : 18432 * K1 * (D⁻¹ * N * (1840 * Cb * (Q * Ls) / θ ^ 2)) =
      (33914880 * K1 * Cb * Ls) * (N * Q) / (D * θ ^ 2) := by
    field_simp; ring
  rw [e, le_div_iff₀ (by positivity)] at hchain
  have e2 : lam * mu * θ * (mu ^ 2 * θ ^ 3 * N * Q * D) * (D * θ ^ 2) =
      (lam * mu ^ 3 * θ ^ 6 * D ^ 2) * (N * Q) := by ring
  rw [e2] at hchain
  exact le_of_mul_le_mul_right hchain (by positivity)

private lemma nd_final_pow6 {lam mu θ D : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hmu : 0 < mu) (hmu1 : mu ≤ 1) (hθ : 0 < θ) (hD0 : 0 < D) (hD1 : D ≤ 1) :
    (lam * mu * θ * D) ^ 6 ≤ lam * mu ^ 3 * θ ^ 6 * D ^ 2 := by
  have e : (lam * mu * θ * D) ^ 6 = lam ^ 6 * mu ^ 6 * θ ^ 6 * D ^ 6 := by ring
  rw [e]
  have h1' : lam ^ 6 ≤ lam := by
    calc lam ^ 6 ≤ lam ^ 1 := pow_le_pow_of_le_one hlam.le hlam1 (by norm_num)
      _ = lam := pow_one lam
  have h2' : mu ^ 6 ≤ mu ^ 3 := pow_le_pow_of_le_one hmu.le hmu1 (by norm_num)
  have h3' : D ^ 6 ≤ D ^ 2 := pow_le_pow_of_le_one hD0.le hD1 (by norm_num)
  gcongr

private lemma nd_final_tail {σ K1 : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (hK1 : 1 ≤ K1)
    (hgg : (10 ^ 15 * K1) ^ (2 / σ) ≤ 33914880 * K1 * 2654208 ^ σ⁻¹) : False := by
  have hK0 : (1 : ℝ) ≤ 10 ^ 15 * K1 := by nlinarith
  have hsi : 1 ≤ σ⁻¹ := (one_le_inv₀ hσ).mpr hσ1.le
  have hA : (10 ^ 15 * K1) ^ (2 / σ) = (10 ^ 15 * K1) ^ σ⁻¹ * (10 ^ 15 * K1) ^ σ⁻¹ := by
    rw [← Real.rpow_add (by positivity)]; congr 1; ring
  have hB : (10 ^ 15 : ℝ) ^ σ⁻¹ ≤ (10 ^ 15 * K1) ^ σ⁻¹ :=
    Real.rpow_le_rpow (by norm_num) (by nlinarith) (by positivity)
  have hC : 10 ^ 15 * K1 ≤ (10 ^ 15 * K1) ^ σ⁻¹ := by
    calc 10 ^ 15 * K1 = (10 ^ 15 * K1) ^ (1:ℝ) := (Real.rpow_one _).symm
      _ ≤ (10 ^ 15 * K1) ^ σ⁻¹ := Real.rpow_le_rpow_of_exponent_le hK0 hsi
  have hE : (2654208 : ℝ) ^ σ⁻¹ ≤ (10 ^ 15) ^ σ⁻¹ :=
    Real.rpow_le_rpow (by norm_num) (by norm_num) (by positivity)
  have hP0 : 0 < (2654208 : ℝ) ^ σ⁻¹ := by positivity
  have hlow : (2654208 : ℝ) ^ σ⁻¹ * (10 ^ 15 * K1) ≤ (10 ^ 15 * K1) ^ (2 / σ) := by
    rw [hA]
    have h := mul_le_mul hE hC (by positivity) (by positivity)
    exact h.trans (mul_le_mul_of_nonneg_right hB (by positivity))
  have hPK : 0 < (2654208 : ℝ) ^ σ⁻¹ * K1 := mul_pos hP0 (by linarith)
  linarith

/-- The final numerical contradiction. -/
lemma nd_final {σ η δ θ L lam mu K1 N g g4 : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (hη : 0 < η)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hmu : 0 < mu) (hmu1 : mu ≤ 1) (hL : 0 < L) (hK1 : 1 ≤ K1) (hN : 0 < N)
    (h1 : mu ^ 2 * θ ^ 3 * N * L ^ (1 - σ) * δ ^ η ≤ K1 * g)
    (h4 : lam * mu * θ * g ≤ 18432 * g4)
    (h13 : g4 ≤ δ ^ (-η) * N *
      (1840 * (2654208 / (lam * mu * θ * δ ^ η)) ^ σ⁻¹ * L / θ ^ 2))
    (hK : (10 ^ 15 * K1) ^ (2 / σ) * L ^ σ ≤ (lam * mu * θ * δ ^ η) ^ (7 / σ)) : False := by
  have hD0 : 0 < δ ^ η := Real.rpow_pos_of_pos hδ η
  have hD1 : δ ^ η ≤ 1 := Real.rpow_le_one hδ.le hδ1 hη.le
  have hDinv : δ ^ (-η) = (δ ^ η)⁻¹ := Real.rpow_neg hδ.le η
  have hx0 : 0 < lam * mu * θ * δ ^ η := by positivity
  have hx1 : lam * mu * θ * δ ^ η ≤ 1 := by
    have h : lam * mu * θ * δ ^ η ≤ 1 * 1 * 1 * 1 := by gcongr
    linarith
  have hQ0 : 0 < L ^ (1 - σ) := Real.rpow_pos_of_pos hL _
  have hLs0 : 0 < L ^ σ := Real.rpow_pos_of_pos hL _
  have hLQ : L = L ^ (1 - σ) * L ^ σ := by
    rw [← Real.rpow_add hL]; simp
  have he : (2654208 / (lam * mu * θ * δ ^ η)) ^ σ⁻¹ =
      2654208 ^ σ⁻¹ / (lam * mu * θ * δ ^ η) ^ σ⁻¹ := Real.div_rpow (by norm_num) hx0.le _
  have hCb0 : 0 < (2654208 / (lam * mu * θ * δ ^ η)) ^ σ⁻¹ := by positivity
  rw [hDinv] at h13
  rw [hLQ] at h13
  have hc := nd_final_mid hθ hlam hmu hK1 hN hD0 hQ0 hLs0 hCb0 h1 h4 h13
  have hd := nd_final_pow6 hlam hlam1 hmu hmu1 hθ hD0 hD1
  have hxs0 : 0 < (lam * mu * θ * δ ^ η) ^ σ⁻¹ := Real.rpow_pos_of_pos hx0 _
  have hf : (lam * mu * θ * δ ^ η) ^ 6 * (lam * mu * θ * δ ^ η) ^ σ⁻¹ ≤
      33914880 * K1 * 2654208 ^ σ⁻¹ * L ^ σ := by
    have h := hd.trans hc
    rw [he] at h
    have e : 33914880 * K1 * (2654208 ^ σ⁻¹ / (lam * mu * θ * δ ^ η) ^ σ⁻¹) * L ^ σ =
        (33914880 * K1 * 2654208 ^ σ⁻¹ * L ^ σ) / (lam * mu * θ * δ ^ η) ^ σ⁻¹ := by ring
    rw [e, le_div_iff₀ hxs0] at h
    exact h
  have hg : (lam * mu * θ * δ ^ η) ^ (7 / σ) ≤
      (lam * mu * θ * δ ^ η) ^ 6 * (lam * mu * θ * δ ^ η) ^ σ⁻¹ := by
    rw [← Real.rpow_natCast (lam * mu * θ * δ ^ η) 6, ← Real.rpow_add hx0]
    apply Real.rpow_le_rpow_of_exponent_ge hx0 hx1
    have h6 : (6 : ℝ) ≤ 6 / σ := by rw [le_div_iff₀ hσ]; nlinarith
    have e : 7 / σ = 6 / σ + σ⁻¹ := by field_simp; ring
    push_cast
    linarith
  have hgg : (10 ^ 15 * K1) ^ (2 / σ) ≤ 33914880 * K1 * 2654208 ^ σ⁻¹ := by
    have h := (hK.trans hg).trans hf
    exact le_of_mul_le_mul_right h hLs0
  exact nd_final_tail hσ hσ1 hK1 hgg

/-- The local-fullness scale `ℓ = (lam δ^η / 40)^(1/σ) / 4`. -/
lemma nd_ell {σ η δ lam K : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (hη : 0 < η) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hK : 160 ≤ K)
    (hKδ : K * δ ^ (σ / 2) ≤ lam * δ ^ η) :
    0 < (lam * δ ^ η / 40) ^ σ⁻¹ / 4 ∧ (lam * δ ^ η / 40) ^ σ⁻¹ / 4 ≤ 1 ∧
    δ ≤ ((lam * δ ^ η / 40) ^ σ⁻¹ / 4) ^ 2 ∧
    2 * δ ^ (-η) * ((lam * δ ^ η / 40) ^ σ⁻¹ / 4) ^ σ ≤ lam / 20 * (1 / 4) ^ σ := by
  have hD0 : 0 < δ ^ η := Real.rpow_pos_of_pos hδ η
  have hD1 : δ ^ η ≤ 1 := Real.rpow_le_one hδ.le hδ1 hη.le
  have ha0 : 0 < lam * δ ^ η / 40 := by positivity
  have ha1 : lam * δ ^ η / 40 ≤ 1 := by
    have : lam * δ ^ η ≤ 1 * 1 := by gcongr
    linarith
  have hsi : 1 ≤ σ⁻¹ := (one_le_inv₀ hσ).mpr hσ1.le
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · have : (lam * δ ^ η / 40) ^ σ⁻¹ ≤ 1 := Real.rpow_le_one ha0.le ha1 (by positivity)
    linarith
  · -- a ≥ 4 δ^(σ/2)
    have hs0 : 0 < δ ^ (σ / 2) := Real.rpow_pos_of_pos hδ _
    have ha : 4 * δ ^ (σ / 2) ≤ lam * δ ^ η / 40 := by
      have : 160 * δ ^ (σ / 2) ≤ K * δ ^ (σ / 2) := mul_le_mul_of_nonneg_right hK hs0.le
      linarith
    have h1 : (4 * δ ^ (σ / 2)) ^ σ⁻¹ ≤ (lam * δ ^ η / 40) ^ σ⁻¹ :=
      Real.rpow_le_rpow (by positivity) ha (by positivity)
    have h2 : (4 * δ ^ (σ / 2)) ^ σ⁻¹ = 4 ^ σ⁻¹ * Real.sqrt δ := by
      rw [Real.mul_rpow (by norm_num) hs0.le, ← Real.rpow_mul hδ.le, Real.sqrt_eq_rpow]
      congr 2
      field_simp
    have h3 : (4 : ℝ) ≤ 4 ^ σ⁻¹ := by
      calc (4 : ℝ) = 4 ^ (1 : ℝ) := (Real.rpow_one 4).symm
        _ ≤ 4 ^ σ⁻¹ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hsi
    have hsq : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
    have h4 : Real.sqrt δ ≤ (lam * δ ^ η / 40) ^ σ⁻¹ / 4 := by
      rw [le_div_iff₀ (by norm_num)]
      nlinarith
    have h5 : Real.sqrt δ ^ 2 ≤ ((lam * δ ^ η / 40) ^ σ⁻¹ / 4) ^ 2 := by gcongr
    rwa [Real.sq_sqrt hδ.le] at h5
  · have e1 : ((lam * δ ^ η / 40) ^ σ⁻¹ / 4) ^ σ = (lam * δ ^ η / 40) / 4 ^ σ := by
      rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_inv_rpow ha0.le hσ.ne']
    have e2 : (1 / 4 : ℝ) ^ σ = 1 / 4 ^ σ := by
      rw [Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow]
    have e3 : δ ^ (-η) * δ ^ η = 1 := by
      rw [Real.rpow_neg hδ.le, inv_mul_cancel₀ hD0.ne']
    rw [e1, e2]
    apply le_of_eq
    calc 2 * δ ^ (-η) * (lam * δ ^ η / 40 / 4 ^ σ)
        = lam / 20 * (δ ^ (-η) * δ ^ η) * (1 / 4 ^ σ) := by ring
      _ = lam / 20 * (1 / 4 ^ σ) := by rw [e3, mul_one]

/-- A shading inside a slab of height `L` has volume `≲ L δ² / θ`. -/
lemma nd_vol_Z {δ L θ z1 : ℝ} (hδ : 0 < δ) (hδL : 100 * δ ≤ L) (hθ : 0 < θ) {x v : Space}
    (hv : ‖v‖ = 1) {Zi : Set Space} (hZT : Zi ⊆ Tube δ x v) (hZv : Zi.Nonempty → θ ≤ |v 2|)
    (hZJ : Zi ⊆ {q | q 2 ∈ Icc z1 (z1 + L)}) :
    volume Zi ≤ ENNReal.ofReal (576 * L * δ ^ 2 / θ) := by
  rcases Zi.eq_empty_or_nonempty with h | h
  · rw [h, measure_empty]; exact zero_le
  have hθv := hZv h
  have hinner : ∀ p : Space, inner ℝ (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) p = p 2 := by
    intro p; rw [EuclideanSpace.inner_single_left]; simp
  have he2 : ‖(EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : Space)‖ ≤ 1 := by simp
  have hq : 0 < |inner ℝ (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) v| := by
    rw [hinner]; linarith
  have hsub : Zi ⊆ Tube δ x v ∩
      {p | |inner ℝ (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) p - (z1 + L / 2)| ≤ L / 2} := by
    intro p hp
    refine ⟨hZT hp, ?_⟩
    have h2 := hZJ hp
    simp only [mem_ofPred_eq, hinner] at h2 ⊢
    rw [abs_le]; constructor <;> linarith [h2.1, h2.2]
  calc volume Zi ≤ _ := measure_mono hsub
    _ ≤ ENNReal.ofReal (1152 * ((L / 2) /
          |inner ℝ (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) v|) * δ ^ 2) :=
        tube_slab_volume_le hδ (by linarith) x v _ hv he2 hq _
    _ ≤ ENNReal.ofReal (576 * L * δ ^ 2 / θ) := by
      apply ENNReal.ofReal_le_ofReal
      rw [hinner]
      have h1 : L / 2 / |v 2| ≤ L / 2 / θ :=
        div_le_div_of_nonneg_left (by linarith) hθ hθv
      calc 1152 * (L / 2 / |v 2|) * δ ^ 2 ≤ 1152 * (L / 2 / θ) * δ ^ 2 := by gcongr
        _ = 576 * L * δ ^ 2 / θ := by ring

/-- A set of positive measure is nonempty. -/
lemma nd_nonempty_of_le {S : Set Space} {a : ℝ} (ha : 0 < a)
    (h : ENNReal.ofReal a ≤ volume S) : S.Nonempty := by
  rw [nonempty_iff_ne_empty]
  rintro rfl
  rw [measure_empty, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h
  linarith

/-- The angle constant is at least `1`. -/
lemma nd_Cb {σ η δ θ lam mu : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hmu : 0 < mu)
    (hmu1 : mu ≤ 1) : 1 ≤ (2654208 / (lam * mu * θ * δ ^ η)) ^ σ⁻¹ := by
  have hD0 : 0 < δ ^ η := Real.rpow_pos_of_pos hδ η
  have hD1 : δ ^ η ≤ 1 := Real.rpow_le_one hδ.le hδ1 hη.le
  apply Real.one_le_rpow _ (by positivity)
  rw [le_div_iff₀ (by positivity)]
  have h : lam * mu * θ * δ ^ η ≤ 1 * 1 * 1 * 1 := by gcongr
  linarith

/-- The total width of the slab containing the anchored tubes. -/
lemma nd_Wd {δ L θ Cb : ℝ} (hδ : 0 < δ) (hδL : 100 * δ ≤ L) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hLθ : 10 * L ≤ θ) (hCb : 1 ≤ Cb) :
    8 * (2 * δ + Cb * (2 * (10 * L / θ) ^ 2 / L) + 2 * (4 * L ^ 2 + 10 * L / θ)) ≤
      1840 * Cb * L / θ ^ 2 := by
  have hL : 0 < L := by linarith
  have hM : L / θ ^ 2 = L / θ ^ 2 := rfl
  have e1 : 2 * (10 * L / θ) ^ 2 / L = 200 * (L / θ ^ 2) := by field_simp; ring
  have e2 : 1840 * Cb * L / θ ^ 2 = 1840 * Cb * (L / θ ^ 2) := by ring
  have hθ2 : θ ^ 2 ≤ 1 := by nlinarith
  have hLM : L ≤ L / θ ^ 2 := by rw [le_div_iff₀ (by positivity)]; nlinarith
  have hLθM : L / θ ≤ L / θ ^ 2 := by
    rw [div_le_div_iff₀ hθ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hθ1 (mul_pos hL hθ).le]
  have hL2 : L ^ 2 ≤ L := by nlinarith
  have hMpos : 0 < L / θ ^ 2 := by positivity
  have hCM : L / θ ^ 2 ≤ Cb * (L / θ ^ 2) := le_mul_of_one_le_left hMpos.le hCb
  rw [e1, e2]
  have e3 : 10 * L / θ = 10 * (L / θ) := by ring
  rw [e3]
  nlinarith

/-- The geometric core (Steps 7–13 of Lemma 6.6): every anchored tube lies in one thin slab,
so the global convex count bounds the number of anchored tubes. -/
lemma nd_core {σ η δ θ L lam mu z1 c y0 : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (hη : 0 < η)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hmu : 0 < mu) (hmu1 : mu ≤ 1) (hL : 0 < L) (hδL : 100 * δ ≤ L) (hδL2 : δ ≤ L ^ 2)
    (hLθ : 10 * L ≤ θ) {n : ℕ} {x v : Fin n → Space} (hv : ∀ i, ‖v i‖ = 1)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1) (hGC : GlobalCount η δ n x v) {f : ℝ → ℝ}
    (hlip : ∀ z ∈ Icc z1 (z1 + L), ∀ z' ∈ Icc z1 (z1 + L), |f z - f z'| ≤ 2 * L * |z - z'|)
    {E : Set Space} {P : Space → Space} (hPn : ∀ p ∈ E, ‖P p‖ = 1)
    (hLG : LocalGrains σ η δ P E) (hy0 : y0 ∈ Icc (-1 : ℝ) 1)
    (G4 : Finset (Fin n)) (Za : Fin n → Set Space)
    (hZaT : ∀ i ∈ G4, Za i ⊆ Tube δ (x i) (v i))
    (hZaJ : ∀ i ∈ G4, Za i ⊆ {q | q 2 ∈ Icc z1 (z1 + L)})
    (hZav : ∀ i ∈ G4, θ ≤ |v i 2|)
    (hZab : ∀ i ∈ G4, Za i ⊆ ball 0 1)
    (hZac : ∀ i ∈ G4, ∀ q ∈ Za i, |twist f q - c| ≤ 4 * L / θ)
    (hZay : ∀ i ∈ G4, ∀ q ∈ Za i, ofTwist f (twist f q) y0 (q 2) ∈ E)
    (hZam : ∀ i ∈ G4, ENNReal.ofReal (lam * mu * L * δ ^ 2 / 32) ≤ volume (Za i))
    {q0 : Space} (hq0J : q0 2 ∈ Icc z1 (z1 + L)) (hq0c : |twist f q0 - c| ≤ 4 * L / θ)
    (hpS : ofTwist f (twist f q0) y0 (q0 2) ∈ E) (hfS : |f (q0 2)| ≤ 1)
    (hA : |P (ofTwist f (twist f q0) y0 (q0 2)) 1 -
      P (ofTwist f (twist f q0) y0 (q0 2)) 0 * f (q0 2)| ≤ 1 / 4) :
    (G4.card : ℝ) ≤ δ ^ (-η) * n *
      (1840 * (2654208 / (lam * mu * θ * δ ^ η)) ^ σ⁻¹ * L / θ ^ 2) := by
  obtain ⟨pS, hpSdef⟩ : ∃ pS, pS = ofTwist f (twist f q0) y0 (q0 2) := ⟨_, rfl⟩
  rw [← hpSdef] at hpS hA
  obtain ⟨Pv, hPvdef⟩ : ∃ Pv, Pv = P pS := ⟨_, rfl⟩
  rw [← hPvdef] at hA
  have hPv : ‖Pv‖ = 1 := hPvdef ▸ hPn pS hpS
  obtain ⟨V, hVdef⟩ : ∃ V, V = nd_vec Pv (f (q0 2)) := ⟨_, rfl⟩
  obtain ⟨hV1, hV2⟩ := nd_norm_vec hPv hfS hA
  rw [← hVdef] at hV1 hV2
  have hVpos : 0 < ‖V‖ := by linarith
  obtain ⟨s, hsdef⟩ : ∃ s, s = ‖V‖⁻¹ := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsdef]; positivity
  have hs2 : s ≤ 2 := by
    rw [hsdef]; exact (inv_le_comm₀ hVpos (by norm_num)).mpr (by linarith)
  have hs12 : 1 / 2 ≤ s := by
    rw [hsdef]; exact (le_inv_comm₀ (by norm_num) hVpos).mpr (by linarith)
  obtain ⟨U, hUdef⟩ : ∃ U, U = s • V := ⟨_, rfl⟩
  have hU : ‖U‖ = 1 := by
    rw [hUdef, norm_smul, Real.norm_eq_abs, abs_of_pos hs0, hsdef, inv_mul_cancel₀ hVpos.ne']
  have hUinner : ∀ p, inner ℝ U p = s * inner ℝ V p := fun p => by
    rw [hUdef, real_inner_smul_left]
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = (10 * L / θ) ^ 2 := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρdef]; positivity
  have hLθ1 : 10 * L / θ ≤ 1 := by rw [div_le_one hθ]; exact hLθ
  have hρ1 : ρ ≤ 1 := by rw [hρdef]; exact pow_le_one₀ (by positivity) hLθ1
  have hρL : 100 * L ^ 2 ≤ ρ := by
    have h1 : 10 * L ≤ 10 * L / θ := by rw [le_div_iff₀ hθ]; nlinarith
    have h2 : (10 * L) ^ 2 ≤ (10 * L / θ) ^ 2 := by gcongr
    rw [hρdef]; nlinarith
  have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
  have h100 : 100 * δ ≤ ρ := by linarith
  have hρδ : δ ≤ ρ := by linarith
  have h4L : 4 * L ^ 2 ≤ ρ := by linarith
  have hADA := hLG ρ hρδ hρ1 pS hpS
  have hsq : Real.sqrt ρ = 10 * L / θ := by rw [hρdef]; exact Real.sqrt_sq (by positivity)
  rw [hsq, ← hPvdef] at hADA
  obtain ⟨K0, hK0def⟩ : ∃ K0, K0 = y0 * (Pv 1 - Pv 0 * f (q0 2)) := ⟨_, rfl⟩
  have hAD2 := nd_ad_affine (K0 := K0) (t := 4 * L ^ 2) hADA hρ0 hs0 (by positivity) h4L
    (by positivity) (by linarith) (by linarith)
  obtain ⟨Cb, hCbdef⟩ : ∃ Cb, Cb = (2654208 / (lam * mu * θ * δ ^ η)) ^ σ⁻¹ := ⟨_, rfl⟩
  have hCb1 : 1 ≤ Cb := hCbdef ▸ nd_Cb hσ hη hδ hδ1 hθ hθ1 hlam hlam1 hmu hmu1
  obtain ⟨Wd, hWddef⟩ : ∃ Wd, Wd = 2 * δ + Cb * (2 * ρ / L) + 2 * (4 * L ^ 2 + 10 * L / θ) :=
    ⟨_, rfl⟩
  have hWd0 : 0 ≤ Wd := by rw [hWddef]; positivity
  have hVpS : inner ℝ V pS = inner ℝ Pv pS - K0 := by
    rw [hVdef, hpSdef, hK0def]; exact nd_inner_vec_ofTwist Pv f _ y0 _
  have hpt : ∀ i ∈ G4, ∀ q ∈ Za i,
      ofTwist f (twist f q) y0 (q 2) ∈ E ∩ ball pS (10 * L / θ) ∧
      |inner ℝ V q - (inner ℝ Pv (ofTwist f (twist f q) y0 (q 2)) - K0)| ≤ 4 * L ^ 2 := by
    intro i hi q hq
    have hqb : ‖q‖ < 1 := mem_ball_zero_iff.mp (hZab i hi hq)
    obtain ⟨hd, hin⟩ := nd_point_est (P := Pv) hPv hL hθ hθ1 hLθ hlip hy0 hqb (hZaJ i hi hq)
      hq0J (hZac i hi q hq) hq0c
    refine ⟨⟨hZay i hi q hq, ?_⟩, ?_⟩
    · rw [mem_ball, hpSdef]; exact hd
    · rw [hVdef, hK0def]; exact hin
  have hslab : ∀ i ∈ G4, Tube δ (x i) (v i) ⊆
      ball 0 1 ∩ {p | |inner ℝ U p - inner ℝ U pS| ≤ Wd} := by
    intro i hi
    have hsubA : (fun p : Space => inner ℝ U p) '' Za i ⊆
        {y | ∃ b ∈ (fun q : Space => inner ℝ Pv q) '' (E ∩ ball pS (10 * L / θ)),
          |y - s * (b - K0)| ≤ s * (4 * L ^ 2)} := by
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨hmem, hest⟩ := hpt i hi q hq
      refine ⟨_, ⟨_, hmem, rfl⟩, ?_⟩
      show |inner ℝ U q - s * (inner ℝ Pv (ofTwist f (twist f q) y0 (q 2)) - K0)| ≤
        s * (4 * L ^ 2)
      rw [hUinner, ← mul_sub, abs_mul, abs_of_pos hs0]
      exact mul_le_mul_of_nonneg_left hest hs0.le
    have hADi := ad_mono hAD2 hsubA
    have hsρ : δ ≤ s * ρ := by
      calc δ ≤ 1 / 2 * ρ := by linarith
        _ ≤ s * ρ := mul_le_mul_of_nonneg_right hs12 hρ0.le
    have hang := nd_angle hσ hσ1 hη hδ hδ1 hθ hθ1 hlam hlam1 hmu hmu1 hL hδL hLθ hsρ (hv i)
      hU.le (hZav i hi) (hZaT i hi) (hZaJ i hi) (hZam i hi) hADi
    rw [← hCbdef] at hang
    have hang2 : |inner ℝ U (v i)| ≤ Cb * (2 * ρ / L) := by
      refine hang.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hs2 hρ0.le) hL.le
    obtain ⟨q', hq'⟩ := nd_nonempty_of_le (by positivity) (hZam i hi)
    have hw : |inner ℝ U q' - inner ℝ U pS| ≤ 2 * (4 * L ^ 2 + 10 * L / θ) := by
      obtain ⟨⟨_, hball'⟩, hest⟩ := hpt i hi q' hq'
      rw [hUinner, hUinner, ← mul_sub, abs_mul, abs_of_pos hs0, hVpS]
      have h1 : |inner ℝ Pv (ofTwist f (twist f q') y0 (q' 2)) - inner ℝ Pv pS| ≤
          10 * L / θ := by
        rw [← inner_sub_right]
        refine (abs_real_inner_le_norm _ _).trans ?_
        rw [hPv, one_mul, ← dist_eq_norm]
        exact (mem_ball.mp hball').le
      have h2 : |inner ℝ V q' - (inner ℝ Pv pS - K0)| ≤ 4 * L ^ 2 + 10 * L / θ := by
        have e : inner ℝ V q' - (inner ℝ Pv pS - K0) =
            (inner ℝ V q' - (inner ℝ Pv (ofTwist f (twist f q') y0 (q' 2)) - K0)) +
            (inner ℝ Pv (ofTwist f (twist f q') y0 (q' 2)) - inner ℝ Pv pS) := by ring
        rw [e]
        exact (abs_add_le _ _).trans (add_le_add hest h1)
      exact mul_le_mul hs2 h2 (abs_nonneg _) (by norm_num)
    intro p hp
    refine ⟨hball i hp, ?_⟩
    have h := nd_tube_slab hU.le (hZaT i hi hq') hw hp
    show |inner ℝ U p - inner ℝ U pS| ≤ Wd
    rw [hWddef]; linarith
  have hGCW := hGC _ (nd_convex_slab U (inner ℝ U pS) Wd)
  have hvolW := nd_slab_volume_le hU (inner ℝ U pS) Wd hWd0
  have hcard : G4.card ≤
      ncard {i | Tube δ (x i) (v i) ⊆ ball 0 1 ∩ {p | |inner ℝ U p - inner ℝ U pS| ≤ Wd}} := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard (fun i hi => hslab i hi)
  have hreal : (ncard {i | Tube δ (x i) (v i) ⊆
      ball 0 1 ∩ {p | |inner ℝ U p - inner ℝ U pS| ≤ Wd}} : ℝ) ≤ δ ^ (-η) * n * (8 * Wd) := by
    have h2 : ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) *
        volume (ball (0 : Space) 1 ∩ {p | |inner ℝ U p - inner ℝ U pS| ≤ Wd}) ≤
        ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * ENNReal.ofReal (8 * Wd) := by gcongr
    have h := hGCW.trans h2
    rw [← ENNReal.ofReal_mul (by positivity)] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  have hWd := nd_Wd hδ hδL hθ hθ1 hLθ hCb1
  rw [← hρdef, ← hWddef] at hWd
  calc (G4.card : ℝ) ≤ δ ^ (-η) * n * (8 * Wd) := (Nat.cast_le.mpr hcard).trans hreal
    _ ≤ δ ^ (-η) * n * (1840 * Cb * L / θ ^ 2) := by gcongr
    _ = _ := by rw [hCbdef]

theorem nondegenerate : ∃ K : ℝ, 1 ≤ K ∧ ∀ (σ η δ θ L lam mu z1 : ℝ), 0 < σ → σ < 1 →
    0 < η → 0 < δ → δ ≤ 1 / 100 → 0 < θ → θ ≤ 1 → 0 < lam → lam ≤ 1 → 0 < mu → mu ≤ 1 →
    100 * δ ≤ L → δ ≤ L ^ 2 → 10 * L ≤ θ → -1 ≤ z1 → z1 + L ≤ 1 →
    K * δ ^ (σ / 2) ≤ lam * δ ^ η →
    K ^ (2 / σ) * L ^ σ ≤ (lam * mu * θ * δ ^ η) ^ (7 / σ) →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space), 0 < n → Family δ n x v Y →
    GlobalCount η δ n x v →
    ∀ (f : ℝ → ℝ) (P : Space → Space), Continuous f → (∀ z ∈ Icc (-1 : ℝ) 1, |f z| ≤ 1) →
    (∀ z ∈ Icc z1 (z1 + L), ∀ z' ∈ Icc z1 (z1 + L), |f z - f z'| ≤ 2 * L * |z - z'|) →
    GlobalGrains σ η δ f (⋃ i, Y i) →
    (∀ p ∈ ⋃ i, Y i, ‖P p‖ = 1) → LocalGrains σ η δ P (⋃ i, Y i) →
    ∀ Z : Fin n → Set Space, (∀ i, MeasurableSet (Z i)) → (∀ i, Z i ⊆ Y i) →
    (∀ i, (Z i).Nonempty → θ ≤ |v i 2|) → (∀ i, Z i ⊆ {q | q 2 ∈ Icc z1 (z1 + L)}) →
    (∀ i, Z i ⊆ FullPart f (⋃ j, Y j) lam) →
    ENNReal.ofReal (mu * n * L * δ ^ 2) ≤ ∑ i, volume (Z i) →
    False := by
  obtain ⟨K1, hK1, hcount⟩ := nd_count
  refine ⟨10 ^ 15 * K1, by nlinarith, ?_⟩
  intro σ η δ θ L lam mu z1 hσ hσ1 hη hδ hδ1 hθ hθ1 hlam hlam1 hmu hmu1 hδL hδL2 hLθ hz1
    hz1L hKδ hKL n x v Y hn hfam hGC f P hf hf1 hlip hGG hPn hLG Z hZm hZY hZv hZJ hZfull hmass
  have hL : 0 < L := by linarith
  have hδ1' : δ ≤ 1 := by linarith
  -- Step 1: a rich prism
  obtain ⟨c, G, hGc, hGm, hGcard⟩ := hcount σ η δ θ L mu z1 hσ hσ1 hη hδ hδ1 hθ hθ1 hmu
    hδL hLθ hz1 hz1L n x v Y hfam f hf hf1 hlip hGG Z hZm hZY hZv hZJ hmass
  have hEm : MeasurableSet (⋃ i, Y i) := MeasurableSet.iUnion hfam.meas
  have hEb : (⋃ i, Y i) ⊆ ball (0 : Space) 1 := by
    intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact hfam.ball i (hfam.sub i hi)
  have hZb : ∀ i, Z i ⊆ ball (0 : Space) 1 :=
    fun i => (hZY i).trans ((subset_iUnion Y i).trans hEb)
  have hZT : ∀ i, Z i ⊆ Tube δ (x i) (v i) := fun i => (hZY i).trans (hfam.sub i)
  -- Step 2: the local fullness scale
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ℓ = (lam * δ ^ η / 40) ^ σ⁻¹ / 4 := ⟨_, rfl⟩
  have hK160 : (160 : ℝ) ≤ 10 ^ 15 * K1 := by linarith
  obtain ⟨hℓ0, hℓ1, hδℓ, hℓsmall⟩ := nd_ell hσ hσ1 hη hδ hδ1' hlam hlam1 hK160 hKδ
  rw [← hℓdef] at hℓ0 hℓ1 hδℓ hℓsmall
  -- Step 3: a common anchoring plane
  obtain ⟨y0, hy0, hanch⟩ := nd_anchor hf hEm hEb hlam hℓ0 hℓ1 G Z (fun i _ => hZm i)
    (fun i _ => hZb i) (fun i _ => hZfull i)
  obtain ⟨Za, hZadef⟩ : ∃ Za : Fin n → Set Space, Za = fun i =>
      {q | q ∈ Z i ∧ y0 ∈ grainFib f (⋃ j, Y j) (twist f q) (q 2) ∧
        LocFull (grainFib f (⋃ j, Y j) (twist f q) (q 2)) ℓ (lam / 20) y0} := ⟨_, rfl⟩
  have hmemZa : ∀ i q, q ∈ Za i ↔ (q ∈ Z i ∧ y0 ∈ grainFib f (⋃ j, Y j) (twist f q) (q 2) ∧
      LocFull (grainFib f (⋃ j, Y j) (twist f q) (q 2)) ℓ (lam / 20) y0) := by
    intro i q; rw [hZadef]; rfl
  have hanch' : ENNReal.ofReal (lam / 8) * ∑ i ∈ G, volume (Z i) ≤
      ∑ i ∈ G, volume (Za i) := by
    rw [hZadef]; exact hanch
  have hZaZ : ∀ i, Za i ⊆ Z i := fun i q hq => ((hmemZa i q).mp hq).1
  -- Step 4: many tubes carry anchored mass
  have hvolZ : ∀ i, volume (Z i) ≤ ENNReal.ofReal (576 * L * δ ^ 2 / θ) := fun i =>
    nd_vol_Z hδ hδL hθ (hfam.unit i) (hZT i) (hZv i) (hZJ i)
  obtain ⟨G4, hG4def⟩ : ∃ G4 : Finset (Fin n),
      G4 = G.filter (fun i => ENNReal.ofReal (lam * mu * L * δ ^ 2 / 32) ≤ volume (Za i)) :=
    ⟨_, rfl⟩
  have hcardG4 : lam * mu * θ * G.card ≤ 18432 * G4.card := by
    rw [hG4def]
    exact nd_card_G4 G (fun i => volume (Za i)) (fun i => volume (Z i)) hlam hmu hL hδ hθ
      (fun i _ => measure_mono (hZaZ i)) (fun i _ => hvolZ i) hGm hanch'
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hGpos : (0 : ℝ) < G.card := by
    have hQ := Real.rpow_pos_of_pos hL (1 - σ)
    have hD := Real.rpow_pos_of_pos hδ η
    have h1 : 0 < mu ^ 2 * θ ^ 3 * n * L ^ (1 - σ) * δ ^ η := by positivity
    have h2 := h1.trans_le hGcard
    rcases (Nat.cast_nonneg (α := ℝ) G.card).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at h2; exact absurd h2 (lt_irrefl 0)
  have hG4pos : (0 : ℝ) < G4.card := by
    have : 0 < lam * mu * θ * G.card := by positivity
    linarith
  have hG4G : ∀ i ∈ G4, i ∈ G ∧ ENNReal.ofReal (lam * mu * L * δ ^ 2 / 32) ≤ volume (Za i) := by
    intro i hi; rw [hG4def, Finset.mem_filter] at hi; exact hi
  -- Step 5: an anchor point
  obtain ⟨i0, hi0⟩ : G4.Nonempty := by
    rw [← Finset.card_pos]; exact_mod_cast hG4pos
  obtain ⟨hi0G, hi0m⟩ := hG4G i0 hi0
  obtain ⟨q0, hq0⟩ := nd_nonempty_of_le (by positivity) hi0m
  obtain ⟨hq0Z, hq0y, hq0full⟩ := (hmemZa i0 q0).mp hq0
  have hzSJ : q0 2 ∈ Icc z1 (z1 + L) := hZJ i0 hq0Z
  have hzS1 : q0 2 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hzSJ.1], by linarith [hzSJ.2]⟩
  have hpS : ofTwist f (twist f q0) y0 (q0 2) ∈ ⋃ j, Y j := hq0y
  have hPv := hPn _ hpS
  -- Step 6: the local plane contains the grain direction
  have hLGℓ := hLG (ℓ ^ 2) hδℓ (pow_le_one₀ hℓ0.le hℓ1) _ hpS
  rw [Real.sqrt_sq hℓ0.le] at hLGℓ
  have hA := nd_claimA hσ hσ1 hη hδ hδ1' hℓ0 hδℓ (by positivity : (0 : ℝ) < lam / 20)
    (by linarith) hℓsmall (hf1 _ hzS1) hPv hLGℓ hq0full
  -- Steps 7–13
  have hcore := nd_core hσ hσ1 hη hδ hδ1' hθ hθ1 hlam hlam1 hmu hmu1 hL hδL hδL2 hLθ hfam.unit
    hfam.ball hGC hlip hPn hLG hy0 G4 Za
    (fun i _ => (hZaZ i).trans (hZT i))
    (fun i _ => (hZaZ i).trans (hZJ i))
    (fun i hi => hZv i ((nd_nonempty_of_le (by positivity) (hG4G i hi).2).mono (hZaZ i)))
    (fun i _ => (hZaZ i).trans (hZb i))
    (fun i hi q hq => hGc i (hG4G i hi).1 (hZaZ i hq))
    (fun i _ q hq => ((hmemZa i q).mp hq).2.1)
    (fun i hi => (hG4G i hi).2)
    hzSJ (hGc i0 hi0G hq0Z) hpS (hf1 _ hzS1) hA
  -- Step 14
  exact nd_final hσ hσ1 hη hδ hδ1' hθ hθ1 hlam hlam1 hmu hmu1 hL hK1 hn' hGcard hcardG4 hcore hKL

end WangZahlLot.Obl.wz_grains_nonsingular_slices
