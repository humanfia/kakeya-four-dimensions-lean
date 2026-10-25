-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse.TSFibre.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Coarse.TSRescale
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Coarse.TSCoarse

/-!
# Rescaled fibres: geometry

Tubes of one fibre are oriented along the coarse direction `w0`, mapped by the
anisotropic rescaling and extended to unit length. Containments in finer covers
transfer to containments in thickened rescaled covers.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse

open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace Pointwise Classical
open WangZahlLot.Obl.wz_separated_cover_refinement (Tube Dilate)

/-- Start point of the tube oriented along `w0`. -/
noncomputable def orStart (w0 x v : Space) : Space := if 0 ≤ ⟪v, w0⟫ then x else x + v

/-- Direction of the tube oriented along `w0`. -/
noncomputable def orDir (w0 v : Space) : Space := if 0 ≤ ⟪v, w0⟫ then v else -v

theorem Tube_orient (r : ℝ) (w0 x v : Space) :
    Tube r (orStart w0 x v) (orDir w0 v) = Tube r x v := by
  unfold orStart orDir
  split_ifs with h
  · rfl
  · simp only [Tube]
    rw [show x + v + -v = x by abel, segment_symm]

theorem norm_orDir (w0 v : Space) : ‖orDir w0 v‖ = ‖v‖ := by
  unfold orDir; split_ifs <;> simp

theorem inner_orDir_nonneg (w0 v : Space) : 0 ≤ ⟪orDir w0 v, w0⟫ := by
  unfold orDir
  split_ifs with h
  · exact h
  · rw [inner_neg_left]; linarith

/-- With compatible orientations, containment matches starts with starts. -/
theorem endpoints_close_oriented {δ ρ : ℝ} (hδ : 0 < δ) (hρ : ρ ≤ 1 / 100)
    {x v z w w0 : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hw0 : ‖w0‖ = 1)
    (hvw0 : 1 / 2 ≤ ⟪v, w0⟫) (hww0 : 0 ≤ ⟪w, w0⟫) (hT : Tube δ x v ⊆ Tube ρ z w) :
    ‖x - z‖ ≤ 3 * ρ ∧ ‖x + v - (z + w)‖ ≤ 3 * ρ := by
  rcases endpoints_close hδ hv hw hT with h | ⟨h1, h2⟩
  · exact h
  · exfalso
    have hvw : ‖v + w‖ ≤ 6 * ρ := by
      have he : v + w = (x + v - z) - (x - (z + w)) := by abel
      rw [he]; exact (norm_sub_le _ _).trans (by linarith)
    have hin : ⟪v + w, w0⟫ ≤ 6 * ρ := by
      have := real_inner_le_norm (v + w) w0
      rw [hw0, mul_one] at this; linarith
    rw [inner_add_left] at hin
    linarith

/-- Direction closeness from endpoint closeness. -/
theorem dir_close_of_endpoints {x v z w : Space} {d : ℝ}
    (h0 : ‖x - z‖ ≤ d) (h1 : ‖x + v - (z + w)‖ ≤ d) : ‖v - w‖ ≤ 2 * d := by
  have he : v - w = (x + v - (z + w)) - (x - z) := by abel
  rw [he]; exact (norm_sub_le _ _).trans (by linarith)

/-- Inner product with `w0` of a unit vector close to `w0`. -/
theorem inner_ge_of_close {v w0 : Space} (hw0 : ‖w0‖ = 1) {θ : ℝ} (hvw : ‖v - w0‖ ≤ θ) :
    1 - θ ≤ ⟪v, w0⟫ := by
  have h := real_inner_le_norm (v - w0) w0
  rw [hw0, mul_one, inner_sub_left, real_inner_self_eq_norm_sq, hw0] at h
  have : ⟪v, w0⟫ - 1 ≥ -θ := by
    have h2 := neg_le_of_abs_le (abs_real_inner_le_norm (v - w0) w0)
    rw [hw0, mul_one, inner_sub_left, real_inner_self_eq_norm_sq, hw0] at h2
    linarith
  linarith

/-- Normalized vectors: `‖p/|p| - q/|q|‖ ≤ 2 ‖p - q‖ / ‖p‖`. -/
theorem norm_normalize_sub_le {p q : Space} (hp : 0 < ‖p‖) (hq : 0 < ‖q‖) :
    ‖‖p‖⁻¹ • p - ‖q‖⁻¹ • q‖ ≤ 2 * ‖p - q‖ / ‖p‖ := by
  have he : ‖p‖⁻¹ • p - ‖q‖⁻¹ • q = ‖p‖⁻¹ • (p - q) + (‖p‖⁻¹ - ‖q‖⁻¹) • q := by module
  rw [he]
  have h1 : ‖‖p‖⁻¹ • (p - q)‖ = ‖p - q‖ / ‖p‖ := by
    rw [norm_smul, norm_inv, norm_norm, div_eq_inv_mul]
  have h2 : ‖(‖p‖⁻¹ - ‖q‖⁻¹) • q‖ ≤ ‖p - q‖ / ‖p‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have : ‖p‖⁻¹ - ‖q‖⁻¹ = (‖q‖ - ‖p‖) / (‖p‖ * ‖q‖) := by field_simp
    rw [this, abs_div, abs_of_pos (mul_pos hp hq), div_mul_eq_mul_div,
      mul_div_mul_right _ _ hq.ne']
    apply div_le_div_of_nonneg_right _ hp.le
    rw [abs_sub_comm]
    exact abs_norm_sub_norm_le p q
  calc _ ≤ ‖‖p‖⁻¹ • (p - q)‖ + ‖(‖p‖⁻¹ - ‖q‖⁻¹) • q‖ := norm_add_le _ _
    _ ≤ ‖p - q‖ / ‖p‖ + ‖p - q‖ / ‖p‖ := by rw [h1]; exact add_le_add le_rfl h2
    _ = 2 * ‖p - q‖ / ‖p‖ := by ring

/-- Normalized anisotropic image of a direction. -/
noncomputable def ndir (w0 : Space) (a : ℝ) (v : Space) : Space :=
  ‖aniso w0 a v‖⁻¹ • aniso w0 a v

theorem norm_ndir {w0 v : Space} (hw0 : ‖w0‖ = 1) {a : ℝ} (ha : 1 ≤ a) (hv : ‖v‖ = 1) :
    ‖ndir w0 a v‖ = 1 := by
  have hp : 0 < ‖aniso w0 a v‖ := lt_of_lt_of_le one_pos (hv ▸ norm_le_norm_aniso hw0 ha v)
  rw [ndir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hp.ne']

theorem ndir_sub_le {w0 v w : Space} (hw0 : ‖w0‖ = 1) {a : ℝ} (ha : 1 ≤ a) (hv : ‖v‖ = 1)
    (hw : ‖w‖ = 1) : ‖ndir w0 a v - ndir w0 a w‖ ≤ 2 * a * ‖v - w‖ := by
  have hp : 1 ≤ ‖aniso w0 a v‖ := hv ▸ norm_le_norm_aniso hw0 ha v
  have hq : 1 ≤ ‖aniso w0 a w‖ := hw ▸ norm_le_norm_aniso hw0 ha w
  have h := norm_normalize_sub_le (p := aniso w0 a v) (q := aniso w0 a w) (by linarith)
    (by linarith)
  rw [← map_sub] at h
  calc ‖ndir w0 a v - ndir w0 a w‖ ≤ 2 * ‖aniso w0 a (v - w)‖ / ‖aniso w0 a v‖ := h
    _ ≤ 2 * ‖aniso w0 a (v - w)‖ := by
        apply div_le_self (by positivity) hp
    _ ≤ 2 * (a * ‖v - w‖) := by
        gcongr; exact norm_aniso_le hw0 ha _
    _ = 2 * a * ‖v - w‖ := by ring

/-- Containment of an oriented fine tube in an oriented cover transfers to the
rescaled tubes, with the cover thickened to `17 a ρ''`. -/
theorem resc_subset_cover {δ ρ'' a b : ℝ} (hδ : 0 < δ) (hρ'' : ρ'' ≤ 1 / 100) (ha : 1 ≤ a)
    (hb : 0 < b) (hb1 : b ≤ 1) (hδρ : δ ≤ ρ'') {w0 c0 x v z w : Space} (hw0 : ‖w0‖ = 1)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hvw0 : 1 / 2 ≤ ⟪v, w0⟫) (hww0 : 0 ≤ ⟪w, w0⟫)
    (hT : Tube δ x v ⊆ Tube ρ'' z w) :
    Tube (b * a * δ) (resc w0 c0 a b x) (ndir w0 a v) ⊆
      Tube (17 * a * ρ'') (resc w0 c0 a b z) (ndir w0 a w) := by
  obtain ⟨h0, h1⟩ := endpoints_close_oriented hδ hρ'' hv hw hw0 hvw0 hww0 hT
  have hvw := dir_close_of_endpoints h0 h1
  intro q hq
  obtain ⟨t, ht, hqt⟩ := exists_param_of_mem_Tube hq
  apply mem_Tube_of_param ht
  have hstart : ‖resc w0 c0 a b x - resc w0 c0 a b z‖ ≤ 3 * a * ρ'' := by
    calc _ ≤ b * a * ‖x - z‖ := norm_resc_sub_le hw0 ha hb.le _ _
      _ ≤ 1 * a * (3 * ρ'') := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hb1 (by linarith)) h0 (norm_nonneg _)
            (by positivity)
      _ = 3 * a * ρ'' := by ring
  have hdir : ‖ndir w0 a v - ndir w0 a w‖ ≤ 12 * a * ρ'' := by
    calc _ ≤ 2 * a * ‖v - w‖ := ndir_sub_le hw0 ha hv hw
      _ ≤ 2 * a * (2 * (3 * ρ'')) := by gcongr
      _ = 12 * a * ρ'' := by ring
  have he : q - (resc w0 c0 a b z + t • ndir w0 a w) =
      (q - (resc w0 c0 a b x + t • ndir w0 a v)) +
        (resc w0 c0 a b x - resc w0 c0 a b z) + t • (ndir w0 a v - ndir w0 a w) := by module
  rw [he]
  have hbaδ : b * a * δ ≤ a * ρ'' := by
    calc b * a * δ ≤ 1 * a * ρ'' := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hb1 (by linarith)) hδρ hδ.le
            (by positivity)
      _ = a * ρ'' := by ring
  calc _ ≤ ‖q - (resc w0 c0 a b x + t • ndir w0 a v)‖ +
        ‖resc w0 c0 a b x - resc w0 c0 a b z‖ + ‖t • (ndir w0 a v - ndir w0 a w)‖ :=
        (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ < b * a * δ + 3 * a * ρ'' + 1 * (12 * a * ρ'') := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        have := mul_le_mul ht.2 hdir (norm_nonneg _) zero_le_one
        linarith
    _ ≤ 17 * a * ρ'' := by
        have : 0 < a * ρ'' := mul_pos (by linarith) (hδ.trans_le hδρ)
        linarith

/-- The rescaled fine tube stays in the unit ball. -/
theorem resc_tube_subset_ball {δ ρ a b lam0 : ℝ} (hρ : 0 < ρ) (ha : a = lam0 / ρ) (ha1 : 1 ≤ a)
    (hb : 1 / 2 ≤ b) (hb1 : b ≤ 1) (hlam0 : lam0 ≤ 1 / 100) (hδ' : b * a * δ ≤ lam0)
    {w0 z0 x v : Space} (hw0 : ‖w0‖ = 1) (hv : ‖v‖ = 1)
    (hx : ‖x - z0‖ ≤ 3 * ρ) (hvw : ‖v - w0‖ ≤ 6 * ρ) :
    Tube (b * a * δ) (resc w0 (z0 + (1 / 2 : ℝ) • w0) a b x) (ndir w0 a v) ⊆ ball 0 1 := by
  have hlam0 : 0 < lam0 := by
    have : lam0 = a * ρ := by rw [ha]; field_simp
    rw [this]; positivity
  have haρ : a * ρ = lam0 := by rw [ha]; field_simp
  intro q hq
  obtain ⟨t, ht, hqt⟩ := exists_param_of_mem_Tube hq
  rw [mem_ball_zero_iff]
  have hx' : x - (z0 + (1 / 2 : ℝ) • w0) = -((1 / 2 : ℝ) • w0) + (x - z0) := by abel
  have hstart : resc w0 (z0 + (1 / 2 : ℝ) • w0) a b x =
      (-(b / 2)) • w0 + b • aniso w0 a (x - z0) := by
    simp only [resc, hx', map_add, map_neg, map_smul, aniso_self hw0, smul_add, smul_neg,
      smul_smul]
    congr 1
    rw [← neg_smul]; congr 1; ring
  have hA : ‖aniso w0 a (x - z0)‖ ≤ 3 * lam0 := by
    calc _ ≤ a * ‖x - z0‖ := norm_aniso_le hw0 ha1 _
      _ ≤ a * (3 * ρ) := by gcongr
      _ = 3 * lam0 := by rw [← haρ]; ring
  have hu : ‖ndir w0 a v - w0‖ ≤ 12 * lam0 := by
    have h := ndir_sub_le hw0 ha1 hv hw0 (v := v) (w := w0)
    have hw0' : ndir w0 a w0 = w0 := by
      rw [ndir, aniso_self hw0, hw0, inv_one, one_smul]
    rw [hw0'] at h
    calc _ ≤ 2 * a * ‖v - w0‖ := h
      _ ≤ 2 * a * (6 * ρ) := by gcongr
      _ = 12 * lam0 := by rw [← haρ]; ring
  have he : q = (q - (resc w0 (z0 + (1 / 2 : ℝ) • w0) a b x + t • ndir w0 a v)) +
      ((t - b / 2) • w0 + b • aniso w0 a (x - z0) + t • (ndir w0 a v - w0)) := by
    rw [hstart]; module
  rw [he]
  have h1 : ‖(t - b / 2) • w0‖ ≤ 3 / 4 := by
    rw [norm_smul, hw0, mul_one, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have h2 : ‖b • aniso w0 a (x - z0)‖ ≤ 3 * lam0 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
    calc b * ‖aniso w0 a (x - z0)‖ ≤ 1 * (3 * lam0) :=
          mul_le_mul hb1 hA (norm_nonneg _) zero_le_one
      _ = 3 * lam0 := one_mul _
  have h3 : ‖t • (ndir w0 a v - w0)‖ ≤ 12 * lam0 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc t * ‖ndir w0 a v - w0‖ ≤ 1 * (12 * lam0) := mul_le_mul ht.2 hu (norm_nonneg _) zero_le_one
      _ = 12 * lam0 := one_mul _
  have hsum : ‖(t - b / 2) • w0 + b • aniso w0 a (x - z0) + t • (ndir w0 a v - w0)‖ ≤
      3 / 4 + 3 * lam0 + 12 * lam0 := by
    have k1 := norm_add_le ((t - b / 2) • w0 + b • aniso w0 a (x - z0))
      (t • (ndir w0 a v - w0))
    have k2 := norm_add_le ((t - b / 2) • w0) (b • aniso w0 a (x - z0))
    linarith
  have htot := norm_add_le (q - (resc w0 (z0 + (1 / 2 : ℝ) • w0) a b x + t • ndir w0 a v))
    ((t - b / 2) • w0 + b • aniso w0 a (x - z0) + t • (ndir w0 a v - w0))
  linarith

/-! ### Preimages and packing -/

theorem aniso_inv {w0 : Space} (hw0 : ‖w0‖ = 1) {a : ℝ} (ha : a ≠ 0) (p : Space) :
    aniso w0 a (aniso w0 a⁻¹ p) = p := by
  have hww : ⟪w0, w0⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw0]; norm_num
  simp only [aniso_apply, inner_add_right, real_inner_smul_right, hww]
  have : a * (1 - a⁻¹) + (1 - a) * (a⁻¹ + (1 - a⁻¹)) = 0 := by field_simp; ring
  calc a • (a⁻¹ • p + (1 - a⁻¹) • (⟪w0, p⟫ • w0)) +
        (1 - a) • ((a⁻¹ * ⟪w0, p⟫ + (1 - a⁻¹) * (⟪w0, p⟫ * 1)) • w0)
      = (a * a⁻¹) • p + ((a * (1 - a⁻¹) + (1 - a) * (a⁻¹ + (1 - a⁻¹))) * ⟪w0, p⟫) • w0 := by
        module
    _ = p := by rw [mul_inv_cancel₀ ha, this]; simp

theorem resc_surjective {w0 c0 : Space} (hw0 : ‖w0‖ = 1) {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Function.Surjective (resc w0 c0 a b) := by
  intro q
  refine ⟨c0 + aniso w0 a⁻¹ (b⁻¹ • q), ?_⟩
  simp only [resc, add_sub_cancel_left, aniso_inv hw0 ha, smul_smul, mul_inv_cancel₀ hb,
    one_smul]

/-- Volumes of preimages under the rescaling. -/
theorem volume_preimage_resc {w0 c0 : Space} (hw0 : ‖w0‖ = 1) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (S : Set Space) :
    ENNReal.ofReal (b ^ 3 * a ^ 2) * volume (resc w0 c0 a b ⁻¹' S) = volume S := by
  rw [← volume_image_resc hw0 hb.le, Set.image_preimage_eq _ (resc_surjective hw0 ha.ne' hb.ne')]

/-- Packing of half-distinct tubes inside a set of bounded volume. -/
theorem card_le_of_subset_vol {k : ℕ} {r V : ℝ} (hr : 0 < r) (hV : 0 ≤ V)
    (z w : Fin k → Space) (hw : ∀ j, ‖w j‖ = 1)
    (hsep : ∀ j j', j ≠ j' → volume (Tube r (z j) (w j) ∩ Tube r (z j') (w j')) ≤
      (1 / 2 : ℝ≥0∞) * volume (Tube r (z j) (w j)))
    (W : Set Space) (hW : volume W ≤ ENNReal.ofReal (V * r ^ 2)) (S : Finset (Fin k))
    (hS : ∀ j ∈ S, Tube r (z j) (w j) ⊆ W) :
    (S.card : ℝ) ≤ 1000000 * V ^ 2 := by
  classical
  let e : Fin S.card → Fin k := fun a => (S.equivFin.symm a).val
  have he : Function.Injective e := Subtype.val_injective.comp S.equivFin.symm.injective
  have hpack := WangZahlLot.Obl.wz_convex_container_tube_packing.packing hr
    (fun a => z (e a)) (fun a => w (e a))
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hW) (fun a => hw (e a))
    (fun a => hS _ (S.equivFin.symm a).property)
    (fun a b hab => hsep (e a) (e b) (he.ne hab))
  have hle : ENNReal.ofReal ((S.card : ℝ) * r ^ 4) ≤
      ENNReal.ofReal (1000000 * V ^ 2 * r ^ 4) := by
    calc _ ≤ ENNReal.ofReal 1000000 * (volume W) ^ 2 := hpack
      _ ≤ ENNReal.ofReal 1000000 * (ENNReal.ofReal (V * r ^ 2)) ^ 2 := by gcongr
      _ = ENNReal.ofReal (1000000 * V ^ 2 * r ^ 4) := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
  have hr4 : 0 < r ^ 4 := by positivity
  nlinarith

theorem ntube_zero (r : ℝ) (z w : Space) : ntube r 0 z w = Tube r z w := by
  simp [ntube]

/-- Preimage of a big container under the rescaling has controlled volume. -/
theorem volume_preimage_bigContainer {w0 c0 z w : Space} (hw0 : ‖w0‖ = 1) (hw : ‖w‖ = 1)
    {a b R : ℝ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R) (hR1 : R ≤ 1 / 10000000) :
    volume (resc w0 c0 a b ⁻¹' bigContainer R z w) ≤
      ENNReal.ofReal (10 ^ 23 * R ^ 2 / (b ^ 3 * a ^ 2)) := by
  have h := volume_preimage_resc hw0 ha hb (c0 := c0) (bigContainer R z w)
  have hv := bigContainer_volume hR hR1 z w hw
  have hpos : 0 < b ^ 3 * a ^ 2 := by positivity
  rw [← h] at hv
  have hfin : volume (resc w0 c0 a b ⁻¹' bigContainer R z w) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top (by simp [hpos])] at hv
    exact absurd hv (not_le.mpr ENNReal.ofReal_lt_top)
  rw [← ENNReal.ofReal_toReal hfin] at hv ⊢
  rw [← ENNReal.ofReal_mul hpos.le] at hv
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hv
  apply ENNReal.ofReal_le_ofReal
  rw [le_div_iff₀ hpos]
  linarith

/-- A tube oriented along `w0` inside the coarse tube along `w0` starts at its start. -/
theorem oriented_in_coarse {δ ρ : ℝ} (hδ : 0 < δ) (hρ : ρ ≤ 1 / 100) {x v z0 w0 : Space}
    (hv : ‖v‖ = 1) (hw0 : ‖w0‖ = 1) (hvw0 : 0 ≤ ⟪v, w0⟫) (hT : Tube δ x v ⊆ Tube ρ z0 w0) :
    ‖x - z0‖ ≤ 3 * ρ ∧ ‖x + v - (z0 + w0)‖ ≤ 3 * ρ := by
  rcases endpoints_close hδ hv hw0 hT with h | ⟨h1, h2⟩
  · exact h
  · exfalso
    have hvw : ‖v + w0‖ ≤ 6 * ρ := by
      have he : v + w0 = (x + v - z0) - (x - (z0 + w0)) := by abel
      rw [he]; exact (norm_sub_le _ _).trans (by linarith)
    have hin : ⟪v + w0, w0⟫ ≤ 6 * ρ := by
      have := real_inner_le_norm (v + w0) w0
      rw [hw0, mul_one] at this; linarith
    rw [inner_add_left, real_inner_self_eq_norm_sq, hw0] at hin
    linarith

/-- Element conflicts of rescaled tubes have bounded degree. -/
theorem resc_elem_conflict_card {nF : ℕ} {δ a b : ℝ} (hδ : 0 < δ) (ha : 1 ≤ a) (hb : 1 / 2 ≤ b)
    (hb1 : b ≤ 1) (hδ' : b * a * δ ≤ 1 / 10000000) {w0 c0 : Space} (hw0 : ‖w0‖ = 1)
    (x v : Fin nF → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hhalf : ∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
      (1 / 2 : ℝ≥0∞) * volume (Tube δ (x i) (v i)))
    (hbL : ∀ i, b * ‖aniso w0 a (v i)‖ ≤ 1)
    (hball : ∀ i, Tube (b * a * δ) (resc w0 c0 a b (x i)) (ndir w0 a (v i)) ⊆ ball 0 1)
    (i : Fin nF) :
    ((Finset.univ.filter (fun j => elemConflict (b * a * δ) 0
      (fun j => resc w0 c0 a b (x j)) (fun j => ndir w0 a (v j)) i j)).card : ℝ) ≤
      10 ^ 53 := by
  classical
  have hδ'0 : 0 < b * a * δ := by positivity
  have hax : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖resc w0 c0 a b (x j) + t • ndir w0 a (v j)‖ ≤ 2 := by
    intro j t ht
    have := hball j (axis_mem_Tube hδ'0 _ _ ht)
    rw [mem_ball_zero_iff] at this; linarith
  set W := resc w0 c0 a b ⁻¹' bigContainer (b * a * δ) (resc w0 c0 a b (x i)) (ndir w0 a (v i))
  have hW : volume W ≤ ENNReal.ofReal ((10 ^ 23 / b) * δ ^ 2) := by
    have h := volume_preimage_bigContainer (c0 := c0) hw0 (norm_ndir hw0 ha (hv i))
      (by linarith : 0 < a) (by linarith : 0 < b) hδ'0 hδ' (z := resc w0 c0 a b (x i))
    refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    field_simp
  have hsub : ∀ j ∈ Finset.univ.filter (fun j => elemConflict (b * a * δ) 0
      (fun j => resc w0 c0 a b (x j)) (fun j => ndir w0 a (v j)) i j),
      Tube δ (x j) (v j) ⊆ W := by
    intro j hj
    have hc := (Finset.mem_filter.mp hj).2
    have hzi : ‖resc w0 c0 a b (x i)‖ ≤ 2 := by simpa using hax i 0 ⟨le_rfl, zero_le_one⟩
    have hcont := overlap_container (ρ0 := b * a * δ) hδ'0 hδ' le_rfl (by norm_num) hδ'0
      (by linarith) (by positivity) (norm_ndir hw0 ha (hv i)) (norm_ndir hw0 ha (hv j))
      (by simpa using hzi) (by simpa using hax j) (by simpa only [ntube_zero] using hc.2)
    intro p hp
    have hp' : resc w0 c0 a b p ∈ Tube (b * a * δ) (resc w0 c0 a b (x j)) (ndir w0 a (v j)) :=
      resc_tube_subset hw0 ha (by linarith) (hbL j)
        (lt_of_lt_of_le one_pos ((hv j) ▸ norm_le_norm_aniso hw0 ha (v j))) ⟨p, hp, rfl⟩
    exact hcont (by simpa using hp')
  have h := card_le_of_subset_vol hδ (by positivity) x v hv hhalf W hW _ hsub
  have hb' : 10 ^ 23 / b ≤ 2 * 10 ^ 23 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  calc _ ≤ 1000000 * (10 ^ 23 / b) ^ 2 := h
    _ ≤ 1000000 * (2 * 10 ^ 23) ^ 2 := by gcongr
    _ ≤ 10 ^ 53 := by norm_num

/-- Conflicts of rescaled covers: only between covers that are hit. -/
def rescCoverConflict {nF K : ℕ} (s R : ℝ) (X U : Fin nF → Space) (Z V : Fin K → Space)
    (hit : Fin K → Prop) (m m' : Fin K) : Prop :=
  m ≠ m' ∧ hit m ∧ hit m' ∧
    ((1 / 2 : ℝ≥0∞) * volume (Tube R (Z m) (V m)) <
        volume (Tube R (Z m) (V m) ∩ Tube R (Z m') (V m')) ∨
      (1 / 2 : ℝ≥0∞) * volume (Tube R (Z m') (V m')) <
        volume (Tube R (Z m') (V m') ∩ Tube R (Z m) (V m)) ∨
      ∃ i, Tube s (X i) (U i) ⊆ Dilate R (Z m) (V m) ∧ Tube s (X i) (U i) ⊆ Dilate R (Z m') (V m'))

theorem rescCoverConflict_symm {nF K : ℕ} {s R : ℝ} {X U : Fin nF → Space} {Z V : Fin K → Space}
    {hit : Fin K → Prop} {m m' : Fin K} (h : rescCoverConflict s R X U Z V hit m m') :
    rescCoverConflict s R X U Z V hit m' m := by
  obtain ⟨hne, h1, h2, h3 | h3 | ⟨i, hi, hi'⟩⟩ := h
  · exact ⟨Ne.symm hne, h2, h1, Or.inr (Or.inl h3)⟩
  · exact ⟨Ne.symm hne, h2, h1, Or.inl h3⟩
  · exact ⟨Ne.symm hne, h2, h1, Or.inr (Or.inr ⟨i, hi', hi⟩)⟩

/-- Rescaled cover conflicts have bounded degree. -/
theorem resc_cover_conflict_card {nF K : ℕ} {s ρ'' a b : ℝ} (hs : 0 < s) (hρ'' : 0 < ρ'')
    (ha : 1 ≤ a) (hb : 1 / 2 ≤ b) (hb1 : b ≤ 1) (hR : 17 * a * ρ'' ≤ 1 / 10000000)
    {w0 c0 : Space} (hw0 : ‖w0‖ = 1)
    (X U : Fin nF → Space) (hU : ∀ i, ‖U i‖ = 1)
    (z w : Fin K → Space) (hw : ∀ m, ‖w m‖ = 1)
    (hsep : ∀ m m', m ≠ m' → volume (Tube ρ'' (z m) (w m) ∩ Tube ρ'' (z m') (w m')) ≤
      (1 / 2 : ℝ≥0∞) * volume (Tube ρ'' (z m) (w m)))
    (hit : Fin K → Prop)
    (hbL : ∀ m, hit m → b * ‖aniso w0 a (w m)‖ ≤ 1)
    (hax : ∀ m, hit m → ∀ t ∈ Icc (0 : ℝ) 1,
      ‖resc w0 c0 a b (z m) + t • ndir w0 a (w m)‖ ≤ 2)
    (m : Fin K) :
    ((Finset.univ.filter (rescCoverConflict s (17 * a * ρ'') X U
      (fun m => resc w0 c0 a b (z m)) (fun m => ndir w0 a (w m)) hit m)).card : ℝ) ≤
      10 ^ 61 := by
  classical
  set R := 17 * a * ρ''
  have hR0 : 0 < R := by positivity
  by_cases hm : hit m
  swap
  · have hempty : Finset.univ.filter (rescCoverConflict s R X U
        (fun m => resc w0 c0 a b (z m)) (fun m => ndir w0 a (w m)) hit m) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun m' _ h => hm h.2.1)
    rw [hempty]; simp
  set W := resc w0 c0 a b ⁻¹' bigContainer R (resc w0 c0 a b (z m)) (ndir w0 a (w m))
  have hW : volume W ≤ ENNReal.ofReal ((289 * 10 ^ 23 / b ^ 3) * ρ'' ^ 2) := by
    have h := volume_preimage_bigContainer (c0 := c0) hw0 (norm_ndir hw0 ha (hw m))
      (by linarith : 0 < a) (by linarith : 0 < b) hR0 hR (z := resc w0 c0 a b (z m))
    refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    simp only [R]
    field_simp
    ring
  have hzm : ‖resc w0 c0 a b (z m)‖ ≤ 2 := by simpa using hax m hm 0 ⟨le_rfl, zero_le_one⟩
  have hsub : ∀ m' ∈ Finset.univ.filter (rescCoverConflict s R X U
      (fun m => resc w0 c0 a b (z m)) (fun m => ndir w0 a (w m)) hit m),
      Tube ρ'' (z m') (w m') ⊆ W := by
    intro m' hm'
    obtain ⟨-, -, hm'hit, hc⟩ := (Finset.mem_filter.mp hm').2
    have hcont : Tube R (resc w0 c0 a b (z m')) (ndir w0 a (w m')) ⊆
        bigContainer R (resc w0 c0 a b (z m)) (ndir w0 a (w m)) := by
      rcases hc with h1 | h2 | ⟨i, hi, hi'⟩
      · exact overlap_container hR0 hR le_rfl (by norm_num) hR0 (by linarith) (by positivity)
          (norm_ndir hw0 ha (hw m)) (norm_ndir hw0 ha (hw m')) (by simpa using hzm)
          (by simpa using hax m' hm'hit) (Or.inl (by simpa only [ntube_zero] using h1))
      · exact overlap_container hR0 hR le_rfl (by norm_num) hR0 (by linarith) (by positivity)
          (norm_ndir hw0 ha (hw m)) (norm_ndir hw0 ha (hw m')) (by simpa using hzm)
          (by simpa using hax m' hm'hit) (Or.inr (by simpa only [ntube_zero] using h2))
      · have hp0 := axis_mem_Tube hs (X i) (U i) (t := 0) ⟨le_rfl, zero_le_one⟩
        have hp1 := axis_mem_Tube hs (X i) (U i) (t := 1) ⟨zero_le_one, le_rfl⟩
        simp only [zero_smul, add_zero, one_smul] at hp0 hp1
        exact dilate_conflict_container hR0 (by linarith) le_rfl (by norm_num) hR0
          (by linarith) (by positivity) (hU i) (norm_ndir hw0 ha (hw m))
          (norm_ndir hw0 ha (hw m')) (by simpa using hzm) (by simpa using hax m' hm'hit)
          (by simpa using hi hp0) (by simpa using hi hp1) (by simpa using hi' hp0)
          (by simpa using hi' hp1)
    intro p hp
    have himg := resc_tube_subset (c0 := c0) hw0 ha (by linarith) (hbL m' hm'hit)
      (lt_of_lt_of_le one_pos ((hw m') ▸ norm_le_norm_aniso hw0 ha (w m'))) ⟨p, hp, rfl⟩
    have hthick : Tube (b * a * ρ'') (resc w0 c0 a b (z m')) (ndir w0 a (w m')) ⊆
        Tube R (resc w0 c0 a b (z m')) (ndir w0 a (w m')) :=
      thickening_mono (by simp only [R]; nlinarith) _
    exact hcont (hthick (by simpa [ndir] using himg))
  have h := card_le_of_subset_vol hρ'' (by positivity) z w hw hsep W hW _ hsub
  have hb3 : 289 * 10 ^ 23 / b ^ 3 ≤ 2312 * 10 ^ 23 := by
    rw [div_le_iff₀ (by positivity)]
    have : (1 / 2 : ℝ) ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ (by norm_num) hb 3
    nlinarith
  calc _ ≤ 1000000 * (289 * 10 ^ 23 / b ^ 3) ^ 2 := h
    _ ≤ 1000000 * (2312 * 10 ^ 23) ^ 2 := by gcongr
    _ ≤ 10 ^ 61 := by norm_num

/-- Axes of rescaled fine tubes and their rescaled covers stay close. -/
theorem resc_axis_close {δ ρ'' a b : ℝ} (hδ : 0 < δ) (hρ'' : ρ'' ≤ 1 / 100) (ha : 1 ≤ a)
    (hb : 0 < b) (hb1 : b ≤ 1) {w0 c0 x v z w : Space} (hw0 : ‖w0‖ = 1)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hvw0 : 1 / 2 ≤ ⟪v, w0⟫) (hww0 : 0 ≤ ⟪w, w0⟫)
    (hT : Tube δ x v ⊆ Tube ρ'' z w) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖(resc w0 c0 a b z + t • ndir w0 a w) - (resc w0 c0 a b x + t • ndir w0 a v)‖ ≤
      15 * a * ρ'' := by
  obtain ⟨h0, h1⟩ := endpoints_close_oriented hδ hρ'' hv hw hw0 hvw0 hww0 hT
  have hvw := dir_close_of_endpoints h0 h1
  have hstart : ‖resc w0 c0 a b z - resc w0 c0 a b x‖ ≤ 3 * a * ρ'' := by
    calc _ ≤ b * a * ‖z - x‖ := norm_resc_sub_le hw0 ha hb.le _ _
      _ ≤ 1 * a * (3 * ρ'') := by
          rw [norm_sub_rev]
          apply mul_le_mul (mul_le_mul_of_nonneg_right hb1 (by linarith)) h0 (norm_nonneg _)
            (by positivity)
      _ = 3 * a * ρ'' := by ring
  have hdir : ‖ndir w0 a w - ndir w0 a v‖ ≤ 12 * a * ρ'' := by
    rw [norm_sub_rev]
    calc _ ≤ 2 * a * ‖v - w‖ := ndir_sub_le hw0 ha hv hw
      _ ≤ 2 * a * (2 * (3 * ρ'')) := by gcongr
      _ = 12 * a * ρ'' := by ring
  have he : (resc w0 c0 a b z + t • ndir w0 a w) - (resc w0 c0 a b x + t • ndir w0 a v) =
      (resc w0 c0 a b z - resc w0 c0 a b x) + t • (ndir w0 a w - ndir w0 a v) := by module
  rw [he]
  have h2 : ‖t • (ndir w0 a w - ndir w0 a v)‖ ≤ 12 * a * ρ'' := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc t * _ ≤ 1 * (12 * a * ρ'') := mul_le_mul ht.2 hdir (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have := norm_add_le (resc w0 c0 a b z - resc w0 c0 a b x) (t • (ndir w0 a w - ndir w0 a v))
  linarith

/-- The rescaling is affine. -/
theorem resc_combo (w0 c0 : Space) (a b : ℝ) (p q : Space) {s t : ℝ} (hst : s + t = 1) :
    resc w0 c0 a b (s • p + t • q) = s • resc w0 c0 a b p + t • resc w0 c0 a b q := by
  have hc : s • p + t • q - c0 = s • (p - c0) + t • (q - c0) := by
    have : c0 = (s + t) • c0 := by rw [hst, one_smul]
    conv_lhs => rw [this]
    module
  simp only [resc, hc, map_add, map_smul, smul_add, smul_comm b s, smul_comm b t]

theorem convex_preimage_resc {W : Set Space} (hW : Convex ℝ W) (w0 c0 : Space) (a b : ℝ) :
    Convex ℝ (resc w0 c0 a b ⁻¹' W) := by
  intro p hp q hq s t hs ht hst
  simp only [mem_preimage] at hp hq ⊢
  rw [resc_combo w0 c0 a b p q hst]
  exact hW hp hq hs ht hst

/-- The image of a measurable set under the rescaling is measurable. -/
theorem measurableSet_image_resc {w0 c0 : Space} (hw0 : ‖w0‖ = 1) {a b : ℝ} (ha : a ≠ 0)
    (hb : b ≠ 0) {S : Set Space} (hS : MeasurableSet S) :
    MeasurableSet (resc w0 c0 a b '' S) := by
  have he : resc w0 c0 a b '' S = (fun q => c0 + aniso w0 a⁻¹ (b⁻¹ • q)) ⁻¹' S := by
    ext q
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨p, hp, rfl⟩
      have : c0 + aniso w0 a⁻¹ (b⁻¹ • resc w0 c0 a b p) = p := by
        simp only [resc, smul_smul, inv_mul_cancel₀ hb, one_smul]
        have h := aniso_inv hw0 (inv_ne_zero ha) (p - c0)
        rw [inv_inv] at h
        rw [h]; abel
      rw [this]; exact hp
    · intro hq
      refine ⟨_, hq, ?_⟩
      simp only [resc, add_sub_cancel_left, aniso_inv hw0 ha, smul_smul, mul_inv_cancel₀ hb,
        one_smul]
  rw [he]
  have hc : Continuous (fun q : Space => c0 + aniso w0 a⁻¹ (b⁻¹ • q)) := by
    have h1 : Continuous (fun q : Space => b⁻¹ • q) := continuous_const_smul _
    exact continuous_const.add ((aniso w0 a⁻¹).continuous.comp h1)
  exact hS.preimage hc.measurable

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse
