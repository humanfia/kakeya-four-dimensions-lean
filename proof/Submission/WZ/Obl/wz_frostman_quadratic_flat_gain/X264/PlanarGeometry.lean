-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.PlanarGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Geometry
import Submission.WZ.Obl.wz_off_stem_brush_overlap.Geometry
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file PlanarGeometry.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_off_stem_brush_overlap (angle adapted_basis inner_angle inner_tube_difference)

lemma prism_norm_sub_le {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 1)
    {c e₁ e₂ e₃ p : Space} (he : Orthonormal ℝ ![e₁, e₂, e₃])
    (hp : p ∈ prism a b c e₁ e₂ e₃) : ‖p - c‖ ≤ 2 := by
  have h₁ : |inner ℝ e₁ (p - c)| ≤ 1 := hp.1.trans (hab.trans hb)
  have h₂ : |inner ℝ e₂ (p - c)| ≤ 1 := hp.2.1.trans hb
  have h₃ : |inner ℝ e₃ (p - c)| ≤ 1 := hp.2.2
  have hsq := WangZahlLot.Obl.wz_transverse_cell_weighted_cover.norm_sq_frame he (p - c)
  change ‖p - c‖ ^ 2 = inner ℝ e₁ (p - c) ^ 2 +
    inner ℝ e₂ (p - c) ^ 2 + inner ℝ e₃ (p - c) ^ 2 at hsq
  have h₁' := sq_le_sq₀ (abs_nonneg (inner ℝ e₁ (p - c))) (by norm_num : (0 : ℝ) ≤ 1)
  have h₂' := sq_le_sq₀ (abs_nonneg (inner ℝ e₂ (p - c))) (by norm_num : (0 : ℝ) ≤ 1)
  have h₃' := sq_le_sq₀ (abs_nonneg (inner ℝ e₃ (p - c))) (by norm_num : (0 : ℝ) ≤ 1)
  simp only [sq_abs, one_pow] at h₁' h₂' h₃'
  nlinarith [h₁'.mpr h₁, h₂'.mpr h₂, h₃'.mpr h₃, norm_nonneg (p - c)]

lemma translated_slab_convex (u c : Space) (r : ℝ) :
    Convex ℝ {p | |inner ℝ u (p - c)| ≤ r} := by
  have heq : {p | |inner ℝ u (p - c)| ≤ r} =
      (fun p => inner ℝ u p) ⁻¹' Icc (inner ℝ u c - r) (inner ℝ u c + r) := by
    ext p
    simp only [mem_setOf_eq, mem_preimage, mem_Icc, inner_sub_right, abs_le]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  rw [heq]
  exact (convex_Icc _ _).linear_preimage (innerₛₗ ℝ u)

/-- Tubes meeting one thickened tube in a small angular cap fit inside a thin
convex container of volume `64 a theta`. The thin width comes from the common prism. -/
lemma planar_cap_container {a b δ r θ : ℝ} (hab : a ≤ b) (hb : b ≤ 1)
    (hδr : δ ≤ r) (hrθ : r ≤ θ) {c e₁ e₂ e₃ x v : Space}
    (he : Orthonormal ℝ ![e₁, e₂, e₃]) :
    ∃ U : Set Space, Convex ℝ U ∧ volume U ≤ ENNReal.ofReal (64 * a * θ) ∧
      ∀ y w : Space, tube δ y w ⊆ prism a b c e₁ e₂ e₃ →
        (tube r x v ∩ tube r y w).Nonempty → angle v w ≤ θ → tube δ y w ⊆ U := by
  obtain ⟨q, _, hqe, hqv⟩ := adapted_basis e₁ v
  let u := q 2
  have hu : ‖u‖ = 1 := q.norm_eq_one 2
  have he₁ : ‖e₁‖ = 1 := he.norm_eq_one 0
  have heu : inner ℝ e₁ u = 0 := by rw [real_inner_comm]; exact hqe
  obtain ⟨z, hz⟩ := WangZahlLot.Obl.wz_transverse_cell_weighted_cover.exists_frame he₁ hu heu
  let U : Set Space := {p | |inner ℝ e₁ (p - c)| ≤ a ∧
    |inner ℝ z (p - c)| ≤ 2 ∧ |inner ℝ u (p - x)| ≤ 4 * θ}
  refine ⟨U, (translated_slab_convex e₁ c a).inter
    ((translated_slab_convex z c 2).inter (translated_slab_convex u x (4 * θ))), ?_, ?_⟩
  · have h := WangZahlLot.Obl.wz_transverse_cell_weighted_cover.volume_le_of_coords
      hz ![c, c, x] ![a, 2, 4 * θ] U (by
        intro p hp k
        fin_cases k
        · exact hp.1
        · exact hp.2.1
        · exact hp.2.2)
    convert h using 1
    congr 1
    simp
    ring
  · intro y w hP hmeet hangle p hp
    obtain ⟨q₀, hqi, hqj⟩ := hmeet
    have hpP := hP hp
    refine ⟨hpP.1, ?_, ?_⟩
    · have hz1 : ‖z‖ = 1 := hz.norm_eq_one 1
      have hnorm := abs_real_inner_le_norm z (p - c)
      rw [hz1, one_mul] at hnorm
      exact hnorm.trans (prism_norm_sub_le hab hb he hpP)
    · have hpr : p ∈ tube r y w := thickening_mono hδr _ hp
      have hdiff := inner_tube_difference hu hpr hqj
      have hdir := inner_angle hu hqv hangle
      have hqi' := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.tube_subset_slab hu hqv x r hqi
      change |inner ℝ u q₀ - inner ℝ u x| ≤ r at hqi'
      change |inner ℝ u (p - x)| ≤ 4 * θ
      rw [inner_sub_right]
      calc
        _ ≤ |inner ℝ u p - inner ℝ u q₀| + |inner ℝ u q₀ - inner ℝ u x| :=
          abs_sub_le _ _ _
        _ ≤ 4 * θ := by linarith

/-- Frostman below and the flat prism improve the angular cap count by a factor `1/b`. -/
lemma planar_cap_count {a b δ r θ D : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1)
    (hδr : δ ≤ r) (hr : 0 < r) (hrθ : r ≤ θ) (hD : 0 ≤ D) {n : ℕ}
    (x v : Fin n → Space) {c e₁ e₂ e₃ : Space}
    (he : Orthonormal ℝ ![e₁, e₂, e₃])
    (hP : ∀ i, tube δ (x i) (v i) ⊆ prism a b c e₁ e₂ e₃)
    (hcount : ∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal (Set.ncard {i | tube δ (x i) (v i) ⊆ U} : ℝ) *
        volume (prism a b c e₁ e₂ e₃) ≤ ENNReal.ofReal (D * n) * volume U)
    (i : Fin n) (F : Finset (Fin n))
    (hF : ∀ j ∈ F, (tube r (x i) (v i) ∩ tube r (x j) (v j)).Nonempty ∧ angle (v i) (v j) ≤ θ) :
    (F.card : ℝ) ≤ (8 * D * n / b) * θ := by
  have hb0 : 0 < b := ha.trans_le hab
  obtain ⟨U, hUc, hUvol, hUF⟩ := planar_cap_container hab hb hδr hrθ (x := x i) (v := v i) he
  have hn : F.card ≤ Set.ncard {j | tube δ (x j) (v j) ⊆ U} := by
    rw [← Set.ncard_coe_finset]
    apply Set.ncard_mono
    intro j hj
    exact hUF (x j) (v j) (hP j) (hF j hj).1 (hF j hj).2
  have hc := hcount U hUc
  have hbound : ENNReal.ofReal ((F.card : ℝ) * (8 * a * b)) ≤
      ENNReal.ofReal (D * n * (64 * a * θ)) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← prism_volume ha.le hb0.le c e₁ e₂ e₃ he]
    calc
      _ ≤ _ := (mul_le_mul' (ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr hn)) le_rfl).trans hc
      _ ≤ ENNReal.ofReal (D * n) * ENNReal.ofReal (64 * a * θ) := by gcongr
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  have hθ : 0 ≤ θ := hr.le.trans hrθ
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ D * n * (64 * a * θ))).mp hbound
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < 8 * a * b)).mp
  calc
    _ ≤ _ := hreal
    _ = ((8 * D * n / b) * θ) * (8 * a * b) := by field_simp <;> ring

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
