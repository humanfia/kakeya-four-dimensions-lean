-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_concentrated_convex_factorization.Enclosure.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Prism

namespace WangZahlLot.Obl.wz_concentrated_convex_factorization

open Set MeasureTheory Metric
open scoped ENNReal

noncomputable section

lemma frame_pair {v u : Space} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1)
    (hvu : inner ℝ v u = 0) : ∃ b : Frame, b 0 = v ∧ b 1 = u := by
  have huv : inner ℝ u v = 0 := by rw [real_inner_comm]; exact hvu
  let f : Fin 3 → Space := ![v, u, 0]
  have ho : Orthonormal ℝ (({0, 1} : Set (Fin 3)).domRestrict f) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp [f, Set.domRestrict, hv, hu, hvu, huv]
  obtain ⟨b, hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq
    (by simp [Space])
  exact ⟨b, hb 0 (by simp), hb 1 (by simp)⟩

/-- A volume-controlled prism enclosure, using a unit segment and transverse determinants. -/
theorem enclose_convex {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    {U : Set Space} (hU : Convex ℝ U) (hfinite : volume U ≠ ⊤)
    {x v : Space} (hv : ‖v‖ = 1)
    (hTU : Tube δ x v ⊆ U ∩ ball (0 : Space) 1) :
    ∃ (b : Frame) (a c : ℝ), δ ≤ a ∧ a ≤ c ∧ c ≤ 2 ∧
      U ∩ ball (0 : Space) 1 ⊆ prism b x a c ∧ a * c ≤ 512 * (volume U).toReal := by
  classical
  let K := U ∩ ball (0 : Space) 1
  have hx : x ∈ K := hTU ((self_subset_thickening hδ _) (left_mem_segment ℝ x (x + v)))
  have hxv : x + v ∈ U := (hTU ((self_subset_thickening hδ _)
    (right_mem_segment ℝ x (x + v)))).1
  have hnorm (p : Space) (hp : p ∈ K) : ‖p - x‖ ≤ 2 := by
    have hp1 : ‖p‖ < 1 := by simpa using hp.2
    have hx1 : ‖x‖ < 1 := by simpa using hx.2
    exact (norm_sub_le p x).trans (by linarith)
  have hball : ball x δ ⊆ K := (ball_subset_thickening (left_mem_segment ℝ x (x + v)) δ).trans hTU
  have probe (u : Space) (hu : ‖u‖ = 1) : x + (δ / 2) • u ∈ K := by
    apply hball
    rw [mem_ball, dist_eq_norm]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hu, mul_one,
      abs_of_pos (half_pos hδ)]
    linarith
  let D : Set ℝ := (fun p => ‖transverse v (p - x)‖) '' K
  have hD : D.Nonempty := ⟨_, x, hx, rfl⟩
  have hDb : BddAbove D := by
    refine ⟨2, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact (transverse_norm_le hv _).trans (hnorm p hp)
  let r := sSup D
  have hrle : r ≤ 2 := by
    apply csSup_le hD
    rintro _ ⟨p, hp, rfl⟩
    exact (transverse_norm_le hv _).trans (hnorm p hp)
  have hproj (p : Space) (hp : p ∈ K) : ‖transverse v (p - x)‖ ≤ r :=
    le_csSup hDb ⟨p, hp, rfl⟩
  obtain ⟨u₀, hu₀, hu₀v⟩ :=
    WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.exists_unit_perp hv
  have hvu₀ : inner ℝ v u₀ = 0 := by rw [real_inner_comm]; exact hu₀v
  have hrδ : δ / 2 ≤ r := by
    have hh := hproj (x + (δ / 2) • u₀) (probe u₀ hu₀)
    have he : transverse v ((x + (δ / 2) • u₀) - x) = (δ / 2) • u₀ := by
      simp [transverse, inner_smul_right, hvu₀]
    rw [he] at hh
    simpa [norm_smul, hu₀, abs_of_pos (half_pos hδ), abs_of_pos hδ] using hh
  have hr : 0 < r := (half_pos hδ).trans_le hrδ
  obtain ⟨t, ⟨y, hy, rfl⟩, hys⟩ := (lt_csSup_iff hDb hD).mp
    (show r / 2 < sSup D by dsimp [r] at *; linarith)
  let w := transverse v (y - x)
  have hw : 0 < ‖w‖ := (half_pos hr).trans hys
  let u := ‖w‖⁻¹ • w
  have hu : ‖u‖ = 1 := by
    change ‖‖w‖⁻¹ • w‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw), inv_mul_cancel₀ hw.ne']
  have hvu : inner ℝ v u = 0 := by
    simp only [u, inner_smul_right, w, transverse_inner hv, mul_zero]
  obtain ⟨b, hb0, hb1⟩ := frame_pair hv hu hvu
  have hb2v : inner ℝ (b 2) v = 0 := by
    rw [← hb0, orthonormal_iff_ite.mp b.orthonormal]
    norm_num
  have hb1v : inner ℝ (b 1) v = 0 := by
    rw [← hb0, orthonormal_iff_ite.mp b.orthonormal]
    norm_num
  have hydecomp : y - x = inner ℝ v (y - x) • b 0 + ‖w‖ • b 1 := by
    rw [hb0, hb1]
    simp only [u, smul_smul, mul_inv_cancel₀ hw.ne', one_smul]
    dsimp [w, transverse]
    module
  have hy1 : inner ℝ (b 1) (y - x) = ‖w‖ := by
    rw [hydecomp]
    simp [inner_add_right, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
  have hy2 : inner ℝ (b 2) (y - x) = 0 := by
    rw [hydecomp]
    simp [inner_add_right, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
  let E : Set ℝ := (fun p => |inner ℝ (b 2) (p - x)|) '' K
  have hE : E.Nonempty := ⟨_, x, hx, rfl⟩
  have hEb : BddAbove E := by
    refine ⟨r, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact (abs_inner_le_transverse (b.norm_eq_one 2) hb2v _).trans (hproj p hp)
  let s := sSup E
  have hsle : s ≤ r := by
    apply csSup_le hE
    rintro _ ⟨p, hp, rfl⟩
    exact (abs_inner_le_transverse (b.norm_eq_one 2) hb2v _).trans (hproj p hp)
  have hsproj (p : Space) (hp : p ∈ K) : |inner ℝ (b 2) (p - x)| ≤ s :=
    le_csSup hEb ⟨p, hp, rfl⟩
  have hsδ : δ / 2 ≤ s := by
    have hh := hsproj (x + (δ / 2) • b 2) (probe (b 2) (b.norm_eq_one 2))
    simpa [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal,
      abs_of_pos (half_pos hδ)] using hh
  have hs : 0 < s := (half_pos hδ).trans_le hsδ
  have hdet (p : Space) (hp : p ∈ K) :
      ‖w‖ * |inner ℝ (b 2) (p - x)| ≤ 64 * (volume U).toReal := by
    have hh := WangZahlLot.Obl.wz_unit_segment_convex_slab_cover.determinant_le_volume
      hU hx.1 hxv hy.1 hp.1 b ENNReal.toReal_nonneg
      (by rw [ENNReal.ofReal_toReal hfinite])
    rw [← hb0, WangZahlLot.Obl.wz_unit_segment_convex_slab_cover.determinant_first,
      hy1, hy2, zero_mul, sub_zero, abs_mul, abs_of_pos hw] at hh
    exact hh
  have hsarea : s ≤ 64 * (volume U).toReal / ‖w‖ := by
    apply csSup_le hE
    rintro _ ⟨p, hp, rfl⟩
    exact (le_div_iff₀ hw).mpr (by simpa only [mul_comm] using hdet p hp)
  have harea : s * r ≤ 128 * (volume U).toReal := calc
    s * r ≤ (64 * (volume U).toReal / ‖w‖) * r :=
      mul_le_mul_of_nonneg_right hsarea hr.le
    _ ≤ (64 * (volume U).toReal / ‖w‖) * (2 * ‖w‖) :=
      mul_le_mul_of_nonneg_left (by linarith [hys]) (by positivity)
    _ = 128 * (volume U).toReal := by field_simp; ring
  refine ⟨b, max δ s, max δ r, le_max_left _ _, max_le_max le_rfl hsle,
    max_le hδ2 hrle, ?_, ?_⟩
  · intro p hp
    refine ⟨?_, ?_, ?_⟩
    · exact ((abs_real_inner_le_norm (b 0) (p - x)).trans
        (by simpa [b.norm_eq_one] using hnorm p hp))
    · exact ((abs_inner_le_transverse (b.norm_eq_one 1) hb1v _).trans
        (hproj p hp)).trans (le_max_right _ _)
    · exact (hsproj p hp).trans (le_max_right _ _)
  · have has : max δ s ≤ 2 * s := max_le (by linarith) (by linarith)
    have har : max δ r ≤ 2 * r := max_le (by linarith) (by linarith)
    have hh := mul_le_mul has har (le_trans hr.le (le_max_right _ _)) (by positivity : 0 ≤ 2 * s)
    nlinarith

end
end WangZahlLot.Obl.wz_concentrated_convex_factorization
