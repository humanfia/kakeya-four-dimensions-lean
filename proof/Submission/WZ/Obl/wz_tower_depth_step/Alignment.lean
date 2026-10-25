-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_tower_depth_step.Alignment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_tower_depth_step.Basic

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_tower_depth_step

open Set Metric

lemma exists_clipped_coefficient {a E : ℝ} (hE : 0 ≤ E) (ha : |a| ≤ 1 / 2 + E) :
    ∃ b : ℝ, -(1 / 2) ≤ b ∧ b ≤ 1 / 2 ∧ |a - b| ≤ E := by
  by_cases hlo : a ≤ -(1 / 2)
  · refine ⟨-(1 / 2), le_rfl, by norm_num, ?_⟩
    rw [abs_of_nonpos (by linarith)]
    linarith [(abs_le.mp ha).1]
  · by_cases hhi : 1 / 2 ≤ a
    · refine ⟨1 / 2, by norm_num, le_rfl, ?_⟩
      rw [abs_of_nonneg (by linarith)]
      linarith [(abs_le.mp ha).2]
    · exact ⟨a, by linarith, by linarith, by simpa using hE⟩

/-- Two endpoints close to a line, with midpoint in a transverse common plane,
are close to the centered unit segment of that line. -/
theorem aligned_endpoints_near_unit_segment {R : ℝ} (hR : 0 < R)
    {u x v y w : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huw : 1 / 4 ≤ |inner ℝ u w|)
    (hplane : inner ℝ u (x + (1 / 2 : ℝ) • v - (y + (1 / 2 : ℝ) • w)) = 0)
    (hnear : ∀ p ∈ ({x, x + v} : Set Space),
      ∃ a : ℝ, ‖p - ((y + (1 / 2 : ℝ) • w) + a • w)‖ < R) :
    x ∈ Tube (8 * R) y w ∧ x + v ∈ Tube (8 * R) y w := by
  obtain ⟨a₀, ha₀⟩ := hnear x (by simp)
  obtain ⟨a₁, ha₁⟩ := hnear (x + v) (by simp)
  let c := y + (1 / 2 : ℝ) • w
  let e₀ := x - (c + a₀ • w)
  let e₁ := x + v - (c + a₁ • w)
  have he₀ : ‖e₀‖ < R := ha₀
  have he₁ : ‖e₁‖ < R := ha₁
  have hsum_id : e₀ + e₁ =
      (2 : ℝ) • (x + (1 / 2 : ℝ) • v - c) - (a₀ + a₁) • w := by
    dsimp [e₀, e₁]
    module
  have hsum_inner : inner ℝ u (e₀ + e₁) = -(a₀ + a₁) * inner ℝ u w := by
    rw [hsum_id, inner_sub_right, inner_smul_right, inner_smul_right]
    change (2 : ℝ) * inner ℝ u (x + (1 / 2 : ℝ) • v - (y + (1 / 2 : ℝ) • w)) -
      (a₀ + a₁) * inner ℝ u w = _
    rw [hplane]
    ring
  have hsum_inner_bound : |a₀ + a₁| * |inner ℝ u w| ≤ 2 * R := by
    calc
      _ = |inner ℝ u (e₀ + e₁)| := by rw [hsum_inner, abs_mul, abs_neg]
      _ ≤ ‖u‖ * ‖e₀ + e₁‖ := abs_real_inner_le_norm _ _
      _ = ‖e₀ + e₁‖ := by rw [hu, one_mul]
      _ ≤ ‖e₀‖ + ‖e₁‖ := norm_add_le _ _
      _ ≤ 2 * R := by linarith
  have hsum : |a₀ + a₁| ≤ 8 * R := by
    nlinarith [mul_le_mul_of_nonneg_left huw (abs_nonneg (a₀ + a₁))]
  have hdiff_id : (a₁ - a₀) • w = v + e₀ - e₁ := by
    dsimp [e₀, e₁]
    module
  have hdiff : |a₁ - a₀| ≤ 1 + 2 * R := by
    calc
      _ = ‖(a₁ - a₀) • w‖ := by rw [norm_smul, Real.norm_eq_abs, hw, mul_one]
      _ = ‖v + e₀ - e₁‖ := congrArg norm hdiff_id
      _ ≤ ‖v + e₀‖ + ‖e₁‖ := norm_sub_le _ _
      _ ≤ ‖v‖ + ‖e₀‖ + ‖e₁‖ := by linarith [norm_add_le v e₀]
      _ ≤ 1 + 2 * R := by rw [hv]; linarith
  have ha₀' : |a₀| ≤ 1 / 2 + 5 * R := by
    rw [abs_le] at hsum hdiff ⊢
    constructor <;> linarith [hsum.1, hsum.2, hdiff.1, hdiff.2]
  have ha₁' : |a₁| ≤ 1 / 2 + 5 * R := by
    rw [abs_le] at hsum hdiff ⊢
    constructor <;> linarith [hsum.1, hsum.2, hdiff.1, hdiff.2]
  have hmem {p : Space} {a : ℝ} (hp : ‖p - (c + a • w)‖ < R)
      (ha : |a| ≤ 1 / 2 + 5 * R) : p ∈ Tube (8 * R) y w := by
    obtain ⟨b, hb₀, hb₁, hab⟩ := exists_clipped_coefficient (by positivity) ha
    apply mem_thickening_iff.mpr
    refine ⟨c + b • w, ?_, ?_⟩
    · rw [segment_eq_image']
      refine ⟨b + 1 / 2, ⟨by linarith, by linarith⟩, ?_⟩
      dsimp [c]
      module
    · rw [dist_eq_norm]
      have he : p - (c + b • w) = (p - (c + a • w)) + (a - b) • w := by module
      rw [he]
      calc
        _ ≤ ‖p - (c + a • w)‖ + ‖(a - b) • w‖ := norm_add_le _ _
        _ = ‖p - (c + a • w)‖ + |a - b| := by rw [norm_smul, Real.norm_eq_abs, hw, mul_one]
        _ < 8 * R := by linarith
  exact ⟨hmem ha₀ ha₀', hmem ha₁ ha₁'⟩

/-- Once the midpoint alignment is available, a doubled cover is replaced by an
exact unit-length cover at a fixed enlargement of its radius. -/
theorem aligned_doubled_cover {R s : ℝ} (hR : 0 < R)
    {u x v y w : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huw : 1 / 4 ≤ |inner ℝ u w|)
    (hplane : inner ℝ u (x + (1 / 2 : ℝ) • v - (y + (1 / 2 : ℝ) • w)) = 0)
    (hends : x ∈ Tube R (y - (1 / 2 : ℝ) • w) (2 • w) ∧
      x + v ∈ Tube R (y - (1 / 2 : ℝ) • w) (2 • w)) :
    Tube s x v ⊆ Tube (s + 8 * R) y w := by
  have hnear : ∀ p ∈ ({x, x + v} : Set Space),
      ∃ a : ℝ, ‖p - ((y + (1 / 2 : ℝ) • w) + a • w)‖ < R := by
    intro p hp
    have hpt : p ∈ Tube R (y - (1 / 2 : ℝ) • w) (2 • w) := by
      rcases Set.mem_insert_iff.mp hp with rfl | hp
      · exact hends.1
      · have : p = x + v := Set.mem_singleton_iff.mp hp
        simpa [this] using hends.2
    obtain ⟨z, hz, hpz⟩ := mem_thickening_iff.mp hpt
    rw [segment_eq_image'] at hz
    obtain ⟨t, _ht, rfl⟩ := hz
    refine ⟨2 * t - 1, ?_⟩
    rw [dist_eq_norm] at hpz
    convert hpz using 1; congr 1; module
  obtain ⟨h₀, h₁⟩ := aligned_endpoints_near_unit_segment hR hu hv hw huw hplane hnear
  have hseg : segment ℝ x (x + v) ⊆ Tube (8 * R) y w :=
    ((convex_segment y (y + w)).thickening (8 * R)).segment_subset h₀ h₁
  intro p hp
  obtain ⟨z, hz, hpz⟩ := mem_thickening_iff.mp hp
  obtain ⟨z', hz', hzz'⟩ := mem_thickening_iff.mp (hseg hz)
  exact mem_thickening_iff.mpr ⟨z', hz', (dist_triangle _ _ _).trans_lt (add_lt_add hpz hzz')⟩

end WangZahlLot.Obl.wz_tower_depth_step
