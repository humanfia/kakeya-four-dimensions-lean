-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Endpoints.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Frostman

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file Endpoints.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set Metric MeasureTheory
open scoped ENNReal

/-- Midpoint of the unit axis segment. -/
noncomputable def center (x v : Space) : Space := x + (1 / 2 : ℝ) • v

lemma sum_parameters_bound {a b : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    |a + b - 1| ≤ 1 - |b - a| := by
  rw [abs_le]
  rcases le_total a b with hab | hba
  · rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  · rw [abs_of_nonpos (sub_nonpos.mpr hba)]
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

/-- Exact unit-length containment controls the longitudinal position as well as the axis. -/
lemma center_near_of_segment_subset {ρ : ℝ} {x v z w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hsub : segment ℝ x (x + v) ⊆ Tube ρ z w) :
    ‖center x v - center z w‖ < 2 * ρ := by
  obtain ⟨p, hp, hxp⟩ := mem_thickening_iff.mp (hsub (left_mem_segment ℝ x (x + v)))
  obtain ⟨q, hq, hxq⟩ := mem_thickening_iff.mp (hsub (right_mem_segment ℝ x (x + v)))
  rw [segment_eq_image'] at hp hq
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨b, hb, rfl⟩ := hq
  simp only [add_sub_cancel_left, dist_eq_norm] at hxp hxq
  have hvw : ‖v - (b - a) • w‖ < 2 * ρ := by
    have he : v - (b - a) • w =
        (x + v - (z + b • w)) - (x - (z + a • w)) := by module
    rw [he]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  have habs : 1 - |b - a| < 2 * ρ := by
    have hh := norm_sub_norm_le v ((b - a) • w)
    rw [hv, norm_smul, hw, Real.norm_eq_abs, mul_one] at hh
    exact hh.trans_lt hvw
  have hs : |a + b - 1| < 2 * ρ := (sum_parameters_bound ha hb).trans_lt habs
  have he : center x v - center z w =
      (1 / 2 : ℝ) • ((x - (z + a • w)) + (x + v - (z + b • w))) +
      ((a + b - 1) / 2) • w := by
    dsimp [center]
    module
  rw [he]
  calc
    _ ≤ ‖(1 / 2 : ℝ) • ((x - (z + a • w)) + (x + v - (z + b • w)))‖ +
        ‖((a + b - 1) / 2) • w‖ := norm_add_le _ _
    _ = (1 / 2 : ℝ) * ‖(x - (z + a • w)) + (x + v - (z + b • w))‖ +
        |a + b - 1| / 2 := by
      rw [norm_smul, norm_smul, hw]
      norm_num only [Real.norm_eq_abs, abs_div, mul_one]
    _ ≤ (1 / 2 : ℝ) * (‖x - (z + a • w)‖ + ‖x + v - (z + b • w)‖) +
        |a + b - 1| / 2 := by gcongr; exact norm_add_le _ _
    _ < 2 * ρ := by linarith

lemma center_near_of_tube_subset {δ ρ : ℝ} (hδ : 0 < δ) {x v z w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hsub : Tube δ x v ⊆ Tube ρ z w) :
    ‖center x v - center z w‖ < 2 * ρ :=
  center_near_of_segment_subset hv hw ((self_subset_thickening hδ _).trans hsub)

/-- Widely separated segment midpoints force singleton fibres in any sufficiently small cover. -/
lemma unique_fibre_of_centers_separated {δ r ρ : ℝ} (hδ : 0 < δ) (hρ : ρ ≤ r)
    {n : ℕ} (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hsep : ∀ i j, i ≠ j → 4 * r ≤ ‖center (x i) (v i) - center (x j) (v j)‖)
    (z w : Space) (hw : ‖w‖ = 1) {i j : Fin n}
    (hi : Tube δ (x i) (v i) ⊆ Tube ρ z w)
    (hj : Tube δ (x j) (v j) ⊆ Tube ρ z w) : i = j := by
  by_contra hne
  have hi' := center_near_of_tube_subset hδ (hv i) hw hi
  have hj' := center_near_of_tube_subset hδ (hv j) hw hj
  have hd := norm_sub_le_norm_sub_add_norm_sub (center (x i) (v i)) (center z w) (center (x j) (v j))
  rw [norm_sub_rev (center z w)] at hd
  linarith [hsep i j hne]

/-- A gap between the tube radius and the midpoint spacing excludes every sticky subfamily. -/
theorem not_sticky_of_centers_separated {δ ξ r ρ₀ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδρ : δ ≤ ρ₀) (hρ1 : ρ₀ ≤ 1)
    (hscale : δ ^ (-ξ) * ρ₀ ≤ r)
    (hgap : 384 * δ ^ (-ξ) * δ ^ 2 < ρ₀ ^ 2)
    {n : ℕ} (x v : Fin n → Space) (hn : 0 < n) (hv : ∀ i, ‖v i‖ = 1)
    (hsep : ∀ i j, i ≠ j → 4 * r ≤ ‖center (x i) (v i) - center (x j) (v j)‖) :
    ¬ Sticky ξ δ (fun i => Tube δ (x i) (v i)) := by
  classical
  intro hS
  obtain ⟨ρ, hρlo, hρhi, hρscale, q, hq, z, w, hw, _, hcover, _, _, hlocal⟩ :=
    hS ρ₀ hδρ hρ1
  let i : Fin n := ⟨0, hn⟩
  obtain ⟨j, hij, _⟩ := hcover i
  have hu : ∀ l, Tube δ (x l) (v l) ⊆ Tube ρ (z j) (w j) ↔ l = i := by
    intro l
    exact ⟨fun hl => unique_fibre_of_centers_separated hδ (hρscale.trans hscale)
      x v hv hsep _ _ (hw j) hl hij, fun he => he ▸ hij⟩
  have he₁ : {l | Tube δ (x l) (v l) ⊆ Tube ρ (z j) (w j)} = {i} := by
    ext l
    exact hu l
  have he₂ : {l | Tube δ (x l) (v l) ⊆ Tube ρ (z j) (w j) ∧
      Tube δ (x l) (v l) ⊆ Tube δ (x i) (v i)} = {i} := by
    ext l
    simp only [mem_ofPred_eq, hu, mem_singleton_iff]
    exact ⟨And.left, fun h => ⟨h, h ▸ Subset.rfl⟩⟩
  have hh := hlocal j (Tube δ (x i) (v i)) (tube_convex _ _ _)
  rw [he₁, he₂, ncard_singleton] at hh
  simp only [Nat.cast_one, one_mul, mul_one] at hh
  have hh' : ENNReal.ofReal (ρ ^ 2) ≤ ENNReal.ofReal (384 * δ ^ (-ξ) * δ ^ 2) := by
    calc
      _ ≤ ENNReal.ofReal (δ ^ (-ξ)) * volume (Tube δ (x i) (v i)) := hh
      _ ≤ ENNReal.ofReal (δ ^ (-ξ)) * ENNReal.ofReal (384 * δ ^ 2) :=
        mul_le_mul' le_rfl (tube_volume_upper hδ hδ1 _ _ (hv i))
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  have hb := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh'
  have hρ₀ : 0 ≤ ρ₀ := hδ.le.trans hδρ
  have hs := pow_le_pow_left₀ hρ₀ hρlo 2
  linarith

/-- The spacing obstruction persists after every injective restriction. -/
theorem no_sticky_subfamily_of_centers_separated {δ ξ r ρ₀ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδρ : δ ≤ ρ₀) (hρ1 : ρ₀ ≤ 1)
    (hscale : δ ^ (-ξ) * ρ₀ ≤ r)
    (hgap : 384 * δ ^ (-ξ) * δ ^ 2 < ρ₀ ^ 2)
    {n : ℕ} (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hsep : ∀ i j, i ≠ j → 4 * r ≤ ‖center (x i) (v i) - center (x j) (v j)‖) :
    ¬ ∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧ 0 < k ∧
      Sticky ξ δ (fun j => Tube δ (x (g j)) (v (g j))) := by
  rintro ⟨k, g, hg, hk, hS⟩
  exact not_sticky_of_centers_separated hδ hδ1 hδρ hρ1 hscale hgap
    (fun j => x (g j)) (fun j => v (g j)) hk (fun j => hv (g j))
    (fun i j hij => hsep _ _ (hg.ne hij)) hS

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
