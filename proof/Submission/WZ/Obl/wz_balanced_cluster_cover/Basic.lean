-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_balanced_cluster_cover.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_direction_density_transfer

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_balanced_cluster_cover

open MeasureTheory Metric Set
open scoped ENNReal

/-- Three-dimensional Euclidean space. -/
abbrev V := EuclideanSpace ℝ (Fin 3)

/-! ### Projective distance -/

theorem min_norm_le_iff {v w : V} {r : ℝ} :
    min ‖v - w‖ ‖v + w‖ ≤ r ↔ ‖v - w‖ ≤ r ∨ ‖v + w‖ ≤ r := min_le_iff

theorem min_norm_triangle (v w u : V) :
    min ‖v - u‖ ‖v + u‖ ≤ min ‖v - w‖ ‖v + w‖ + ‖w - u‖ := by
  rcases le_total ‖v - w‖ ‖v + w‖ with h | h
  · rw [min_eq_left h]
    apply min_le_of_left_le
    calc ‖v - u‖ = ‖(v - w) + (w - u)‖ := by congr 1; abel
      _ ≤ ‖v - w‖ + ‖w - u‖ := norm_add_le _ _
  · rw [min_eq_right h]
    apply min_le_of_right_le
    calc ‖v + u‖ = ‖(v + w) - (w - u)‖ := by congr 1; abel
      _ ≤ ‖v + w‖ + ‖w - u‖ := norm_sub_le _ _

/-! ### Coordinates and lattice cells -/

theorem abs_apply_le_norm (y : V) (k : Fin 3) : |y k| ≤ ‖y‖ := by
  simpa using PiLp.norm_apply_le y k

theorem norm_le_of_forall_abs_le {y : V} {t : ℝ} (ht : 0 ≤ t) (h : ∀ k, |y k| ≤ t) :
    ‖y‖ ≤ 2 * t := by
  rw [EuclideanSpace.norm_eq]
  have hk : ∀ k, ‖y.ofLp k‖ ^ 2 ≤ t ^ 2 := by
    intro k
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h k) 2
  have hs : ∑ k, ‖y.ofLp k‖ ^ 2 ≤ (2 * t) ^ 2 := by
    rw [Fin.sum_univ_three]
    nlinarith [hk 0, hk 1, hk 2]
  calc √(∑ k, ‖y.ofLp k‖ ^ 2) ≤ √((2 * t) ^ 2) := Real.sqrt_le_sqrt hs
    _ = 2 * t := Real.sqrt_sq (by linarith)

/-- Coordinatewise floor cell at scale `θ`. -/
def cell (θ : ℝ) (y : V) : Fin 3 → ℤ := fun k => ⌊y k / θ⌋

theorem norm_sub_le_of_cell_eq {θ : ℝ} (hθ : 0 < θ) {y y' : V} (h : cell θ y = cell θ y') :
    ‖y - y'‖ ≤ 2 * θ := by
  apply norm_le_of_forall_abs_le hθ.le
  intro k
  have hk : ⌊y k / θ⌋ = ⌊y' k / θ⌋ := congrFun h k
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor hk
  rw [← sub_div, abs_div, abs_of_pos hθ, div_lt_one hθ] at h1
  have : (y - y') k = y k - y' k := by simp
  rw [this]
  exact h1.le

/-- The lattice cells meeting the closed ball of radius `ρ` about `c`. -/
def box (θ : ℝ) (c : V) (ρ : ℝ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset fun k => Finset.Icc ⌊(c k - ρ) / θ⌋ ⌊(c k + ρ) / θ⌋

theorem cell_mem_box {θ : ℝ} (hθ : 0 < θ) {c y : V} {ρ : ℝ} (h : ‖y - c‖ ≤ ρ) :
    cell θ y ∈ box θ c ρ := by
  rw [box, Fintype.mem_piFinset]
  intro k
  have hk : |y k - c k| ≤ ρ := by
    have h1 := abs_apply_le_norm (y - c) k
    have h2 : (y - c) k = y k - c k := by simp
    rw [h2] at h1
    linarith
  rw [abs_le] at hk
  rw [Finset.mem_Icc]
  constructor
  · apply Int.floor_mono
    apply div_le_div_of_nonneg_right _ hθ.le
    linarith
  · apply Int.floor_mono
    apply div_le_div_of_nonneg_right _ hθ.le
    linarith

theorem card_Icc_floor_le {θ : ℝ} (hθ : 0 < θ) (x ρ : ℝ) (hρ : 0 ≤ ρ) :
    ((Finset.Icc ⌊(x - ρ) / θ⌋ ⌊(x + ρ) / θ⌋).card : ℝ) ≤ 2 * ρ / θ + 2 := by
  rw [Int.card_Icc]
  have ha : (x - ρ) / θ - 1 < (⌊(x - ρ) / θ⌋ : ℝ) := Int.sub_one_lt_floor _
  have hb : (⌊(x + ρ) / θ⌋ : ℝ) ≤ (x + ρ) / θ := Int.floor_le _
  have hdiff : (x + ρ) / θ - (x - ρ) / θ = 2 * ρ / θ := by ring
  have hpos : 0 ≤ 2 * ρ / θ := by positivity
  rcases le_or_gt 0 (⌊(x + ρ) / θ⌋ + 1 - ⌊(x - ρ) / θ⌋) with h | h
  · have e1 : (((⌊(x + ρ) / θ⌋ + 1 - ⌊(x - ρ) / θ⌋).toNat : ℤ) : ℝ) =
        ((⌊(x + ρ) / θ⌋ + 1 - ⌊(x - ρ) / θ⌋ : ℤ) : ℝ) := by
      rw [Int.toNat_of_nonneg h]
    have e2 : (((⌊(x + ρ) / θ⌋ + 1 - ⌊(x - ρ) / θ⌋).toNat : ℕ) : ℝ) =
        (((⌊(x + ρ) / θ⌋ + 1 - ⌊(x - ρ) / θ⌋).toNat : ℤ) : ℝ) := by norm_cast
    rw [e2, e1]
    push_cast
    linarith
  · have : (⌊(x + ρ) / θ⌋ + 1 - ⌊(x - ρ) / θ⌋).toNat = 0 := Int.toNat_eq_zero.mpr h.le
    rw [this]
    simp only [Nat.cast_zero]
    linarith

theorem card_box_le {θ : ℝ} (hθ : 0 < θ) (c : V) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ((box θ c ρ).card : ℝ) ≤ (2 * ρ / θ + 2) ^ 3 := by
  rw [box, Fintype.card_piFinset, Nat.cast_prod, Fin.prod_univ_three]
  have h0 := card_Icc_floor_le hθ (c 0) ρ hρ
  have h1 := card_Icc_floor_le hθ (c 1) ρ hρ
  have h2 := card_Icc_floor_le hθ (c 2) ρ hρ
  have hpos : 0 ≤ 2 * ρ / θ + 2 := by positivity
  calc _ ≤ (2 * ρ / θ + 2) * (2 * ρ / θ + 2) * (2 * ρ / θ + 2) := by
        apply mul_le_mul (mul_le_mul h0 h1 (Nat.cast_nonneg _) hpos) h2 (Nat.cast_nonneg _)
          (by positivity)
    _ = _ := by ring

theorem measurable_cell (θ : ℝ) : Measurable (cell θ) := by
  unfold cell
  apply measurable_pi_iff.mpr
  intro k
  apply Measurable.floor
  apply Measurable.div_const
  exact ((EuclideanSpace.proj k : V →L[ℝ] ℝ).continuous.measurable)

/-! ### Projection orthogonal to a unit vector -/

/-- The projection of `y` onto the orthogonal complement of `w`. -/
def proj (w y : V) : V := y - (inner ℝ w y) • w

theorem continuous_proj (w : V) : Continuous (proj w) := by
  unfold proj
  fun_prop

theorem norm_proj_le {w : V} (hw : ‖w‖ = 1) (y : V) : ‖proj w y‖ ≤ 2 * ‖y‖ := by
  unfold proj
  have h := abs_real_inner_le_norm w y
  rw [hw, one_mul] at h
  calc ‖y - inner ℝ w y • w‖ ≤ ‖y‖ + ‖inner ℝ w y • w‖ := norm_sub_le _ _
    _ = ‖y‖ + |inner ℝ w y| := by rw [norm_smul, hw, mul_one, Real.norm_eq_abs]
    _ ≤ 2 * ‖y‖ := by linarith

/-! ### Tubes -/

theorem exists_param_of_mem_tube {δ : ℝ} {x v q : V}
    (h : q ∈ thickening δ (segment ℝ x (x + v))) :
    ∃ t ∈ Icc (0 : ℝ) 1, ‖q - (x + t • v)‖ < δ := by
  obtain ⟨y, hy, hqy⟩ := mem_thickening_iff.mp h
  rw [segment_eq_image'] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  refine ⟨t, ht, ?_⟩
  simpa [dist_eq_norm] using hqy

theorem mem_cyl {z w q : V} {τ R : ℝ} (hτ0 : 0 ≤ τ) (hτ6 : τ ≤ 6)
    (h : ‖q - (z + τ • w)‖ < R) :
    q ∈ thickening R (segment ℝ z (z + (6 : ℝ) • w)) := by
  rw [mem_thickening_iff]
  refine ⟨z + τ • w, ?_, by rwa [dist_eq_norm]⟩
  rw [segment_eq_image']
  refine ⟨τ / 6, ⟨by positivity, by linarith⟩, ?_⟩
  simp only [add_sub_cancel_left, smul_smul]
  congr 2
  ring

theorem tube_volume_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (x v : V) (hv : ‖v‖ = 1) :
    volume (thickening δ (segment ℝ x (x + v))) ≤ ENNReal.ofReal (384 * δ ^ 2) := by
  have h := WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper x v hv
    (T := Icc 0 1) subset_rfl (r := δ) (A := 1) hδ zero_le_one (by
      intro s hs t ht
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hs.1, hs.2, ht.1, ht.2])
  have hseg : (fun t : ℝ => x + t • v) '' Icc 0 1 = segment ℝ x (x + v) := by
    rw [segment_eq_image']
    simp
  rw [hseg] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  nlinarith [sq_nonneg δ]


/-! ### Labels -/

/-- A unit vector in the direction cell `L`, when there is one. -/
def W (θ : ℝ) (L : Fin 3 → ℤ) : V := Classical.epsilon fun u : V => ‖u‖ = 1 ∧ cell θ u = L

theorem W_spec {θ : ℝ} {L : Fin 3 → ℤ} {u : V} (hu : ‖u‖ = 1) (hL : cell θ u = L) :
    ‖W θ L‖ = 1 ∧ cell θ (W θ L) = L :=
  Classical.epsilon_spec (p := fun u : V => ‖u‖ = 1 ∧ cell θ u = L) ⟨u, hu, hL⟩

/-- The label of a point: the cell of its selected direction and the cell of its
transverse position. -/
def lab (θ : ℝ) (u : V → V) (p : V) : (Fin 3 → ℤ) × (Fin 3 → ℤ) :=
  (cell θ (u p), cell θ (proj (W θ (cell θ (u p))) p))

theorem measurableSet_lab {n : ℕ} (θ : ℝ) (v : Fin n → V) (a : V → Fin n)
    (ha : ∀ i, MeasurableSet {p | a p = i}) (ℓ : (Fin 3 → ℤ) × (Fin 3 → ℤ)) :
    MeasurableSet {p | lab θ (fun p => v (a p)) p = ℓ} := by
  have e : {p | lab θ (fun p => v (a p)) p = ℓ} =
      ⋃ m : Fin n, ({p | a p = m} ∩
        {p | (cell θ (v m), cell θ (proj (W θ (cell θ (v m))) p)) = ℓ}) := by
    ext p
    simp only [lab, mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      exact ⟨a p, rfl, h⟩
    · rintro ⟨m, rfl, h⟩
      exact h
  rw [e]
  refine MeasurableSet.iUnion fun m => (ha m).inter ?_
  have hm : Measurable fun p : V => (cell θ (v m), cell θ (proj (W θ (cell θ (v m))) p)) :=
    measurable_const.prodMk ((measurable_cell θ).comp (continuous_proj _).measurable)
  exact hm (measurableSet_singleton ℓ)

/-! ### Geometry of one cluster -/

theorem exists_sign {v w : V} {r : ℝ} (h : min ‖v - w‖ ‖v + w‖ ≤ r) :
    ∃ σ : ℝ, |σ| ≤ 1 ∧ ‖v - σ • w‖ ≤ r := by
  rcases min_le_iff.mp h with h | h
  · exact ⟨1, by norm_num, by simpa using h⟩
  · exact ⟨-1, by norm_num, by simpa using h⟩

/-- The direction of a cluster member is close to the cluster's axis. -/
theorem dir_close {θ A : ℝ} (hθ : 0 < θ) {vi up : V} (hup : ‖up‖ = 1)
    (h : min ‖vi - up‖ ‖vi + up‖ ≤ A * θ) :
    ‖W θ (cell θ up)‖ = 1 ∧
      min ‖vi - W θ (cell θ up)‖ ‖vi + W θ (cell θ up)‖ ≤ (A + 2) * θ := by
  obtain ⟨hw, hcell⟩ := W_spec (θ := θ) hup rfl
  refine ⟨hw, ?_⟩
  have hclose : ‖up - W θ (cell θ up)‖ ≤ 2 * θ := norm_sub_le_of_cell_eq hθ hcell.symm
  calc _ ≤ min ‖vi - up‖ ‖vi + up‖ + ‖up - W θ (cell θ up)‖ := min_norm_triangle vi up _
    _ ≤ A * θ + 2 * θ := add_le_add h hclose
    _ = (A + 2) * θ := by ring

/-- Every tube through a point of a cluster lies in the cluster's cylinder. -/
theorem tube_subset_cyl {δ θ A : ℝ} (hθ : 0 < θ) (hδθ : δ ≤ θ) {x vi w p pt : V}
    (hw : ‖w‖ = 1) (hp1 : ‖p‖ < 1)
    (hpT : p ∈ thickening δ (segment ℝ x (x + vi)))
    (hvw : min ‖vi - w‖ ‖vi + w‖ ≤ (A + 2) * θ)
    (hcell : cell θ (proj w p) = cell θ (proj w pt)) :
    thickening δ (segment ℝ x (x + vi)) ⊆
      thickening ((A + 6) * θ)
        (segment ℝ (proj w pt - (3 : ℝ) • w) (proj w pt - (3 : ℝ) • w + (6 : ℝ) • w)) := by
  intro q hq
  obtain ⟨t, ht, hqt⟩ := exists_param_of_mem_tube hq
  obtain ⟨s, hs, hps⟩ := exists_param_of_mem_tube hpT
  obtain ⟨σ, hσ, hσv⟩ := exists_sign hvw
  have hpp : ‖proj w p - proj w pt‖ ≤ 2 * θ := norm_sub_le_of_cell_eq hθ hcell
  have hin : |inner ℝ w p| < 1 := by
    have := abs_real_inner_le_norm w p
    rw [hw, one_mul] at this
    linarith
  have hts : |t - s| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2, hs.1, hs.2]
  have hσts : |(t - s) * σ| ≤ 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (t - s), abs_nonneg σ]
  apply mem_cyl (τ := inner ℝ w p + (t - s) * σ + 3)
  · have := (abs_le.mp hσts).1
    have := (abs_lt.mp hin).1
    linarith
  · have := (abs_le.mp hσts).2
    have := (abs_lt.mp hin).2
    linarith
  · have e : q - (proj w pt - (3 : ℝ) • w + (inner ℝ w p + (t - s) * σ + 3) • w) =
        (q - (x + t • vi)) - (p - (x + s • vi)) + (proj w p - proj w pt) +
          (t - s) • (vi - σ • w) := by
      unfold proj
      module
    rw [e]
    have h4 : ‖(t - s) • (vi - σ • w)‖ ≤ (A + 2) * θ := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |t - s| * ‖vi - σ • w‖ ≤ 1 * ((A + 2) * θ) :=
            mul_le_mul hts hσv (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    have n1 := norm_add_le ((q - (x + t • vi)) - (p - (x + s • vi)) + (proj w p - proj w pt))
      ((t - s) • (vi - σ • w))
    have n2 := norm_add_le ((q - (x + t • vi)) - (p - (x + s • vi))) (proj w p - proj w pt)
    have n3 := norm_sub_le (q - (x + t • vi)) (p - (x + s • vi))
    linarith

/-- The transverse position of a point of a tube is close to that of the tube's base. -/
theorem proj_close {δ θ A : ℝ} (hδθ : δ ≤ θ) {x vi w p : V} (hw : ‖w‖ = 1)
    (hpT : p ∈ thickening δ (segment ℝ x (x + vi)))
    (hvw : min ‖vi - w‖ ‖vi + w‖ ≤ (A + 2) * θ) :
    ‖proj w p - proj w x‖ ≤ (2 * A + 6) * θ := by
  obtain ⟨s, hs, hps⟩ := exists_param_of_mem_tube hpT
  obtain ⟨σ, hσ, hσv⟩ := exists_sign hvw
  have e : proj w p - proj w x = s • proj w (vi - σ • w) + proj w (p - (x + s • vi)) := by
    simp only [proj, inner_sub_right, inner_add_right, inner_smul_right,
      real_inner_self_eq_norm_sq, hw]
    module
  rw [e]
  have h1 : ‖s • proj w (vi - σ • w)‖ ≤ 2 * ((A + 2) * θ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    have := norm_proj_le hw (vi - σ • w)
    have hs1 := hs.2
    nlinarith [norm_nonneg (proj w (vi - σ • w))]
  have h2 : ‖proj w (p - (x + s • vi))‖ ≤ 2 * δ := by
    have := norm_proj_le hw (p - (x + s • vi))
    linarith
  calc _ ≤ ‖s • proj w (vi - σ • w)‖ + ‖proj w (p - (x + s • vi))‖ := norm_add_le _ _
    _ ≤ 2 * ((A + 2) * θ) + 2 * δ := add_le_add h1 h2
    _ ≤ (2 * A + 6) * θ := by linarith

theorem dir_cell_mem {θ A : ℝ} (hθ : 0 < θ) {vi up : V}
    (h : min ‖vi - up‖ ‖vi + up‖ ≤ A * θ) :
    cell θ up ∈ box θ vi (A * θ) ∪ box θ (-vi) (A * θ) := by
  rcases min_le_iff.mp h with h | h
  · exact Finset.mem_union_left _ (cell_mem_box hθ (by rw [norm_sub_rev]; exact h))
  · refine Finset.mem_union_right _ (cell_mem_box hθ ?_)
    rw [sub_neg_eq_add, add_comm]
    exact h

/-- All labels that points of a tube can carry. -/
def labelBox (θ A : ℝ) (x vi : V) : Finset ((Fin 3 → ℤ) × (Fin 3 → ℤ)) :=
  (box θ vi (A * θ) ∪ box θ (-vi) (A * θ)).biUnion fun L =>
    (box θ (proj (W θ L) x) ((2 * A + 6) * θ)).image fun h => (L, h)

theorem lab_mem_labelBox {δ θ A : ℝ} (hθ : 0 < θ) (hδθ : δ ≤ θ) {x vi up p : V}
    (hup : ‖up‖ = 1) (hpT : p ∈ thickening δ (segment ℝ x (x + vi)))
    (h : min ‖vi - up‖ ‖vi + up‖ ≤ A * θ) :
    (cell θ up, cell θ (proj (W θ (cell θ up)) p)) ∈ labelBox θ A x vi := by
  obtain ⟨hw, hvw⟩ := dir_close hθ hup h
  rw [labelBox, Finset.mem_biUnion]
  refine ⟨cell θ up, dir_cell_mem hθ h, ?_⟩
  rw [Finset.mem_image]
  exact ⟨_, cell_mem_box hθ (proj_close hδθ hw hpT hvw), rfl⟩

theorem card_labelBox_le {θ A : ℝ} (hθ : 0 < θ) (hA : 0 ≤ A) (x vi : V) :
    ((labelBox θ A x vi).card : ℝ) ≤ 2 * (2 * A + 2) ^ 3 * (4 * A + 14) ^ 3 := by
  set DB := box θ vi (A * θ) ∪ box θ (-vi) (A * θ) with hDBdef
  have himg : ∀ L ∈ DB, (((box θ (proj (W θ L) x) ((2 * A + 6) * θ)).image
      fun h => (L, h)).card : ℝ) ≤ (4 * A + 14) ^ 3 := by
    intro L _
    calc _ ≤ ((box θ (proj (W θ L) x) ((2 * A + 6) * θ)).card : ℝ) := by
          exact_mod_cast Finset.card_image_le
      _ ≤ (2 * ((2 * A + 6) * θ) / θ + 2) ^ 3 := card_box_le hθ _ (by positivity)
      _ = (4 * A + 14) ^ 3 := by
          congr 1
          field_simp
          ring
  have hDB : (DB.card : ℝ) ≤ 2 * (2 * A + 2) ^ 3 := by
    have h1 := card_box_le hθ vi (show 0 ≤ A * θ by positivity)
    have h2 := card_box_le hθ (-vi) (show 0 ≤ A * θ by positivity)
    have e : 2 * (A * θ) / θ + 2 = 2 * A + 2 := by
      field_simp
    rw [e] at h1 h2
    calc (DB.card : ℝ) ≤ ((box θ vi (A * θ)).card : ℝ) + ((box θ (-vi) (A * θ)).card : ℝ) := by
          exact_mod_cast Finset.card_union_le _ _
      _ ≤ _ := by linarith
  calc ((labelBox θ A x vi).card : ℝ) ≤ ∑ L ∈ DB, (((box θ (proj (W θ L) x)
        ((2 * A + 6) * θ)).image fun h => (L, h)).card : ℝ) := by
        rw [labelBox]
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ L ∈ DB, (4 * A + 14) ^ 3 := Finset.sum_le_sum himg
    _ = DB.card * (4 * A + 14) ^ 3 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * (2 * A + 2) ^ 3 * (4 * A + 14) ^ 3 := by
        apply mul_le_mul_of_nonneg_right hDB (by positivity)

/-! ### Counting through an injective reindexing -/

theorem ncard_comp_eq {n k : ℕ} (f : Fin k → Fin n) (hf : Function.Injective f)
    (Q : Fin n → Prop) (hQ : ∀ i, Q i → i ∈ Set.range f) :
    Set.ncard {i' : Fin k | Q (f i')} = Set.ncard {i : Fin n | Q i} := by
  rw [← Set.ncard_image_of_injective _ hf]
  congr 1
  ext i
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i', hi', rfl⟩
    exact hi'
  · intro hi
    obtain ⟨i', rfl⟩ := hQ i hi
    exact ⟨i', hi, rfl⟩

end WangZahlLot.Obl.wz_balanced_cluster_cover
