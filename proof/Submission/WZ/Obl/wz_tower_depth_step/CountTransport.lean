-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_tower_depth_step.CountTransport.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_tower_depth_step.ScalarAlignment
import Submission.WZ.Obl.wz_normalized_projection_iteration.Convex

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_tower_depth_step

open Set Metric MeasureTheory

/-- Bounded open convex tests suffice for a finite indexed family of open bounded sets. -/
lemma fiberCount_of_bounded_open {s L : ℝ} {n : ℕ} {P : Fin n → Prop}
    {U : Fin n → Set Space} (hopen : ∀ i, IsOpen (U i))
    (hbounded : ∀ i, Bornology.IsBounded (U i))
    (h : ∀ W : Set Space, Convex ℝ W → IsOpen W → Bornology.IsBounded W →
      ENNReal.ofReal ((Set.ncard {i | P i ∧ U i ⊆ W} : ℝ) * s ^ 2) ≤
        ENNReal.ofReal L * volume W) : FiberCount s L n P U := by
  have hb : Bornology.IsBounded (⋃ i, U i) := Bornology.isBounded_iUnion.mpr hbounded
  obtain ⟨R, hR⟩ := hb.subset_ball (0 : Space)
  intro W hW
  let V := interior W ∩ ball (0 : Space) R
  have hV : Convex ℝ V := hW.interior.inter (convex_ball _ _)
  have hVo : IsOpen V := isOpen_interior.inter isOpen_ball
  have hVb : Bornology.IsBounded V := isBounded_ball.subset inter_subset_right
  have he : {i | P i ∧ U i ⊆ W} = {i | P i ∧ U i ⊆ V} := by
    ext i
    constructor
    · rintro ⟨hi, hisub⟩
      exact ⟨hi, subset_inter ((hopen i).subset_interior_iff.mpr hisub)
        (fun p hp => hR (mem_iUnion.mpr ⟨i, hp⟩))⟩
    · rintro ⟨hi, hisub⟩
      exact ⟨hi, hisub.trans (inter_subset_left.trans interior_subset)⟩
  rw [he]
  exact (h V hV hVo hVb).trans
    (mul_le_mul' le_rfl (measure_mono (inter_subset_left.trans interior_subset)))

lemma mem_tube_axial_translate {s a : ℝ} {x v p : Space}
    (hp : p ∈ Tube s x v) : p + a • v ∈ Tube s (x + a • v) v := by
  obtain ⟨z, hz, hpz⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  apply mem_thickening_iff.mpr
  refine ⟨x + a • v + t • v, ?_, ?_⟩
  · rw [segment_eq_image']
    exact ⟨t, ht, by simp⟩
  · rw [dist_eq_norm] at hpz ⊢
    convert hpz using 1
    congr 1
    module

/-- A bounded axial translation is controlled by differences of points of the moved tube. -/
lemma tube_subset_axial_difference {s R a : ℝ} (hs : 0 < s) (hR : 1 ≤ R)
    (ha : |a| ≤ R) {x v : Space} {U : Set Space}
    (hU : ∀ p ∈ Tube s (x + a • v) v,
      ∀ q ∈ Tube s (x + a • v) v, ∀ z ∈ Tube s (x + a • v) v,
        p + R • (q - z) ∈ U) : Tube s x v ⊆ U := by
  have hRp : 0 < R := by linarith
  have hab : -1 ≤ a / R ∧ a / R ≤ 1 := by
    rw [le_div_iff₀ hRp, div_le_iff₀ hRp]
    constructor <;> linarith [(abs_le.mp ha).1, (abs_le.mp ha).2]
  let q := x + a • v + ((1 - a / R) / 2) • v
  let z := x + a • v + ((1 + a / R) / 2) • v
  have hq : q ∈ Tube s (x + a • v) v := by
    apply self_subset_thickening hs
    rw [segment_eq_image']
    exact ⟨(1 - a / R) / 2, ⟨by linarith [hab.2], by linarith [hab.1]⟩, by simp [q]⟩
  have hz : z ∈ Tube s (x + a • v) v := by
    apply self_subset_thickening hs
    rw [segment_eq_image']
    exact ⟨(1 + a / R) / 2, ⟨by linarith [hab.1], by linarith [hab.2]⟩, by simp [z]⟩
  intro p hp
  have hh := hU (p + a • v) (mem_tube_axial_translate hp) q hq z hz
  convert hh using 1
  dsimp [q, z]
  have he : R * ((1 - a / R) / 2 - (1 + a / R) / 2) = -a := by
    field_simp
    ring
  calc
    p = p + (a + R * ((1 - a / R) / 2 - (1 + a / R) / 2)) • v := by rw [he]; simp
    _ = _ := by module

/-- Axial moves with a fixed bound preserve every local convex count up to a fixed factor. -/
theorem fiberCount_axial_translate {s L R : ℝ} (hs : 0 < s) (hR : 1 ≤ R)
    {n : ℕ} {P : Fin n → Prop} {x v : Fin n → Space} (a : Fin n → ℝ)
    (ha : ∀ i, |a i| ≤ R)
    (hcount : FiberCount s L n P (fun i => Tube s (x i) (v i))) :
    FiberCount s ((48 * R) ^ 3 * L) n P (fun i => Tube s (x i + a i • v i) (v i)) := by
  apply fiberCount_of_bounded_open (fun _ => isOpen_thickening)
    (fun i => by
      have hc : IsCompact (segment ℝ (x i + a i • v i)
          (x i + a i • v i + v i)) := by
        rw [segment_eq_image']
        exact isCompact_Icc.image (by fun_prop)
      exact hc.isBounded.thickening)
  intro W hW hWo hWb
  by_cases hnone : {i | P i ∧ Tube s (x i + a i • v i) (v i) ⊆ W} = ∅
  · simp [hnone]
  have hi : (interior W).Nonempty := by
    obtain ⟨i, hi⟩ := Set.nonempty_iff_ne_empty.mpr hnone
    have hx : x i + a i • v i ∈ W := hi.2
      (self_subset_thickening hs _ (left_mem_segment ℝ _ _))
    exact ⟨_, by simpa [hWo.interior_eq] using hx⟩
  obtain ⟨U, hU, hvol, hcover⟩ :=
    WangZahlLot.Obl.wz_normalized_projection_iteration.exists_convex_difference_container hW hWb hi hR
  have hc : Set.ncard {i | P i ∧ Tube s (x i + a i • v i) (v i) ⊆ W} ≤
      Set.ncard {i | P i ∧ Tube s (x i) (v i) ⊆ U} := by
    apply Set.ncard_le_ncard _ (Set.toFinite _)
    intro i hi
    refine ⟨hi.1, tube_subset_axial_difference hs hR (ha i) ?_⟩
    intro p hp q hq z hz
    exact hcover p (hi.2 hp) q (hi.2 hq) z (hi.2 hz)
  calc
    _ ≤ ENNReal.ofReal ((Set.ncard {i | P i ∧ Tube s (x i) (v i) ⊆ U} : ℝ) * s ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (sq_nonneg _)
    _ ≤ ENNReal.ofReal L * volume U := hcount U hU
    _ = _ := by
      rw [hvol, ENNReal.ofReal_mul (by positivity : 0 ≤ (48 * R) ^ 3)]
      ring

end WangZahlLot.Obl.wz_tower_depth_step
