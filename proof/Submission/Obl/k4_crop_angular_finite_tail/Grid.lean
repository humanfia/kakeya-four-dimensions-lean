/- Adapted from this LOT tree, obligation o091, session x0299, commit 918e44ebabf26b3b2fd56f3cccbf12b4ac1bac6e,
Submission/Obl/k4_dyadic_crop_typicality/Grid.lean. Transfer.lean in that branch was written by session x0302 (9db252b). -/

import Submission.Obl.k4_profile_density_bounds.Common
import Submission.Obl.k4_matching_homogeneous_records.Encoding

open MeasureTheory Set
noncomputable section

namespace Submission.Obl.k4_crop_angular_finite_tail

abbrev Line := Submission.Obl.k4_profile_density_bounds.Line
abbrev State := Submission.Obl.k4_profile_density_bounds.State
abbrev Base := Submission.Obl.k4_profile_density_bounds.Base
abbrev Observation := Submission.Obl.k4_profile_density_bounds.Observation

open Submission.Obl.k4_profile_density_bounds (width base velocity hidden observe selected reference)

noncomputable def height (N u : ℝ) : ℕ := ⌊u * Real.log N / Real.log 2⌋₊

lemma depth_nonneg {N u : ℝ} (hN : 1 ≤ N) (hu : 0 ≤ u) :
    0 ≤ u * Real.log N / Real.log 2 := by
  positivity [Real.log_nonneg hN]

lemma width_height {N u : ℝ} (hN : 1 ≤ N) (hu : 0 ≤ u) :
    width N u = (2 : ℝ) ^ (-(height N u : ℤ)) := by
  unfold width height
  congr 2
  exact (Int.natCast_floor_eq_floor (depth_nonneg hN hu)).symm

lemma height_add {N u v : ℝ} (hN : 1 ≤ N) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    height N u + height N v ≤ height N (u + v) ∧
      height N (u + v) ≤ height N u + height N v + 1 := by
  have hs : (u + v) * Real.log N / Real.log 2 =
      u * Real.log N / Real.log 2 + v * Real.log N / Real.log 2 := by ring
  have h0 := depth_nonneg hN hu
  have h1 := depth_nonneg hN hv
  have h2 := depth_nonneg hN (add_nonneg hu hv)
  have ha := Int.le_floor_add (u * Real.log N / Real.log 2)
    (v * Real.log N / Real.log 2)
  have hb := Int.le_floor_add_floor (u * Real.log N / Real.log 2)
    (v * Real.log N / Real.log 2)
  rw [← hs] at ha hb
  simp only [height]
  rw [← Int.natCast_floor_eq_floor h0, ← Int.natCast_floor_eq_floor h1,
    ← Int.natCast_floor_eq_floor h2] at ha hb
  omega

lemma width_product {N u v : ℝ} (hN : 1 ≤ N) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ∃ d : ℕ, d ≤ 1 ∧ height N (u + v) = height N u + height N v + d ∧
      width N u * width N v = (2 : ℝ) ^ d * width N (u + v) := by
  obtain ⟨ha, hb⟩ := height_add hN hu hv
  let d := height N (u + v) - (height N u + height N v)
  have hd : height N (u + v) = height N u + height N v + d := by dsimp [d]; omega
  refine ⟨d, by dsimp [d]; omega, hd, ?_⟩
  rw [width_height hN hu, width_height hN hv, width_height hN (add_nonneg hu hv), hd]
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
    ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  push_cast
  ring

lemma width_inv_height {N u : ℝ} (hN : 1 ≤ N) (hu : 0 ≤ u) :
    (width N u)⁻¹ = (2 : ℝ) ^ height N u := by
  rw [width_height hN hu, zpow_neg, inv_inv, zpow_natCast]

/-- The angular bins in a crop are an integer shift of a coarsening of the
original canonical bins. The coarsening has at most two children per coordinate. -/
lemma angular_floor {N u v : ℝ} (hN : 1 ≤ N) (hu : 0 ≤ u) (hv : 0 ≤ v)
    {d : ℕ} (hd : height N (u + v) = height N u + height N v + d)
    (x : ℝ) (q : ℤ) :
    ⌊(x / width N u - (q : ℝ)) / width N v⌋ =
      ⌊x / width N (u + v)⌋ / (2 : ℤ) ^ d - q * (2 : ℤ) ^ height N v := by
  simp only [div_eq_mul_inv, width_inv_height hN hu, width_inv_height hN hv,
    width_inv_height hN (add_nonneg hu hv)]
  have he : (x * (2 : ℝ) ^ height N u - q) * (2 : ℝ) ^ height N v =
      x * (2 : ℝ) ^ (height N u + height N v) -
        ((q * (2 : ℤ) ^ height N v : ℤ) : ℝ) := by
    push_cast
    rw [pow_add]
    ring
  rw [he, Int.floor_sub_intCast,
    Submission.Obl.k4_matching_homogeneous_records.floor_dyadic_refinement
      (show height N u + height N v ≤ height N (u + v) by omega)]
  rw [show height N (u + v) - (height N u + height N v) = d by omega]

def cropLine (a : ℝ) (q : Fin 4 → ℤ) (l : Line) : Line :=
  (l.1, ![l.2 0 / a - q 0, l.2 1 / a - q 1, l.2 2,
    l.2 3 / a - q 2, l.2 4 / a - q 3, l.2 5])

def cropState (a : ℝ) (q : Fin 4 → ℤ) (p : State) : State :=
  (cropLine a q p.1, p.2)

def cropBase (a : ℝ) (q : Fin 4 → ℤ) (z : Base) : Base :=
  WithLp.toLp 2 ![z 0, z 1 / a - q 0 - z 0 * q 2,
    z 2 / a - q 1 - z 0 * q 3]

lemma measurable_cropLine (a : ℝ) (q : Fin 4 → ℤ) : Measurable (cropLine a q) := by
  unfold cropLine
  fun_prop

lemma measurable_cropState (a : ℝ) (q : Fin 4 → ℤ) : Measurable (cropState a q) := by
  exact (measurable_cropLine a q |>.comp measurable_fst).prodMk measurable_snd

lemma measurable_cropBase (a : ℝ) (q : Fin 4 → ℤ) : Measurable (cropBase a q) := by
  unfold cropBase
  fun_prop

lemma base_cropState (a : ℝ) (q : Fin 4 → ℤ) (p : State) :
    base (cropState a q p) = cropBase a q (base p) := by
  ext j
  fin_cases j <;> simp [base, cropBase, cropState, cropLine] <;> ring

lemma hidden_cropState (a : ℝ) (q : Fin 4 → ℤ) (p : State) :
    hidden (cropState a q p) = hidden p := by
  simp [Submission.Obl.k4_profile_density_bounds.hidden, cropState, cropLine]

lemma velocity_cropLine (a : ℝ) (q : Fin 4 → ℤ) (l : Line) (j : Fin 2) :
    velocity (cropLine a q l) j = velocity l j / a - q (j.natAdd 2) := by
  fin_cases j <;> simp [velocity, cropLine]

/-- The original coefficient box retained by a crop. -/
def cropBox (a : ℝ) (q : Fin 4 → ℤ) : Set Line :=
  {l | ⌊l.2 0 / a⌋ = q 0 ∧ ⌊l.2 1 / a⌋ = q 1 ∧
    ⌊l.2 3 / a⌋ = q 2 ∧ ⌊l.2 4 / a⌋ = q 3}

lemma measurableSet_cropBox (a : ℝ) (q : Fin 4 → ℤ) :
    MeasurableSet (cropBox a q) := by
  unfold cropBox
  measurability

lemma cropBox_disjoint (a : ℝ) {q q' : Fin 4 → ℤ} (h : q ≠ q') :
    Disjoint (cropBox a q) (cropBox a q') := by
  rw [Set.disjoint_left]
  intro l hl hl'
  apply h
  funext j
  fin_cases j
  · exact hl.1.symm.trans hl'.1
  · exact hl.2.1.symm.trans hl'.2.1
  · exact hl.2.2.1.symm.trans hl'.2.2.1
  · exact hl.2.2.2.symm.trans hl'.2.2.2

/-- Knowing the position and the velocity bin leaves two possible intercept
bins in one coordinate. -/
lemma intercept_floor_bounds {a t : ℝ} (ha : 0 < a)
    (ht : t ∈ Icc (0 : ℝ) 1) (b v : ℝ) :
    ⌊(b + t * v) / a - t * (⌊v / a⌋ : ℝ)⌋ - 1 ≤ ⌊b / a⌋ ∧
      ⌊b / a⌋ ≤ ⌊(b + t * v) / a - t * (⌊v / a⌋ : ℝ)⌋ := by
  have hθ0 : 0 ≤ v / a - (⌊v / a⌋ : ℝ) := sub_nonneg.mpr (Int.floor_le _)
  have hθ1 : v / a - (⌊v / a⌋ : ℝ) < 1 := by
    linarith [Int.lt_floor_add_one (v / a)]
  have hmul0 := mul_nonneg ht.1 hθ0
  have hmul1 : t * (v / a - (⌊v / a⌋ : ℝ)) < 1 :=
    (mul_le_mul_of_nonneg_right ht.2 hθ0).trans_lt (by simpa using hθ1)
  have he : (b + t * v) / a - t * (⌊v / a⌋ : ℝ) =
      b / a + t * (v / a - (⌊v / a⌋ : ℝ)) := by ring
  rw [he]
  constructor
  · have hb : b / a + t * (v / a - (⌊v / a⌋ : ℝ)) < (⌊b / a⌋ : ℝ) + 2 := by
      linarith [Int.lt_floor_add_one (b / a)]
    have hh : ⌊b / a + t * (v / a - (⌊v / a⌋ : ℝ))⌋ < ⌊b / a⌋ + 2 := by
      rw [Int.floor_lt]
      push_cast
      exact hb
    omega
  · exact Int.floor_mono (by linarith)

def cropCandidate (a : ℝ) (z : Base) (v : Fin 2 → ℤ)
    (e : Fin 2 → Fin 2) : Fin 4 → ℤ :=
  ![⌊z 1 / a - z 0 * v 0⌋ - (e 0).val,
    ⌊z 2 / a - z 0 * v 1⌋ - (e 1).val, v 0, v 1]

def cropCandidates (a : ℝ) (z : Base) (v : Fin 2 → ℤ) : Finset (Fin 4 → ℤ) :=
  Finset.univ.image (cropCandidate a z v)

lemma card_cropCandidates (a : ℝ) (z : Base) (v : Fin 2 → ℤ) :
    (cropCandidates a z v).card ≤ 4 := by
  exact (Finset.card_image_le).trans (by decide)

lemma cropBox_mem_candidates {a : ℝ} (ha : 0 < a) {q : Fin 4 → ℤ}
    {p : State} (hp : p.1 ∈ cropBox a q) (ht : p.2 ∈ Icc (0 : ℝ) 1) :
    q ∈ cropCandidates a (base p) (fun j => ⌊velocity p.1 j / a⌋) := by
  classical
  have hb0 := intercept_floor_bounds ha ht (p.1.2 0) (p.1.2 3)
  have hb1 := intercept_floor_bounds ha ht (p.1.2 1) (p.1.2 4)
  let c0 : ℤ := ⌊(p.1.2 0 + p.2 * p.1.2 3) / a - p.2 * (⌊p.1.2 3 / a⌋ : ℝ)⌋
  let c1 : ℤ := ⌊(p.1.2 1 + p.2 * p.1.2 4) / a - p.2 * (⌊p.1.2 4 / a⌋ : ℝ)⌋
  have h0 : 0 ≤ c0 - q 0 ∧ c0 - q 0 < 2 := by dsimp [c0]; rw [hp.1] at hb0; omega
  have h1 : 0 ≤ c1 - q 1 ∧ c1 - q 1 < 2 := by dsimp [c1]; rw [hp.2.1] at hb1; omega
  let e : Fin 2 → Fin 2 :=
    ![⟨(c0 - q 0).toNat, by omega⟩, ⟨(c1 - q 1).toNat, by omega⟩]
  apply Finset.mem_image.mpr
  refine ⟨e, Finset.mem_univ _, ?_⟩
  funext j
  fin_cases j
  · simp [cropCandidate, base, e, c0, velocity]
    omega
  · simp [cropCandidate, base, e, c1, velocity]
    omega
  · simpa [cropCandidate, velocity] using hp.2.2.1
  · simpa [cropCandidate, velocity] using hp.2.2.2

lemma card_cropCandidate_indices {n : ℕ} (q : Fin n → Fin 4 → ℤ)
    (hq : Function.Injective q) (a : ℝ) (z : Base) (v : Fin 2 → ℤ) :
    (Finset.univ.filter (fun i => q i ∈ cropCandidates a z v)).card ≤ 4 := by
  classical
  let s := Finset.univ.filter (fun i => q i ∈ cropCandidates a z v)
  calc
    s.card = (s.image q).card := (Finset.card_image_of_injective s hq).symm
    _ ≤ (cropCandidates a z v).card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hi).2
    _ ≤ 4 := card_cropCandidates a z v

def uncropLine (a : ℝ) (q : Fin 4 → ℤ) (l : Line) : Line :=
  (l.1, ![a * (l.2 0 + q 0), a * (l.2 1 + q 1), l.2 2,
    a * (l.2 3 + q 2), a * (l.2 4 + q 3), l.2 5])

lemma measurable_uncropLine (a : ℝ) (q : Fin 4 → ℤ) : Measurable (uncropLine a q) := by
  unfold uncropLine
  fun_prop

lemma uncropLine_cropLine {a : ℝ} (ha : a ≠ 0) (q : Fin 4 → ℤ) (l : Line) :
    uncropLine a q (cropLine a q l) = l := by
  apply Prod.ext
  · rfl
  · funext j
    fin_cases j <;> simp [uncropLine, cropLine, ha] <;> field_simp <;> ring

lemma cropLine_uncropLine {a : ℝ} (ha : a ≠ 0) (q : Fin 4 → ℤ) (l : Line) :
    cropLine a q (uncropLine a q l) = l := by
  apply Prod.ext
  · rfl
  · funext j
    fin_cases j <;> simp [uncropLine, cropLine, ha]

def cropLineEquiv {a : ℝ} (ha : a ≠ 0) (q : Fin 4 → ℤ) : Line ≃ᵐ Line where
  toFun := cropLine a q
  invFun := uncropLine a q
  left_inv := uncropLine_cropLine ha q
  right_inv := cropLine_uncropLine ha q
  measurable_toFun := measurable_cropLine a q
  measurable_invFun := measurable_uncropLine a q

def cropStateEquiv {a : ℝ} (ha : a ≠ 0) (q : Fin 4 → ℤ) : State ≃ᵐ State :=
  MeasurableEquiv.prodCongr (cropLineEquiv ha q) (MeasurableEquiv.refl ℝ)

lemma cropStateEquiv_apply {a : ℝ} (ha : a ≠ 0) (q : Fin 4 → ℤ) (p : State) :
    cropStateEquiv ha q p = cropState a q p := rfl

def uncropBase (a : ℝ) (q : Fin 4 → ℤ) (z : Base) : Base :=
  WithLp.toLp 2 ![z 0, a * (z 1 + q 0 + z 0 * q 2),
    a * (z 2 + q 1 + z 0 * q 3)]

lemma measurable_uncropBase (a : ℝ) (q : Fin 4 → ℤ) : Measurable (uncropBase a q) := by
  unfold uncropBase
  fun_prop

lemma uncropBase_cropBase {a : ℝ} (ha : a ≠ 0) (q : Fin 4 → ℤ) (z : Base) :
    uncropBase a q (cropBase a q z) = z := by
  ext j
  fin_cases j <;> simp [uncropBase, cropBase] <;> field_simp <;> ring

lemma cropBase_uncropBase {a : ℝ} (ha : a ≠ 0) (q : Fin 4 → ℤ) (z : Base) :
    cropBase a q (uncropBase a q z) = z := by
  ext j
  fin_cases j <;> simp [uncropBase, cropBase, ha] <;> ring

def cropBaseEquiv {a : ℝ} (ha : a ≠ 0) (q : Fin 4 → ℤ) : Base ≃ᵐ Base where
  toFun := cropBase a q
  invFun := uncropBase a q
  left_inv := uncropBase_cropBase ha q
  right_inv := cropBase_uncropBase ha q
  measurable_toFun := measurable_cropBase a q
  measurable_invFun := measurable_uncropBase a q

end Submission.Obl.k4_crop_angular_finite_tail
