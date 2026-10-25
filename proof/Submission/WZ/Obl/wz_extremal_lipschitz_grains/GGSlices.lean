-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.GGSlices.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.GGCovering
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.GGIsometry

/-!
# Twisted slices of a family near AD slabs

Prop. 4.1, Step 2 of the sticky Kakeya paper, (4.36)–(4.37): if a set `E1` is a union of
horizontal slabs of height `h`, each AD at scale `h` in the direction `a z = (a₀, a₁, 0)` with
`a₀ ≥ 1/2`, and `f (h z) = a₁ / a₀` with `f` Lipschitz, then every twisted slice
`projectedSlice f Ef t` of a set `Ef` within `10 δf` of `E1` is AD at scale `δf`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric
open scoped RealInnerProductSpace

theorem abs_coord_sub_le (p q : Space) (i : Fin 3) : |p i - q i| ≤ ‖p - q‖ := by
  have := PiLp.norm_apply_le (p - q) i
  simpa [Real.norm_eq_abs] using this

/-- The horizontal slab of height `h` with index `z`. -/
def hslab (h : ℝ) (z : ℤ) : Set Space := {p | h * z ≤ p 2 ∧ p 2 < h * (z + 1)}

/-- Slab indices near a height. -/
theorem card_near_le {h d t : ℝ} (hh : 0 < h) (hd : 0 ≤ d) (Zb : Finset ℤ) :
    ((Zb.filter (fun z : ℤ => |h * z - t| ≤ d + h)).card : ℝ) ≤ 2 * (d + h) / h + 3 := by
  set z0 : ℤ := ⌊(t - d - h) / h⌋ with hz0
  set M : ℕ := ⌈2 * (d + h) / h⌉₊ + 1 with hM
  have hsub : Zb.filter (fun z : ℤ => |h * z - t| ≤ d + h) ⊆ Finset.Icc z0 (z0 + M) := by
    intro z hz
    obtain ⟨-, hz⟩ := Finset.mem_filter.mp hz
    rw [abs_le] at hz
    rw [Finset.mem_Icc]
    have h1 : (t - d - h) / h ≤ z := by rw [div_le_iff₀ hh]; linarith
    have h2 : (z : ℝ) ≤ (t + d + h) / h := by rw [le_div_iff₀ hh]; linarith
    have hfl := Int.floor_le ((t - d - h) / h)
    have hfl2 := Int.lt_floor_add_one ((t - d - h) / h)
    have hc := Nat.le_ceil (2 * (d + h) / h)
    have e1 : (t + d + h) / h = (t - d - h) / h + 2 * (d + h) / h := by field_simp; ring
    constructor
    · calc z0 = ⌊(t - d - h) / h⌋ := rfl
        _ ≤ ⌊((z : ℤ) : ℝ)⌋ := Int.floor_le_floor h1
        _ = z := Int.floor_intCast z
    · have h3 : (z : ℝ) ≤ z0 + M := by
        rw [hM]; push_cast; linarith
      exact_mod_cast h3
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  have e2 : (z0 + M + 1 - z0).toNat = M + 1 := by omega
  rw [e2] at hcard
  have h4 : ((Zb.filter (fun z : ℤ => |h * z - t| ≤ d + h)).card : ℝ) ≤ M + 1 := by
    exact_mod_cast hcard
  have h5 : (M : ℝ) ≤ 2 * (d + h) / h + 2 := by
    rw [hM]; push_cast
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 * (d + h) / h by positivity)
    linarith
  linarith

theorem inner_eq_coords (a q : Space) : ⟪a, q⟫ = a 0 * q 0 + a 1 * q 1 + a 2 * q 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  ring

/-- Twisted slices of a set near AD slabs are AD. -/
theorem slices_covering {σ h δf C1 K : ℝ} (hh : 0 < h) (hδf : 0 < δf) (hδf1 : δf ≤ 1 / 10)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hC1 : 0 ≤ C1) (hK : 1 ≤ K) (hhK : h ≤ K * δf)
    (hδK : δf ≤ K * h)
    {E1 Ef : Set Space} (hE1b : E1 ⊆ ball 0 1)
    (Zb : Finset ℤ) (a : ℤ → Space)
    (ha0 : ∀ z ∈ Zb, 1 / 2 ≤ a z 0) (ha1 : ∀ z ∈ Zb, |a z 1| ≤ 1) (ha2 : ∀ z ∈ Zb, a z 2 = 0)
    (hcov : ∀ z ∈ Zb, Covering h (1 - σ) C1 ((fun q => ⟪a z, q⟫) '' (E1 ∩ hslab h z)))
    (hE1 : ∀ p ∈ E1, ∃ z ∈ Zb, p ∈ hslab h z)
    (f : ℝ → ℝ) (hf : ∀ z ∈ Zb, f (h * z) = a z 1 / a z 0)
    (hfL : ∀ s t, |f s - f t| ≤ K * |s - t|)
    (hEf : Ef ⊆ thickening (10 * δf) E1) (t : ℝ) :
    Covering δf (1 - σ) (20800 * K ^ 3 * C1) (projectedSlice f Ef t) := by
  classical
  set D : ℝ := 52 * K ^ 2 * δf with hD
  have hDpos : 0 < D := by positivity
  set Zt := Zb.filter (fun z : ℤ => |h * z - t| ≤ 10 * δf + h) with hZt
  set B : ℤ → Set ℝ := fun z => (fun u => (a z 0)⁻¹ * u + 0) ''
    ((fun q => ⟪a z, q⟫) '' (E1 ∩ hslab h z)) with hB
  have hBcov : ∀ z ∈ Zt, Covering D (1 - σ) C1 (B z) := by
    intro z hz
    have hzb : z ∈ Zb := (Finset.mem_filter.mp hz).1
    have ha : 0 < a z 0 := by linarith [ha0 z hzb]
    have h1 := (hcov z hzb).affine (l := (a z 0)⁻¹) (inv_pos.mpr ha) 0
    apply h1.mono_scale
    have h2 : (a z 0)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ ha (by norm_num)]; linarith [ha0 z hzb]
    have h3 : 2 * h ≤ D := by
      rw [hD]
      have : K ≤ K ^ 2 := by nlinarith
      nlinarith
    calc (a z 0)⁻¹ * h ≤ 2 * h := mul_le_mul_of_nonneg_right h2 hh.le
      _ ≤ D := h3
  have hU := Covering.biUnion Zt hBcov hDpos hC1
  have hclose : ∀ u ∈ projectedSlice f Ef t, ∃ y ∈ ⋃ z ∈ Zt, B z, dist u y ≤ D := by
    rintro u ⟨p, hpE, hpu⟩
    simp only [Prod.mk.injEq] at hpu
    obtain ⟨hu, hpt⟩ := hpu
    subst hu
    obtain ⟨p', hp'E, hpp'⟩ := mem_thickening_iff.mp (hEf hpE)
    obtain ⟨z, hzb, hz⟩ := hE1 p' hp'E
    have hpp'n : ‖p - p'‖ < 10 * δf := by rwa [dist_eq_norm] at hpp'
    have h2 : |p 2 - p' 2| < 10 * δf := (abs_coord_sub_le p p' 2).trans_lt hpp'n
    have hzt : |h * z - t| ≤ 10 * δf + h := by
      obtain ⟨hz1, hz2⟩ := hz
      rw [← hpt, abs_le]; rw [abs_lt] at h2
      constructor <;> linarith
    have hzZt : z ∈ Zt := Finset.mem_filter.mpr ⟨hzb, hzt⟩
    have ha : 0 < a z 0 := by linarith [ha0 z hzb]
    refine ⟨(a z 0)⁻¹ * ⟪a z, p'⟫ + 0, mem_iUnion₂.mpr ⟨z, hzZt, ⟨_, ⟨p', ⟨hp'E, hz⟩, rfl⟩, rfl⟩⟩, ?_⟩
    -- the twisted coordinate of the nearby slab point
    have hy : (a z 0)⁻¹ * ⟪a z, p'⟫ + 0 = p' 0 + f (h * z) * p' 1 := by
      rw [inner_eq_coords, ha2 z hzb, hf z hzb]
      field_simp
      ring
    rw [hy, Real.dist_eq]
    have h0' : |p 0 - p' 0| < 10 * δf := (abs_coord_sub_le p p' 0).trans_lt hpp'n
    have h1' : |p 1 - p' 1| < 10 * δf := (abs_coord_sub_le p p' 1).trans_lt hpp'n
    have hp'1 : |p' 1| ≤ 1 := by
      have h := PiLp.norm_apply_le p' 1
      have h' : ‖p'‖ < 1 := by simpa using hE1b hp'E
      rw [Real.norm_eq_abs] at h
      linarith
    have hfz : |f (h * z)| ≤ 2 := by
      rw [hf z hzb, abs_div, abs_of_pos ha, div_le_iff₀ ha]
      linarith [ha1 z hzb, ha0 z hzb]
    have hft : |f (p 2) - f (h * z)| ≤ 11 * K ^ 2 * δf := by
      have h1 := hfL (p 2) (h * z)
      have h3 : |p 2 - h * z| ≤ 10 * δf + h := by
        rw [abs_sub_comm, hpt]; exact hzt
      have hKK : K ≤ K ^ 2 := by nlinarith
      calc |f (p 2) - f (h * z)| ≤ K * |p 2 - h * z| := h1
        _ ≤ K * (10 * δf + K * δf) := by gcongr; linarith
        _ = 10 * K * δf + K ^ 2 * δf := by ring
        _ ≤ 11 * K ^ 2 * δf := by nlinarith
    have hfp : |f (p 2)| ≤ 2 + 11 * K ^ 2 * δf := by
      have := abs_sub_abs_le_abs_sub (f (p 2)) (f (h * z))
      linarith
    have e1 : p 0 + f (p 2) * p 1 - (p' 0 + f (h * z) * p' 1) =
        (p 0 - p' 0) + f (p 2) * (p 1 - p' 1) + (f (p 2) - f (h * z)) * p' 1 := by ring
    rw [e1]
    have hK2 : 1 ≤ K ^ 2 := by nlinarith
    calc |(p 0 - p' 0) + f (p 2) * (p 1 - p' 1) + (f (p 2) - f (h * z)) * p' 1|
        ≤ |p 0 - p' 0| + |f (p 2)| * |p 1 - p' 1| + |f (p 2) - f (h * z)| * |p' 1| := by
          have h1 := abs_add_le ((p 0 - p' 0) + f (p 2) * (p 1 - p' 1))
            ((f (p 2) - f (h * z)) * p' 1)
          have h2 := abs_add_le (p 0 - p' 0) (f (p 2) * (p 1 - p' 1))
          have h3 : |f (p 2) * (p 1 - p' 1)| = |f (p 2)| * |p 1 - p' 1| := abs_mul _ _
          have h4 : |(f (p 2) - f (h * z)) * p' 1| = |f (p 2) - f (h * z)| * |p' 1| :=
            abs_mul _ _
          linarith
      _ ≤ 10 * δf + (2 + 11 * K ^ 2 * δf) * (10 * δf) + 11 * K ^ 2 * δf * 1 := by
          have e1 : |f (p 2)| * |p 1 - p' 1| ≤ (2 + 11 * K ^ 2 * δf) * (10 * δf) :=
            mul_le_mul hfp h1'.le (abs_nonneg _) (by positivity)
          have e2 : |f (p 2) - f (h * z)| * |p' 1| ≤ 11 * K ^ 2 * δf * 1 :=
            mul_le_mul hft hp'1 (abs_nonneg _) (by positivity)
          linarith [h0'.le]
      _ ≤ D := by
          rw [hD]
          have : 11 * K ^ 2 * δf * (10 * δf) ≤ 11 * K ^ 2 * δf := by
            have : 10 * δf ≤ 1 := by linarith
            have h0 : 0 ≤ 11 * K ^ 2 * δf := by positivity
            nlinarith
          nlinarith
  have hα : 0 ≤ 1 - σ := by linarith
  have hC := hU.of_close hDpos hα (by positivity) (fun u hu => by
    obtain ⟨y, hy, hd⟩ := hclose u hu
    exact ⟨y, hy, hd⟩)
  have hR := hC.refine_scale hδf (by rw [hD]; nlinarith) hα (by linarith) (by positivity)
  apply hR.mono_constant hδf
  -- the constant
  have h4 : (4 : ℝ) ^ (1 - σ) ≤ 4 := by
    calc (4 : ℝ) ^ (1 - σ) ≤ 4 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := Real.rpow_one 4
  have hZcard : (Zt.card : ℝ) ≤ 25 * K := by
    have := card_near_le (d := 10 * δf) (t := t) hh (by positivity) Zb
    have h5 : 2 * (10 * δf + h) / h + 3 ≤ 25 * K := by
      rw [div_add' _ _ _ hh.ne', div_le_iff₀ hh]
      nlinarith
    rw [hZt]
    linarith
  have hDd : 2 * D / δf = 104 * K ^ 2 := by rw [hD]; field_simp; ring
  rw [hDd]
  have h40 : 0 ≤ (4 : ℝ) ^ (1 - σ) := by positivity
  calc 2 * ((4 : ℝ) ^ (1 - σ) * (Zt.card * C1)) * (104 * K ^ 2)
      ≤ 2 * (4 * (25 * K * C1)) * (104 * K ^ 2) := by
        gcongr
  _ = 20800 * K ^ 3 * C1 := by ring

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
