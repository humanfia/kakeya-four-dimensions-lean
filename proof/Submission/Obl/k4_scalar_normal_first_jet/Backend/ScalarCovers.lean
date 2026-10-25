/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarCovers.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarCovers.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.WZ.Obl.wz_slab_local_linearity.Covering
import Submission.WZ.Obl.wz_slab_local_linearity.CoverUpper
import Submission.WZ.Obl.wz_slab_local_linearity.CellProofs.Normalization
import Submission.WZ.Obl.wz_slab_local_linearity.CellProofs.LinearityClasses

/-! Scalar support covering bounds survive the errors in the local collision
identity. The cost is polynomial in the number of bottom-scale error cells. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Set Metric
open WangZahlLot.Obl.wz_slab_local_linearity

theorem intervalAD_mono_exponent {p d e C : ℝ} {S : Set ℝ}
    (hp : 0 < p) (hC : 0 ≤ C) (hde : d ≤ e) (hS : IntervalAD p d C S) :
    IntervalAD p e C S := by
  intro r R a hpr hrR
  obtain ⟨m, c, hcover, hcard⟩ := hS r R a hpr hrR
  refine ⟨m, c, hcover, hcard.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC
  exact Real.rpow_le_rpow_of_exponent_le ((one_le_div (hp.trans_le hpr)).mpr hrR) hde

/-- The prebuilt affine-change theorem has the same covering definition.
Its minimum scale transforms by the actual dilation. -/
theorem intervalAD_affine {p d C a b : ℝ} {S : Set ℝ}
    (hp : 0 < p) (ha : 0 < a) (hS : IntervalAD p d C S) :
    IntervalAD (a * p) d C ((fun x => a * x + b) '' S) :=
  (show CellProofs.Assouad p d C S from hS).affine_image hp ha

theorem intervalAD_contract {p d C a b : ℝ} {S : Set ℝ}
    (hp : 0 < p) (ha : 0 < a) (ha1 : a ≤ 1) (hS : IntervalAD p d C S) :
    IntervalAD p d C ((fun x => a * x + b) '' S) := by
  have h := intervalAD_affine (b := b) hp ha hS
  intro r R c hpr hrR
  exact h r R c ((mul_le_of_le_one_left hp.le ha1).trans hpr) hrR

/-- An interval AD bound supplies a finite list of every occupied ordinary
floor bin, including for an infinite scalar support. -/
theorem intervalAD_grid_list {p d C R a : ℝ} {S : Set ℝ}
    (hp : 0 < p) (hpR : p ≤ R) (hS : IntervalAD p d C S) :
    ∃ K : Finset ℤ, (K.card : ℝ) ≤ 3 * (C * (R / p) ^ d) ∧
      ∀ x ∈ S ∩ Icc a (a + R), ⌊x / p⌋ ∈ K := by
  classical
  obtain ⟨m, c, hcov, hm⟩ := hS p R a le_rfl hpR
  let q : Fin m × Fin 3 → ℤ := fun j => ⌊c j.1 / p⌋ + ((j.2 : ℤ) - 1)
  refine ⟨Finset.univ.image q, ?_, ?_⟩
  · calc
      ((Finset.univ.image q).card : ℝ) ≤ (Fintype.card (Fin m × Fin 3) : ℝ) :=
        Nat.cast_le.mpr (Finset.card_image_le.trans_eq Finset.card_univ)
      _ = 3 * m := by simp; ring
      _ ≤ 3 * (C * (R / p) ^ d) := mul_le_mul_of_nonneg_left hm (by norm_num)
  · intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcov hx)
    obtain ⟨e, he⟩ := CellProofs.floor_div_mem_of_mem_closedBall hp hj
    exact Finset.mem_image.mpr ⟨(j, e), Finset.mem_univ _, he.symm⟩

/-- Interval covering bounds are stable under translation and a bounded
bottom-scale perturbation. This includes the error in the scalar collision
dot-product identity. -/
theorem intervalAD_nearby {p d C b : ℝ} {S B : Set ℝ}
    (hp : 0 < p) (hd : 0 ≤ d) (hC : 0 ≤ C) (n : ℕ)
    (hS : IntervalAD p d C S)
    (hclose : ∀ x ∈ B, ∃ y ∈ S, |x - (y + b)| ≤ (n : ℝ) * p) :
    IntervalAD p d ((2 * (n : ℝ) + 3) * C * (1 + 2 * (n : ℝ)) ^ d) B := by
  intro r R a hpr hrR
  have hr : 0 < r := hp.trans_le hpr
  have hR : 0 < R := hr.trans_le hrR
  have hpR : p ≤ R := hpr.trans hrR
  let R' := R + 2 * (n : ℝ) * p
  let a' := a - b - (n : ℝ) * p
  have hrR' : r ≤ R' := hrR.trans (by
    dsimp [R']
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hp.le])
  obtain ⟨m, c, hcov, hcard⟩ := hS r R' a' hpr hrR'
  have hsmall : CoverUpper (S ∩ Icc a' (a' + R')) r (C * (R' / r) ^ d) :=
    ⟨m, c, hcov, hcard⟩
  have hperturb : ∀ x ∈ B ∩ Icc a (a + R),
      ∃ y ∈ S ∩ Icc a' (a' + R'), |x - (y + b)| ≤ (n : ℝ) * r := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hclose x hx.1
    have hxy' := abs_le.mp hxy
    refine ⟨y, ⟨hy, ?_, ?_⟩, hxy.trans ?_⟩
    · dsimp [a']
      linarith [hx.2.1]
    · dsimp [a', R']
      linarith [hx.2.2]
    · exact mul_le_mul_of_nonneg_left hpr (Nat.cast_nonneg n)
  have hout := hsmall.perturb hr n hperturb
  apply hout.mono_bound
  have hratio : R' / r ≤ (1 + 2 * (n : ℝ)) * (R / r) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hr.le
    dsimp [R']
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sub_nonneg.mpr hpR)]
  calc
    (2 * (n : ℝ) + 3) * (C * (R' / r) ^ d) ≤
        (2 * (n : ℝ) + 3) * (C * ((1 + 2 * (n : ℝ)) * (R / r)) ^ d) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.rpow_le_rpow (by dsimp [R']; positivity) hratio hd
    _ = ((2 * (n : ℝ) + 3) * C * (1 + 2 * (n : ℝ)) ^ d) * (R / r) ^ d := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      ring

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
