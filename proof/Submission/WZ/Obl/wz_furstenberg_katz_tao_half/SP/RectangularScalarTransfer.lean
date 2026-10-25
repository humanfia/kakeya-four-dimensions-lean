-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.RectangularScalarTransfer.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.CartesianScalarExpansion

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open scoped Pointwise

theorem rectangular_projection_image (A B : Finset ℝ) (t : ℝ) :
    ((fun p : ℝ × ℝ => p.1 + t * p.2) '' (↑(A ×ˢ B) : Set (ℝ × ℝ))) =
      (↑(A + realScalarImage t B) : Set ℝ) := by
  classical
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact Finset.add_mem_add (Finset.mem_product.mp hp).1
      (Finset.mem_image.mpr ⟨p.2, (Finset.mem_product.mp hp).2, rfl⟩)
  · intro hx
    obtain ⟨a, ha, y, hy, rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩

/-- Expanding the real line by division by a positive number at most one
preserves the original Frostman cutoff as well. -/
theorem RealFiniteFrostman.div_image_same_scale {δ C σ t : ℝ} {A : Finset ℝ}
    (hA : RealFiniteFrostman δ C σ A) (hδ : 0 < δ) (ht : 0 < t) (ht1 : t ≤ 1) :
    RealFiniteFrostman δ C σ (A.image (fun a => a / t)) := by
  classical
  intro x r hr
  have hrp : 0 < r := hδ.trans_le hr
  have hinj : Function.Injective (fun a : ℝ => a / t) := by
    intro a b hab
    exact (div_left_inj' ht.ne').mp hab
  rw [Finset.filter_image, Finset.card_image_of_injective _ hinj,
    Finset.card_image_of_injective _ hinj]
  have hsub : A.filter (fun a => dist (a / t) x ≤ r) ⊆
      A.filter (fun a => dist a (t * x) ≤ r) := by
    intro a ha
    have hh := (Finset.mem_filter.mp ha).2
    have hid : dist a (t * x) = t * dist (a / t) x := by
      rw [Real.dist_eq, Real.dist_eq]
      calc
        |a - t * x| = |t * (a / t - x)| := by congr 1; field_simp
        _ = _ := by rw [abs_mul, abs_of_pos ht]
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1, ?_⟩
    rw [hid]
    have hm := mul_le_mul_of_nonneg_left hh ht.le
    nlinarith
  exact (show ((A.filter (fun a => dist (a / t) x ≤ r)).card : ℝ) ≤
    ((A.filter (fun a => dist a (t * x) ≤ r)).card : ℝ) by
      exact_mod_cast Finset.card_le_card hsub).trans (hA (t * x) r hr)

/-- Two small rectangular projections yield a small square projection
at the ratio of their scalars. -/
theorem rectangular_scalar_transfer (A B : Finset ℝ) {δ a t K : ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (ha1 : a ≤ 1) (hK : 0 ≤ K) (hA : A.Nonempty)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ dist x y)
    (hfirst : RealCoverBound δ (A + realScalarImage a B) (K * (A.card : ℝ)))
    (hsecond : RealCoverBound δ (A + realScalarImage t B) (K * (A.card : ℝ))) :
    RealCoverBound δ (B + realScalarImage (t / a) B) ((108 * K ^ 2 / a) * (A.card : ℝ)) := by
  classical
  obtain ⟨m, ca, hca, hm⟩ := hfirst
  obtain ⟨n, ct, hct, hn⟩ := hsecond
  have hca' : Covers δ (↑(realScalarImage a B + A) : Set ℝ) ca := by
    simpa only [add_comm] using hca
  obtain ⟨k, cc, hc, hk⟩ := real_ruzsa_sum hδ (realScalarImage a B) A (realScalarImage t B)
    ca ct hca' hct
  have hAc : (A.image (realGridIndex δ)).card = A.card :=
    Finset.card_image_iff.mpr (realGridIndex_injective hδ hsep)
  rw [hAc] at hk
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hprod : (m : ℝ) * (n : ℝ) ≤ (K * (A.card : ℝ)) * (K * (A.card : ℝ)) :=
    mul_le_mul hm hn (Nat.cast_nonneg _) (by positivity)
  have hk' : (k : ℝ) ≤ 36 * K ^ 2 * (A.card : ℝ) := by
    apply (mul_le_mul_iff_left₀ hAp).mp
    nlinarith
  have hcover : RealCoverBound δ (realScalarImage a B + realScalarImage t B)
      (36 * K ^ 2 * (A.card : ℝ)) := ⟨k, cc, hc, hk'⟩
  have haInv : 1 ≤ 1 / a := (le_div_iff₀ ha).mpr (by simpa using ha1)
  have hh := hcover.scale hδ haInv (show |1 / a| ≤ 1 / a by rw [abs_of_pos (by positivity)])
  change RealCoverBound δ (realScalarImage (1 / a) (realScalarImage a B + realScalarImage t B)) _ at hh
  rw [realScalarImage_add, realScalarImage_mul, realScalarImage_mul,
    show 1 / a * a = 1 by field_simp, realScalarImage_one,
    show 1 / a * t = t / a by ring] at hh
  convert hh using 1 <;> ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
