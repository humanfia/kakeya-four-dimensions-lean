-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.ScalarFamilyCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.SmallProjectionScalars
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.ScalarAlgebra

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open scoped Pointwise

theorem SmallScalarProjection.weaken {δ K L t : ℝ} {A : Finset ℝ}
    (h : SmallScalarProjection δ A K t) (hKL : K ≤ L) : SmallScalarProjection δ A L t :=
  h.mono Finset.Subset.rfl (mul_le_mul_of_nonneg_right hKL (Nat.cast_nonneg _))

/-- Any finite family of small-projection scalars has a small cover. -/
theorem small_projection_family_cover (A S : Finset ℝ) {δ q C σ K : ℝ}
    (hδ : 0 < δ) (hδq : δ ≤ q) (hq1 : q ≤ 1) (hC : 0 ≤ C) (hK : 0 < K)
    (hA : A.Nonempty) (hAF : RealFiniteFrostman δ C σ A)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b)
    (hbudget : 12 * K * C * q ^ σ ≤ 1)
    (hsmall : ∀ t ∈ S, SmallScalarProjection δ A K t) :
    RealCoverBound δ S ((12 * K / q) * (A.card : ℝ)) := by
  classical
  have hq : 0 < q := hδ.trans_le hδq
  obtain ⟨m, cc, hcS, hcsep, hcover⟩ := exists_separated_cover S.finite_toSet.totallyBounded hδ
  let T := Finset.univ.image cc
  have hTS : T ⊆ S := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    exact hcS i
  have hTsep : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → δ ≤ dist a b := by
    intro a ha b hb hne
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    exact (hcsep i j (fun hij => hne (hij ▸ rfl))).le
  have hccinj : Function.Injective cc := by
    intro i j hij
    by_contra hne
    have hh := hcsep i j hne
    rw [hij, dist_self] at hh
    linarith
  have hTc : T.card = m := by
    rw [Finset.card_image_iff.mpr (fun i _ j _ hij => hccinj hij)]
    simp
  have hf (t : ℝ) (ht : t ∈ T) : ∃ (n : ℕ) (centers : Fin n → ℝ),
      Covers δ ((fun p : ℝ × ℝ => p.1 + t * p.2) '' (↑(A ×ˢ A) : Set (ℝ × ℝ))) centers ∧
        (n : ℝ) ≤ K * (A.card : ℝ) := by
    obtain ⟨n, centers, hc, hn⟩ := hsmall t (hTS ht)
    refine ⟨n, centers, ?_, hn⟩
    rintro x ⟨p, hp, rfl⟩
    exact hc (Finset.add_mem_add (Finset.mem_product.mp hp).1
      (Finset.mem_image.mpr ⟨p.2, (Finset.mem_product.mp hp).2, rfl⟩))
  have hh := small_projection_scalar_count A T hδ hδq hq1 hC hK hA hAF hsep hTsep hbudget hf
  rw [hTc] at hh
  refine ⟨m, cc, hcover, ?_⟩
  have hd : (m : ℝ) ≤ (12 * K * (A.card : ℝ)) / q :=
    (le_div_iff₀ hq).mpr (by nlinarith)
  convert hd using 1 <;> ring

/-- Two products of initial small-projection scalars remain small after
one addition. Only the initial multiplicative factors need a lower bound. -/
theorem product_sum_scalar_small (A S : Finset ℝ) {δ c K : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hK : 0 ≤ K) (hA : A.Nonempty)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b)
    (hS : ∀ s ∈ S, c ≤ s ∧ s ≤ 1)
    (hbase : SmallScalarProjection δ A K 1)
    (hsmall : ∀ s ∈ S, SmallScalarProjection δ A K s) :
    ∀ t ∈ S * S + S * S,
      SmallScalarProjection δ A (9 * (6 * (K + 144 * K ^ 2 / c + 144 * K ^ 2 / c)) ^ 3) t := by
  classical
  have hprod (t : ℝ) (ht : t ∈ S * S) :
      SmallScalarProjection δ A (144 * K ^ 2 / c) t := by
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_mul.mp ht
    have hup : 0 < u := hc.trans_le (hS u hu).1
    have hh := (hsmall u hu).mul hδ hup (hS u hu).2 hK hK hA hsep (hsmall v hv)
    apply hh.weaken
    have hm := div_le_div_of_nonneg_left (by positivity : 0 ≤ 144 * K ^ 2) hc (hS u hu).1
    convert hm using 1 <;> ring
  intro t ht
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp ht
  exact SmallScalarProjection.add hδ hK (by positivity) (by positivity) hA hsep hbase
    (hprod u hu) (hprod v hv)

/-- A family with small scalar projections has small two-product entropy,
provided the near-collision budget holds for the enlarged projection bound. -/
theorem product_sum_scalar_cover (A S : Finset ℝ) {δ c q C σ K : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hK : 0 < K)
    (hδq : δ ≤ q) (hq1 : q ≤ 1) (hC : 0 ≤ C)
    (hA : A.Nonempty) (hAF : RealFiniteFrostman δ C σ A)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b)
    (hS : ∀ s ∈ S, c ≤ s ∧ s ≤ 1)
    (hbase : SmallScalarProjection δ A K 1)
    (hsmall : ∀ s ∈ S, SmallScalarProjection δ A K s)
    (hbudget : 12 * (9 * (6 * (K + 144 * K ^ 2 / c + 144 * K ^ 2 / c)) ^ 3) * C * q ^ σ ≤ 1) :
    RealCoverBound δ (S * S + S * S)
      ((12 * (9 * (6 * (K + 144 * K ^ 2 / c + 144 * K ^ 2 / c)) ^ 3) / q) * (A.card : ℝ)) := by
  apply small_projection_family_cover A (S * S + S * S) hδ hδq hq1 hC (by positivity)
    hA hAF hsep hbudget
  exact product_sum_scalar_small A S hδ hc hK.le hA hsep hS hbase hsmall

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
