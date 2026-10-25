import Mathlib

/-!
# Determinant mass from breadth of directions

The spanning step of the multilinear-Kakeya arguments in the paper's Section 6
(`tex-06-isotropic.tex`, proof of Proposition `a05:velocity-graph`: "successive independent
samples have distances at least `b^τ` from the preceding spans with probability bounded
below ... the resulting `n'`-fold determinant is at least a constant times `b^{τ(n'-1)}`";
and the strip filling in the proof of Proposition `a05:qualification`), for finite weighted
families.

* `abs_det_ge_prod_infDist`: for vectors `f 0, …, f (d-1)` of `ℝ^d`,
  `∏ᵢ dist(f i, span{f j : j < i}) ≤ |det [f 0; …; f (d-1)]|` (Gram–Schmidt).
* `det_weight_of_breadth`: if every subspace of dimension `< d` leaves weight at least
  `c * W` of a finite weighted family of directions `e` at distance `≥ ρ`, where `W` is the
  total weight, then `(c ρ)^d W^d ≤ ∑_{T : Fin d → ι} |det [e (T 0); …]| ∏ w (T i)`.

Applied to the lines of one family through a point `x` (weights `w k · 1[x ∈ tube k]`,
the family repeated `d` times), the right side is the integrand of the determinant
multilinear Kakeya inequality at `x`, so this supplies the per-cell lower bound
`θ · mass^d ≤ F` with `θ = (c ρ)^d` that a power-mean budget against multilinear Kakeya
consumes.
-/

namespace Submission.Lib.K4DeterminantBreadth

open InnerProductSpace Module

noncomputable section

/-- Successive distances to the spans of the preceding vectors bound the determinant from
below: `∏ᵢ dist(f i, span (f '' Iio i)) ≤ |det|` (rows `f i`). -/
theorem abs_det_ge_prod_infDist (n : ℕ) (f : Fin n → EuclideanSpace ℝ (Fin n)) :
    ∏ i, Metric.infDist (f i)
        (Submodule.span ℝ (f '' Set.Iio i) : Set (EuclideanSpace ℝ (Fin n))) ≤
      |(Matrix.of fun i j => f i j).det| := by
  classical
  have h : finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by simp
  set b := gramSchmidtOrthonormalBasis h f with hb
  have e1 : (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det f =
      (Matrix.of fun i j => f i j).det := by
    rw [Basis.det_apply, ← Matrix.det_transpose]
    congr 1
  have hdet : |(Matrix.of fun i j => f i j).det| = |b.toBasis.det f| := by
    have hsm := congrArg (fun F : (EuclideanSpace ℝ (Fin n)) [⋀^Fin n]→ₗ[ℝ] ℝ => F f)
      (AlternatingMap.eq_smul_basis_det (EuclideanSpace.basisFun (Fin n) ℝ).toBasis b.toBasis.det)
    simp only [AlternatingMap.smul_apply, smul_eq_mul] at hsm
    rw [← e1, hsm, abs_mul]
    rcases OrthonormalBasis.det_to_matrix_orthonormalBasis_real b
      (EuclideanSpace.basisFun (Fin n) ℝ) with h1 | h1 <;> simp [h1]
  rw [hdet, gramSchmidtOrthonormalBasis_det, Finset.abs_prod]
  refine Finset.prod_le_prod₀ (fun i _ => Metric.infDist_nonneg) (fun i _ => ?_)
  set g := gramSchmidt ℝ f i with hg
  set p : EuclideanSpace ℝ (Fin n) :=
    ∑ k ∈ Finset.Iio i, (ℝ ∙ gramSchmidt ℝ f k).starProjection (f i) with hp
  have hgp : g = f i - p := gramSchmidt_def ℝ f i
  have hpmem : p ∈ Submodule.span ℝ (f '' Set.Iio i) := by
    rw [← span_gramSchmidt_Iio ℝ f i]
    refine Submodule.sum_mem _ (fun k hk => ?_)
    have hk' : k ∈ Set.Iio i := by simpa using hk
    have hmem : (ℝ ∙ gramSchmidt ℝ f k).starProjection (f i) ∈ (ℝ ∙ gramSchmidt ℝ f k) :=
      Submodule.coe_mem _
    exact Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_image_of_mem _ hk')) hmem
  have hinf : Metric.infDist (f i) (Submodule.span ℝ (f '' Set.Iio i) :
      Set (EuclideanSpace ℝ (Fin n))) ≤ ‖g‖ := by
    calc _ ≤ dist (f i) p := Metric.infDist_le_dist_of_mem hpmem
      _ = ‖g‖ := by rw [dist_eq_norm, hgp]
  by_cases hg0 : g = 0
  · rw [hg0, norm_zero] at hinf
    exact hinf.trans (abs_nonneg _)
  · have hne : gramSchmidtNormed ℝ f i ≠ 0 := by
      simp [gramSchmidtNormed, ← hg, hg0]
    rw [gramSchmidtOrthonormalBasis_apply h hne]
    have hgpo : ⟪g, p⟫_ℝ = 0 := by
      rw [hp, inner_sum]
      refine Finset.sum_eq_zero (fun k hk => ?_)
      have hki : k ≠ i := (Finset.mem_Iio.mp hk).ne
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
        (Submodule.coe_mem ((ℝ ∙ gramSchmidt ℝ f k).orthogonalProjectionOnto (f i)))
      have : (ℝ ∙ gramSchmidt ℝ f k).starProjection (f i) = a • gramSchmidt ℝ f k := by
        rw [Submodule.starProjection_apply, ← ha]
      rw [this, inner_smul_right, hg, gramSchmidt_orthogonal ℝ f hki.symm, mul_zero]
    have hfi : f i = g + p := by rw [hgp]; abel
    have hval : ⟪gramSchmidtNormed ℝ f i, f i⟫_ℝ = ‖g‖ := by
      rw [gramSchmidtNormed, ← hg, hfi, inner_smul_left, inner_add_right, hgpo, add_zero,
        real_inner_self_eq_norm_sq]
      have : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg0
      simp only [RCLike.conj_to_real, RCLike.ofReal_real_eq_id, id_eq]
      field_simp
    rw [hval, abs_of_nonneg (norm_nonneg _)]
    exact hinf

variable {ι : Type*} {d : ℕ}

/-- A tuple of directions is `ρ`-good if each is at distance at least `ρ` from the span of
the preceding ones. -/
def Good (e : ι → EuclideanSpace ℝ (Fin d)) (ρ : ℝ) {k : ℕ} (T : Fin k → ι) : Prop :=
  ∀ j : Fin k, ρ ≤ Metric.infDist (e (T j))
    (Submodule.span ℝ ((fun i => e (T i)) '' Set.Iio j) : Set (EuclideanSpace ℝ (Fin d)))

/-- The preceding vectors of an old index are unchanged by appending. -/
theorem image_Iio_castSucc_snoc {k : ℕ} (e : ι → EuclideanSpace ℝ (Fin d)) (T : Fin k → ι)
    (t : ι) (j : Fin k) :
    (fun i => e (Fin.snoc (α := fun _ => ι) T t i)) '' Set.Iio (Fin.castSucc j) =
      (fun i => e (T i)) '' Set.Iio j := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hik : (i : ℕ) < k := lt_of_lt_of_le (Fin.lt_def.mp hi) (by simp [Nat.le_of_lt j.2])
    refine ⟨⟨i, hik⟩, ?_, ?_⟩
    · simp only [Set.mem_Iio, Fin.lt_def] at hi ⊢
      simpa using hi
    · have : Fin.snoc (α := fun _ => ι) T t i = T ⟨i, hik⟩ := by simp [Fin.snoc, hik]; rfl
      simp only [this]
  · rintro ⟨i, hi, rfl⟩
    refine ⟨Fin.castSucc i, ?_, ?_⟩
    · simpa [Set.mem_Iio] using hi
    · simp only [Fin.snoc_castSucc]

/-- The vectors preceding the appended one are the old tuple. -/
theorem image_Iio_last_snoc {k : ℕ} (e : ι → EuclideanSpace ℝ (Fin d)) (T : Fin k → ι)
    (t : ι) :
    (fun i => e (Fin.snoc (α := fun _ => ι) T t i)) '' Set.Iio (Fin.last k) =
      Set.range (fun i => e (T i)) := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hik : (i : ℕ) < k := by simpa [Set.mem_Iio, Fin.lt_def] using hi
    refine ⟨⟨i, hik⟩, ?_⟩
    have : Fin.snoc (α := fun _ => ι) T t i = T ⟨i, hik⟩ := by simp [Fin.snoc, hik]; rfl
    simp only [this]
  · rintro ⟨i, rfl⟩
    refine ⟨Fin.castSucc i, ?_, ?_⟩
    · simp [Set.mem_Iio, Fin.castSucc_lt_last]
    · simp only [Fin.snoc_castSucc]

/-- Appending a vector keeps a tuple good iff it is far from the span of the old ones. -/
theorem good_snoc_iff (e : ι → EuclideanSpace ℝ (Fin d)) (ρ : ℝ) {k : ℕ} (T : Fin k → ι)
    (t : ι) :
    Good e ρ (Fin.snoc T t : Fin (k + 1) → ι) ↔ Good e ρ T ∧
      ρ ≤ Metric.infDist (e t)
        (Submodule.span ℝ (Set.range fun i => e (T i)) : Set (EuclideanSpace ℝ (Fin d))) := by
  constructor
  · intro h
    refine ⟨fun j => ?_, ?_⟩
    · have := h (Fin.castSucc j)
      rwa [image_Iio_castSucc_snoc, Fin.snoc_castSucc] at this
    · have := h (Fin.last k)
      rwa [image_Iio_last_snoc, Fin.snoc_last] at this
  · rintro ⟨hT, ht⟩ j
    induction j using Fin.lastCases with
    | last => rwa [image_Iio_last_snoc, Fin.snoc_last]
    | cast j => rw [image_Iio_castSucc_snoc, Fin.snoc_castSucc]; exact hT j

/-- A sum over `(k + 1)`-tuples splits as a sum over `k`-tuples and a last entry. -/
theorem sum_snoc (k : ℕ) (F : (Fin (k+1) → ι) → ℝ) [Fintype ι] :
    ∑ T, F T = ∑ T : Fin k → ι, ∑ t : ι, F (Fin.snoc T t) := by
  rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ => ι)) (fun p => F (Fin.snocEquiv _ p)) F
    (fun p => rfl), Fintype.sum_prod_type, Finset.sum_comm]
  rfl

open Classical in
/-- The weight of good `k`-tuples is at least `(c W)^k` for `k ≤ d`. -/
theorem good_weight [Fintype ι] (e : ι → EuclideanSpace ℝ (Fin d)) (w : ι → ℝ)
    (hw : ∀ t, 0 ≤ w t) (ρ c : ℝ) (hc : 0 ≤ c)
    (hbroad : ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin d)), finrank ℝ V < d →
      c * ∑ t, w t ≤ ∑ t, if ρ ≤ Metric.infDist (e t) (V : Set _) then w t else 0) :
    ∀ k ≤ d, (c * ∑ t, w t) ^ k ≤
      ∑ T : Fin k → ι, if Good e ρ T then ∏ j, w (T j) else 0 := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [Good]
  | succ k ih =>
    intro hk
    have hW : 0 ≤ c * ∑ t, w t := mul_nonneg hc (Finset.sum_nonneg (fun t _ => hw t))
    rw [sum_snoc]
    have hstep : ∀ T : Fin k → ι, (if Good e ρ T then ∏ j, w (T j) else 0) * (c * ∑ t, w t) ≤
        ∑ t : ι, (if Good e ρ (Fin.snoc T t : Fin (k + 1) → ι) then
          ∏ j, w ((Fin.snoc T t : Fin (k + 1) → ι) j) else 0) := by
      intro T
      have hrank : finrank ℝ (Submodule.span ℝ (Set.range fun i => e (T i))) < d := by
        have := finrank_range_le_card (R := ℝ) (fun i => e (T i))
        simp only [Fintype.card_fin] at this
        exact lt_of_le_of_lt this hk
      have hb := hbroad _ hrank
      by_cases hT : Good e ρ T
      · simp only [hT, ite_true]
        calc (∏ j, w (T j)) * (c * ∑ t, w t)
            ≤ (∏ j, w (T j)) * ∑ t, (if ρ ≤ Metric.infDist (e t)
                (Submodule.span ℝ (Set.range fun i => e (T i)) : Set _) then w t else 0) :=
              mul_le_mul_of_nonneg_left hb (Finset.prod_nonneg (fun j _ => hw _))
          _ = ∑ t, (if Good e ρ (Fin.snoc T t : Fin (k + 1) → ι) then
                ∏ j, w ((Fin.snoc T t : Fin (k + 1) → ι) j) else 0) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun t _ => ?_)
              rw [good_snoc_iff]
              by_cases ht : ρ ≤ Metric.infDist (e t)
                  (Submodule.span ℝ (Set.range fun i => e (T i)) : Set _)
              · simp only [hT, ht, and_self, ite_true, Fin.prod_univ_castSucc, Fin.snoc_castSucc,
                  Fin.snoc_last]
              · simp [ht]
      · simp only [hT, ite_false, zero_mul]
        exact Finset.sum_nonneg (fun t _ => by
          split_ifs
          · exact Finset.prod_nonneg (fun j _ => hw _)
          · exact le_refl _)
    calc (c * ∑ t, w t) ^ (k + 1) = (c * ∑ t, w t) ^ k * (c * ∑ t, w t) := pow_succ _ _
      _ ≤ (∑ T : Fin k → ι, if Good e ρ T then ∏ j, w (T j) else 0) * (c * ∑ t, w t) :=
          mul_le_mul_of_nonneg_right (ih (by omega)) hW
      _ = ∑ T : Fin k → ι, (if Good e ρ T then ∏ j, w (T j) else 0) * (c * ∑ t, w t) :=
          Finset.sum_mul _ _ _
      _ ≤ _ := Finset.sum_le_sum (fun T _ => hstep T)

open Classical in
/-- **Determinant mass from breadth.**  If every subspace of dimension `< d` leaves weight
at least `c * W` of the weighted directions `e` at distance at least `ρ` (`W` the total
weight), then the determinant-weighted `d`-fold sum is at least `(c ρ)^d W^d`. -/
theorem det_weight_of_breadth [Fintype ι] (e : ι → EuclideanSpace ℝ (Fin d)) (w : ι → ℝ)
    (hw : ∀ t, 0 ≤ w t) (ρ c : ℝ) (hρ : 0 ≤ ρ) (hc : 0 ≤ c)
    (hbroad : ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin d)), finrank ℝ V < d →
      c * ∑ t, w t ≤ ∑ t, if ρ ≤ Metric.infDist (e t) (V : Set _) then w t else 0) :
    (c * ρ) ^ d * (∑ t, w t) ^ d ≤
      ∑ T : Fin d → ι, |(Matrix.of fun i j => e (T i) j).det| * ∏ i, w (T i) := by
  have hG := good_weight e w hw ρ c hc hbroad d le_rfl
  calc (c * ρ) ^ d * (∑ t, w t) ^ d = ρ ^ d * (c * ∑ t, w t) ^ d := by ring
    _ ≤ ρ ^ d * ∑ T : Fin d → ι, (if Good e ρ T then ∏ j, w (T j) else 0) :=
        mul_le_mul_of_nonneg_left hG (pow_nonneg hρ d)
    _ = ∑ T : Fin d → ι, ρ ^ d * (if Good e ρ T then ∏ j, w (T j) else 0) := Finset.mul_sum _ _ _
    _ ≤ ∑ T : Fin d → ι, |(Matrix.of fun i j => e (T i) j).det| * ∏ i, w (T i) := by
        refine Finset.sum_le_sum (fun T _ => ?_)
        have hprod : 0 ≤ ∏ i, w (T i) := Finset.prod_nonneg (fun i _ => hw _)
        by_cases hT : Good e ρ T
        · simp only [hT, ↓reduceIte]
          refine mul_le_mul_of_nonneg_right ?_ hprod
          calc ρ ^ d = ∏ _i : Fin d, ρ := by simp
            _ ≤ ∏ i : Fin d, Metric.infDist (e (T i))
                (Submodule.span ℝ ((fun i => e (T i)) '' Set.Iio i) :
                  Set (EuclideanSpace ℝ (Fin d))) :=
                Finset.prod_le_prod₀ (fun _ _ => hρ) (fun i _ => hT i)
            _ ≤ |(Matrix.of fun i j => e (T i) j).det| :=
                abs_det_ge_prod_infDist d (fun i => e (T i))
        · simp only [hT, ↓reduceIte, mul_zero]
          exact mul_nonneg (abs_nonneg _) hprod

end

end Submission.Lib.K4DeterminantBreadth
