import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.Setup

/-!
# Basic almost-everywhere facts at one sample

Dyadic block endpoints are null for incidence laws dominated by `ν ⊗ dt`; off them, a point
lies in the fitted set of at most one label of a family, and nesting identifies the
coarse label of a point in a fine label.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

theorem ae_not_dyadic (ν : Measure α) [SFinite ν] (μ : Measure (α × ℝ)) (C : ℝ≥0∞)
    (hdom : μ ≤ C • ν.prod volume) (T : ℕ) :
    ∀ᵐ p ∂μ, ∀ k : ℕ, p.2 ≠ (k : ℝ) / 2 ^ T := by
  rw [ae_iff]
  have hsub : {p : α × ℝ | ¬ ∀ k : ℕ, p.2 ≠ (k : ℝ) / 2 ^ T} ⊆
      ⋃ k : ℕ, (univ : Set α) ×ˢ {(k : ℝ) / 2 ^ T} := by
    intro p hp
    push Not at hp
    obtain ⟨k, hk⟩ := hp
    exact mem_iUnion.mpr ⟨k, ⟨mem_univ _, hk⟩⟩
  refine measure_mono_null hsub ?_
  refine measure_iUnion_null (fun k => ?_)
  refine le_antisymm ((hdom _).trans ?_) zero_le
  rw [Measure.smul_apply, Measure.prod_prod, Real.volume_singleton, mul_zero, smul_zero]

/-- Two distinct dyadic blocks of the same depth meet at most at an endpoint. -/
theorem eq_of_mem_blk {T : ℕ} {a a' : ℕ} {t : ℝ} (ht : t ∈ blk T a) (ht' : t ∈ blk T a')
    (hnd : ∀ k : ℕ, t ≠ (k : ℝ) / 2 ^ T) : a = a' := by
  by_contra hne
  have hpos : (0 : ℝ) < 2 ^ T := by positivity
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · -- a + 1 ≤ a', so t ≤ (a+1)/2^T ≤ a'/2^T ≤ t
    have h1 : ((a : ℝ) + 1) ≤ (a' : ℝ) := by exact_mod_cast hlt
    have h2 : t ≤ ((a : ℝ) + 1) / 2 ^ T := ht.2
    have h3 : (a' : ℝ) / 2 ^ T ≤ t := ht'.1
    have h4 : ((a : ℝ) + 1) / 2 ^ T ≤ (a' : ℝ) / 2 ^ T :=
      div_le_div_of_nonneg_right h1 hpos.le
    have : t = (a' : ℝ) / 2 ^ T := le_antisymm (h2.trans h4) h3
    exact hnd a' this
  · have h1 : ((a' : ℝ) + 1) ≤ (a : ℝ) := by exact_mod_cast hlt
    have h2 : t ≤ ((a' : ℝ) + 1) / 2 ^ T := ht'.2
    have h3 : (a : ℝ) / 2 ^ T ≤ t := ht.1
    have h4 : ((a' : ℝ) + 1) / 2 ^ T ≤ (a : ℝ) / 2 ^ T :=
      div_le_div_of_nonneg_right h1 hpos.le
    have : t = (a : ℝ) / 2 ^ T := le_antisymm (h2.trans h4) h3
    exact hnd a this

/-- Off dyadic endpoints, a point lies in the assignment block of at most one label. -/
theorem Fam.label_unique (f : Fam α)
    (hdisj : ∀ i i', i ≠ i' → f.j i = f.j i' → Disjoint (f.A i) (f.A i'))
    {p : α × ℝ} (hnd : ∀ k : ℕ, p.2 ≠ (k : ℝ) / 2 ^ f.T) {i i' : Fin f.n}
    (hi : p.1 ∈ f.A i ∧ p.2 ∈ f.I i) (hi' : p.1 ∈ f.A i' ∧ p.2 ∈ f.I i') : i = i' := by
  have hj : (f.j i : ℕ) = f.j i' := eq_of_mem_blk hi.2 hi'.2 hnd
  have hj' : f.j i = f.j i' := Fin.ext hj
  by_contra hne
  exact Set.disjoint_left.mp (hdisj i i' hne hj') hi.1 hi'.1

/-- Nesting identifies the coarse label of a point of a fine label. -/
theorem nest_label {fine coarse : Fam α} (hnest : Nests fine coarse)
    (hdisj : ∀ i i', i ≠ i' → coarse.j i = coarse.j i' → Disjoint (coarse.A i) (coarse.A i'))
    (hBA : ∀ i, coarse.B i ⊆ coarse.A i) (hfBA : ∀ i, fine.B i ⊆ fine.A i)
    {p : α × ℝ} (hnd : ∀ k : ℕ, p.2 ≠ (k : ℝ) / 2 ^ coarse.T) {i : Fin fine.n} {j : Fin coarse.n}
    (hpi : p.1 ∈ fine.B i ∧ p.2 ∈ fine.I i) (hpj : p.1 ∈ coarse.B j ∧ p.2 ∈ coarse.I j) :
    ∃ h : Fin coarse.n, fine.A i ⊆ coarse.A h ∧ fine.I i ⊆ coarse.I h ∧ h = j := by
  obtain ⟨h, hA, hI⟩ := hnest i
  refine ⟨h, hA, hI, ?_⟩
  exact coarse.label_unique hdisj hnd ⟨hA (hfBA i hpi.1), hI hpi.2⟩ ⟨hBA j hpj.1, hpj.2⟩

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
