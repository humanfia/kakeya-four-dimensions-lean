/- Adapted from this LOT tree, obligation o029, session x0089, commits
2c6ac76 and 18abde3, file Submission/Obl/k4_bounded_sign_choice/FiniteSamples.lean.
Namespace and imports changed to the owned o051 module. -/

import Mathlib

/-!
A finite sample set for the sign cells of finitely many real polynomials in one
variable. This is the elementary order-theoretic ingredient of definable choice.
-/

namespace Submission.Obl.k4_scalar_sign_choice

open Set

/-- Roots, unit shifts of roots, and midpoints of pairs of roots suffice to
sample all the complementary intervals. Zero handles an empty root set. -/
def rootSamples (R : Set ℝ) : Set ℝ :=
  {0} ∪ R ∪ ((fun a => a + 1) '' R) ∪ ((fun a => a - 1) '' R) ∪
    ((fun ab : ℝ × ℝ => (ab.1 + ab.2) / 2) '' (R ×ˢ R))

theorem finite_rootSamples {R : Set ℝ} (hR : R.Finite) : (rootSamples R).Finite :=
  ((((finite_singleton 0).union hR).union (hR.image _)).union (hR.image _)).union
    ((hR.prod hR).image _)

theorem mem_rootSamples_zero (R : Set ℝ) : 0 ∈ rootSamples R := by
  simp [rootSamples]

theorem mem_rootSamples_root {R : Set ℝ} {a : ℝ} (ha : a ∈ R) :
    a ∈ rootSamples R := by
  simp only [rootSamples, mem_union, mem_singleton_iff, mem_image, mem_prod]
  exact Or.inl (Or.inl (Or.inl (Or.inr ha)))

theorem mem_rootSamples_add_one {R : Set ℝ} {a : ℝ} (ha : a ∈ R) :
    a + 1 ∈ rootSamples R := by
  simp only [rootSamples, mem_union, mem_singleton_iff, mem_image, mem_prod]
  exact Or.inl (Or.inl (Or.inr ⟨a, ha, rfl⟩))

theorem mem_rootSamples_sub_one {R : Set ℝ} {a : ℝ} (ha : a ∈ R) :
    a - 1 ∈ rootSamples R := by
  simp only [rootSamples, mem_union, mem_singleton_iff, mem_image, mem_prod]
  exact Or.inl (Or.inr ⟨a, ha, rfl⟩)

theorem mem_rootSamples_midpoint {R : Set ℝ} {a b : ℝ} (ha : a ∈ R) (hb : b ∈ R) :
    (a + b) / 2 ∈ rootSamples R :=
  Or.inr ⟨(a, b), ⟨ha, hb⟩, rfl⟩

/-- Every point outside a finite set shares a complementary interval with a
point in the finite sample set. -/
theorem exists_rootSample_same_cut {R : Set ℝ} (hR : R.Finite) {t : ℝ} (ht : t ∉ R) :
    ∃ u ∈ rootSamples R, ∀ r ∈ R,
      (r < t ∧ r < u) ∨ (t < r ∧ u < r) := by
  classical
  let L := {r ∈ R | r < t}
  let U := {r ∈ R | t < r}
  have hL : L.Finite := hR.subset (fun _ h => h.1)
  have hU : U.Finite := hR.subset (fun _ h => h.1)
  have htr (r : ℝ) (hr : r ∈ R) : r < t ∨ t < r :=
    lt_or_gt_of_ne (fun heq => ht (heq ▸ hr))
  rcases L.eq_empty_or_nonempty with hemptyL | hneL <;>
    rcases U.eq_empty_or_nonempty with hemptyU | hneU
  · refine ⟨0, mem_rootSamples_zero _, ?_⟩
    intro r hr
    rcases htr r hr with h | h
    · have : r ∈ L := ⟨hr, h⟩
      simp [hemptyL] at this
    · have : r ∈ U := ⟨hr, h⟩
      simp [hemptyU] at this
  · obtain ⟨b, hb, hmin⟩ := Set.exists_min_image U id hU hneU
    refine ⟨b - 1, mem_rootSamples_sub_one hb.1, ?_⟩
    intro r hr
    rcases htr r hr with h | h
    · have : r ∈ L := ⟨hr, h⟩
      simp [hemptyL] at this
    · right
      have hbr : b ≤ r := hmin r ⟨hr, h⟩
      exact ⟨h, by linarith⟩
  · obtain ⟨a, ha, hmax⟩ := Set.exists_max_image L id hL hneL
    refine ⟨a + 1, mem_rootSamples_add_one ha.1, ?_⟩
    intro r hr
    rcases htr r hr with h | h
    · left
      have hra : r ≤ a := hmax r ⟨hr, h⟩
      exact ⟨h, by linarith⟩
    · have : r ∈ U := ⟨hr, h⟩
      simp [hemptyU] at this
  · obtain ⟨a, ha, hmax⟩ := Set.exists_max_image L id hL hneL
    obtain ⟨b, hb, hmin⟩ := Set.exists_min_image U id hU hneU
    have hab : a < b := ha.2.trans hb.2
    refine ⟨(a + b) / 2, mem_rootSamples_midpoint ha.1 hb.1, ?_⟩
    intro r hr
    rcases htr r hr with h | h
    · left
      have hra : r ≤ a := hmax r ⟨hr, h⟩
      exact ⟨h, by linarith⟩
    · right
      have hbr : b ≤ r := hmin r ⟨hr, h⟩
      exact ⟨h, by linarith⟩

theorem not_mem_of_same_cut {R : Set ℝ} {t u : ℝ}
    (hcut : ∀ r ∈ R, (r < t ∧ r < u) ∨ (t < r ∧ u < r))
    {r : ℝ} (hr : r ∈ uIcc t u) : r ∉ R := by
  intro hR
  rcases hcut r hR with h | h
  · have := hr.1
    exact (lt_min h.1 h.2).not_ge this
  · have := hr.2
    exact (max_lt h.1 h.2).not_ge this

/-- The sign of a continuous real function is constant along a root-free
interval. -/
theorem sign_eq_of_nonzero_interval {f : ℝ → ℝ} (hf : Continuous f) {t u : ℝ}
    (hnz : ∀ r ∈ uIcc t u, f r ≠ 0) : SignType.sign (f t) = SignType.sign (f u) := by
  have hc : ContinuousOn (fun r => SignType.sign (f r)) (uIcc t u) := by
    intro r hr
    exact (continuousAt_sign_of_ne_zero (hnz r hr)).comp_continuousWithinAt
      hf.continuousAt.continuousWithinAt
  exact (isPreconnected_uIcc.image _ hc).subsingleton
    ⟨t, left_mem_uIcc, rfl⟩ ⟨u, right_mem_uIcc, rfl⟩

/-- A finite root set samples every sign vector of a continuous family whose
nonzero members have all their roots in that set. -/
theorem exists_rootSample_same_sign {η : Type} (f : η → ℝ → ℝ)
    (hf : ∀ i, Continuous (f i)) {R : Set ℝ} (hR : R.Finite)
    (hroots : ∀ i r, (∃ w, f i w ≠ 0) → f i r = 0 → r ∈ R) (t : ℝ) :
    ∃ u ∈ rootSamples R, ∀ i, SignType.sign (f i t) = SignType.sign (f i u) := by
  by_cases ht : t ∈ R
  · exact ⟨t, mem_rootSamples_root ht, fun _ => rfl⟩
  obtain ⟨u, hu, hcut⟩ := exists_rootSample_same_cut hR ht
  refine ⟨u, hu, ?_⟩
  intro i
  by_cases hn : ∃ w, f i w ≠ 0
  · apply sign_eq_of_nonzero_interval (hf i)
    intro r hr hz
    exact not_mem_of_same_cut hcut hr (hroots i r hn hz)
  · push Not at hn
    simp [hn]

/-- The roots of the nonzero members of a finite polynomial family form a
finite set; zero polynomials impose no boundary. -/
def familyRoots {η : Type} (p : η → Polynomial ℝ) : Set ℝ :=
  {t | ∃ i, p i ≠ 0 ∧ (p i).eval t = 0}

theorem finite_familyRoots {η : Type} [Finite η] (p : η → Polynomial ℝ) :
    (familyRoots p).Finite := by
  classical
  rw [show familyRoots p = ⋃ i, {t | p i ≠ 0 ∧ (p i).eval t = 0} by
    ext t
    simp [familyRoots]]
  apply Set.finite_iUnion
  intro i
  by_cases hp : p i = 0
  · simp [hp]
  · exact (Polynomial.finite_setOfPred_isRoot hp).subset (fun _ h => h.2)

theorem exists_polynomial_sign_sample {η : Type} [Finite η] (p : η → Polynomial ℝ)
    (t : ℝ) : ∃ u ∈ rootSamples (familyRoots p),
      ∀ i, SignType.sign ((p i).eval t) = SignType.sign ((p i).eval u) := by
  apply exists_rootSample_same_sign (fun i t => (p i).eval t)
    (fun i => (p i).continuous) (finite_familyRoots p)
  intro i r hi hr
  refine ⟨i, ?_, hr⟩
  rintro hp
  obtain ⟨w, hw⟩ := hi
  simp [hp] at hw

/-- The least eligible member of the finite sample set. -/
def sampleChoiceGraph {η : Type} (p : η → Polynomial ℝ)
    (B : Set (η → SignType)) (t : ℝ) : Prop :=
  (fun i => SignType.sign ((p i).eval t)) ∈ B ∧
    t ∈ rootSamples (familyRoots p) ∧
    ∀ u, (fun i => SignType.sign ((p i).eval u)) ∈ B →
      u ∈ rootSamples (familyRoots p) → t ≤ u

theorem exists_unique_sampleChoice {η : Type} [Finite η] (p : η → Polynomial ℝ)
    (B : Set (η → SignType))
    (hne : ∃ t, (fun i => SignType.sign ((p i).eval t)) ∈ B) :
    ∃! t, sampleChoiceGraph p B t := by
  obtain ⟨t, ht⟩ := hne
  obtain ⟨u, hu, hsign⟩ := exists_polynomial_sign_sample p t
  have heq : (fun i => SignType.sign ((p i).eval t)) =
      (fun i => SignType.sign ((p i).eval u)) := funext hsign
  let E := {u | (fun i => SignType.sign ((p i).eval u)) ∈ B ∧
    u ∈ rootSamples (familyRoots p)}
  have hE : E.Finite := (finite_rootSamples (finite_familyRoots p)).subset (fun _ h => h.2)
  have hneE : E.Nonempty := ⟨u, heq ▸ ht, hu⟩
  obtain ⟨a, ha, hmin⟩ := Set.exists_min_image E id hE hneE
  refine ⟨a, ⟨ha.1, ha.2, fun u hB hu => hmin u ⟨hB, hu⟩⟩, ?_⟩
  intro b hb
  exact le_antisymm (hb.2.2 a ha.1 ha.2) (hmin b ⟨hb.1, hb.2.1⟩)

end Submission.Obl.k4_scalar_sign_choice
