import Submission.Lib.K4FinitePlankAtlases.FinitePlankSubset
import Submission.Lib.K4FinitePlankAtlases.Greedy
import Submission.Lib.K4FinitePlankAtlases.Assignments
import Submission.Lib.K4FinitePlankAtlases.IndexMeasure

/-!
Adapted from: here:o049

Original finite-atlas proofs developed by session x0147, through commit e50df50.
The weighted plank input is a parameter; no obligation module is imported.
-/

namespace Submission.Lib.K4FinitePlankAtlases

open Set MeasureTheory
attribute [local instance] Classical.propDecidable
open scoped BigOperators

/-- A candidate full-time plank at the discrete mesh resolution. -/
structure NormalizedPlank (D : ℕ) where
  center : Plane
  speed : Plane
  axis₁ : Plane
  axis₂ : Plane
  narrow : ℝ
  wide : ℝ
  unit₁ : ‖axis₁‖ = 1
  unit₂ : ‖axis₂‖ = 1
  orthogonal : inner ℝ axis₁ axis₂ = 0
  narrow_ge_one : 1 ≤ narrow
  narrow_le_wide : narrow ≤ wide
  wide_le_D : wide ≤ (D : ℝ)

def NormalizedPlank.contains {D : ℕ} (p : NormalizedPlank D) (b u : Plane) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1,
    |inner ℝ (b + t • u - p.center - t • p.speed) p.axis₁| ≤ p.narrow / (D : ℝ) ∧
    |inner ℝ (b + t • u - p.center - t • p.speed) p.axis₂| ≤ p.wide / (D : ℝ)

def NormalizedPlank.fitSet {D : ℕ} {ι : Type*} (p : NormalizedPlank D)
    (b u : ι → Plane) : Set ι := {i | p.contains (b i) (u i)}

/-- Disjoint heavy full-time planks cover all but the amount allowed by the
weighted mark estimate. Every packet keeps its original trajectory weights. -/
theorem finite_plank_cover (hweighted : WeightedPlankEstimate) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (D : ℕ), 1 ≤ D → ∀ (n : ℕ) (b u : Fin n → Plane)
      (ω : Fin n → ℝ) (J : Fin n → Finset (Fin D)),
    (∀ i, ‖b i‖ ≤ 1 ∧ ‖u i‖ ≤ 1) → (∀ i, 0 < ω i) →
    (∀ i, (D : ℝ) ^ (1 - η) ≤ ((J i).card : ℝ)) →
    ∀ A : ℝ, 0 < A → ∃ m : ℕ, ∃ p : Fin m → NormalizedPlank D,
      ∃ S : Fin m → Finset (Fin n),
      m ≤ n ∧ (m : ℝ) * A ≤ ∑ i, ω i ∧ Pairwise (fun i j => Disjoint (S i) (S j)) ∧
      (∀ j, (∀ i ∈ S j, (p j).contains (b i) (u i)) ∧
        A * (p j).narrow * (p j).wide ≤ ∑ i ∈ S j, ω i) ∧
      ∑ i ∈ Finset.univ.filter (fun i => ∀ j, i ∉ S j), ω i * ((J i).card : ℝ) ≤
        C * A * (D : ℝ) ^ ε * ((visitedCells b u J).card : ℝ) := by
  intro ε hε
  obtain ⟨η, hη, C, hC, hbound⟩ := weighted_plank_subset hweighted ε hε
  refine ⟨η, hη, C, hC, ?_⟩
  intro D hD n b u ω J hbu hω hmarks A hA
  classical
  letI : MeasurableSpace (Fin n) := ⊤
  letI : MeasurableSingletonClass (Fin n) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  let μ : Measure (Fin n) := indexMeasure ω
  letI : IsFiniteMeasure μ := indexMeasure_finite _
  let F : NormalizedPlank D → Set (Fin n) := fun p => p.fitSet b u
  have hF (p : NormalizedPlank D) : MeasurableSet (F p) := MeasurableSpace.measurableSet_top
  let threshold : NormalizedPlank D → ℝ := fun p => A * p.narrow * p.wide
  have hthreshold (p : NormalizedPlank D) : A ≤ threshold p := by
    have hw : 1 ≤ p.wide := p.narrow_ge_one.trans p.narrow_le_wide
    dsimp [threshold]
    nlinarith [mul_le_mul_of_nonneg_left p.narrow_ge_one hA.le,
      mul_le_mul_of_nonneg_left hw (show 0 ≤ A * p.narrow from mul_nonneg hA.le (zero_le_one.trans p.narrow_ge_one))]
  obtain ⟨l, hg, hstop⟩ := exists_threshold_greedy_exhaustion F hF threshold μ hA hthreshold
  let P : Fin l.length → NormalizedPlank D := l.get
  let assignments : Fin l.length → Set (Fin n) := firstAssignment (fun j => F (P j))
  let S : Fin l.length → Finset (Fin n) := fun j => Finset.univ.filter (fun i => i ∈ assignments j)
  have hS (j : Fin l.length) : (↑(S j) : Set (Fin n)) = assignments j := by
    ext i
    simp [S]
  have hmass (j : Fin l.length) : threshold (P j) ≤ μ.real (assignments j) := by
    have h := hg.mass_at j
    rw [residualMeasure_eq F hF, measureReal_restrict_apply (hF _)] at h
    have heq : F (l.get j) ∩ (⋃ b ∈ l.take j.val, F b)ᶜ =
        F (l.get j) \ ⋃ b ∈ l.take j.val, F b := by ext x; rfl
    rw [heq] at h
    simpa only [assignments, P, firstAssignment_get] using h
  let R : Finset (Fin n) := Finset.univ.filter (fun i => ∀ j, i ∉ S j)
  have hU : (⋃ j, assignments j) = ⋃ p ∈ l, F p := by
    calc
      _ = ⋃ j : Fin l.length, F (P j) := iUnion_firstAssignment _
      _ = ⋃ p ∈ l, F p := by
        ext i
        simp only [Set.mem_iUnion, exists_prop, P]
        exact (List.exists_mem_iff_get (l := l) (p := fun p => i ∈ F p)).symm
  have hR : (↑R : Set (Fin n)) = (⋃ p ∈ l, F p)ᶜ := by
    rw [← hU]
    ext i
    simp [R, S]
  have hcap : ResidualPlankCap (D := D) b u ω A R := by
    intro c w e₁ e₂ a β he₁ he₂ he ha hab hβ T hT hfit
    let p : NormalizedPlank D := ⟨c, w, e₁, e₂, a, β, he₁, he₂, he, ha, hab, hβ⟩
    have hsub : (↑T : Set (Fin n)) ⊆ F p ∩ (⋃ q ∈ l, F q)ᶜ := by
      intro i hi
      exact ⟨hfit i hi, (show (↑R : Set (Fin n)) = _ from hR) ▸ hT hi⟩
    have h := hstop p
    rw [residualMeasure_eq F hF, measureReal_restrict_apply (hF p)] at h
    have hμ := measureReal_mono (μ := μ) hsub
    have hTmass : μ.real (↑T : Set (Fin n)) = ∑ i ∈ T, ω i := by
      rw [show μ.real (↑T : Set (Fin n)) = _ from indexMeasure_real_finset ω (fun i => (hω i).le) _]
      simp
    rw [hTmass] at hμ
    exact hμ.trans h.le
  have hdisj : Pairwise (fun i j => Disjoint (S i) (S j)) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp (firstAssignment_disjoint (fun j => F (P j)) hij)
      (by simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hx)
      (by simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hy)
  have hne (j : Fin l.length) : (S j).Nonempty := by
    by_contra hj
    have hempty : S j = ∅ := Finset.not_nonempty_iff_eq_empty.mp hj
    have h := hmass j
    rw [← hS j, hempty] at h
    simp only [Finset.coe_empty, measureReal_empty] at h
    exact (not_le_of_gt (hA.trans_le (hthreshold (P j)))) h
  have hcount : l.length ≤ n := by
    calc
      _ = (Finset.univ : Finset (Fin l.length)).card := by simp
      _ ≤ ((Finset.univ : Finset (Fin l.length)).biUnion S).card :=
        Finset.card_le_card_biUnion (fun i _ j _ hij => hdisj hij) (fun j _ => hne j)
      _ ≤ Fintype.card (Fin n) := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  have hweightcount : (l.length : ℝ) * A ≤ ∑ i, ω i := by
    calc
      _ = ∑ _j : Fin l.length, A := by simp
      _ ≤ ∑ j, ∑ i ∈ S j, ω i := by
        apply Finset.sum_le_sum
        intro j _
        apply (hthreshold (P j)).trans
        simpa only [S] using (hmass j).trans_eq
          (indexMeasure_real_finset ω (fun i => (hω i).le) (assignments j))
      _ = ∑ i ∈ (Finset.univ : Finset (Fin l.length)).biUnion S, ω i :=
        (Finset.sum_biUnion (fun i _ j _ hij => hdisj hij)).symm
      _ ≤ ∑ i, ω i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => (hω i).le)
  refine ⟨l.length, P, S, hcount, hweightcount, hdisj, ?_, ?_⟩
  · intro j
    constructor
    · intro i hi
      exact ((Finset.mem_filter.mp hi).2).1
    · have h := hmass j
      rw [show μ.real (assignments j) = _ from indexMeasure_real_finset ω (fun i => (hω i).le) _] at h
      exact h
  · exact hbound D hD (Fin n) b u ω J hbu hω hmarks A R hA hcap

/-- A full trajectory-weight floor becomes an unnormalized marked-incidence
floor using the original duration lower bounds. -/
theorem marked_packet_floor {D : ℕ} {ι : Type*} [DecidableEq ι]
    (ω : ι → ℝ) (J : ι → Finset (Fin D)) (S : Finset ι)
    {η m : ℝ} (hD : 1 ≤ D) (hω : ∀ i ∈ S, 0 ≤ ω i)
    (hm : m ≤ ∑ i ∈ S, ω i)
    (hmarks : ∀ i ∈ S, (D : ℝ) ^ (1 - η) ≤ ((J i).card : ℝ)) :
    (D : ℝ) ^ (1 - η) * m / (D : ℝ) ≤
      (∑ i ∈ S, ω i * ((J i).card : ℝ)) / (D : ℝ) := by
  have hD₀ : (0 : ℝ) < D := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  apply div_le_div_of_nonneg_right _ hD₀.le
  calc
    _ ≤ (D : ℝ) ^ (1 - η) * ∑ i ∈ S, ω i :=
      mul_le_mul_of_nonneg_left hm (Real.rpow_pos_of_pos hD₀ _).le
    _ = ∑ i ∈ S, (D : ℝ) ^ (1 - η) * ω i := Finset.mul_sum ..
    _ ≤ _ := Finset.sum_le_sum (fun i hi => by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hmarks i hi) (hω i hi))

end Submission.Lib.K4FinitePlankAtlases
