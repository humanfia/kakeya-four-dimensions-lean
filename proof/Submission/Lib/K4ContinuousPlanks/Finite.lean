/-
Adapted from: here:o018
-/
import Mathlib

/-! The accepted weighted plank estimate with zero-weight classes permitted. -/

open Set

namespace Submission.Lib.K4ContinuousPlanks

def InFullTracePlank (b u c w e₁ e₂ : EuclideanSpace ℝ (Fin 2)) (a β : ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1,
    |inner ℝ (b + t • u - c - t • w) e₁| ≤ a ∧
    |inner ℝ (b + t • u - c - t • w) e₂| ≤ β

def FiniteFullPlankCap {n : ℕ} (D : ℕ) (b u : Fin n → EuclideanSpace ℝ (Fin 2))
    (ω : Fin n → ℝ) (A : ℝ) : Prop :=
  ∀ (c w e₁ e₂ : EuclideanSpace ℝ (Fin 2)) (a β : ℝ),
    ‖e₁‖ = 1 → ‖e₂‖ = 1 → inner ℝ e₁ e₂ = 0 → 1 ≤ a → a ≤ β → β ≤ D →
    ∀ S : Finset (Fin n),
      (∀ i ∈ S, InFullTracePlank (b i) (u i) c w e₁ e₂ (a / D) (β / D)) →
      ∑ i ∈ S, ω i ≤ A * a * β

noncomputable def plankVisited {n : ℕ} (D : ℕ)
    (b u : Fin n → EuclideanSpace ℝ (Fin 2)) (J : Fin n → Finset (Fin D)) :
    Finset (ℕ × (Fin 2 → ℤ)) := by
  classical
  exact ((Finset.univ.sigma J).image fun p =>
    ((p.2 : ℕ), fun k : Fin 2 =>
      ⌊(D : ℝ) * (b p.1 + (((((p.2 : ℕ) : ℝ) + 1 / 2) / D) • u p.1)) k⌋))

/-- The exact finite weighted plank input, with its loss chosen before the data. -/
def PlankEstimate : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧
  ∀ (D : ℕ), 1 ≤ D → ∀ (n : ℕ)
    (b u : Fin n → EuclideanSpace ℝ (Fin 2)) (ω : Fin n → ℝ)
    (A : ℝ) (J : Fin n → Finset (Fin D)),
    (∀ i, ‖b i‖ ≤ 1 ∧ ‖u i‖ ≤ 1) → (∀ i, 0 < ω i) → 0 < A →
    FiniteFullPlankCap D b u ω A →
    (∀ i, (D : ℝ) ^ (1 - η) ≤ ((J i).card : ℝ)) →
    ∑ i, ω i * ((J i).card : ℝ) ≤
      C * A * (D : ℝ) ^ ε * ((plankVisited D b u J).card : ℝ)

/-- Zero weights can be discarded before using the positive-weight theorem. -/
theorem nonnegative_weighted_plank_estimate (Hplank : PlankEstimate) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (D : ℕ), 1 ≤ D → ∀ (n : ℕ)
      (b u : Fin n → EuclideanSpace ℝ (Fin 2)) (ω : Fin n → ℝ)
      (A : ℝ) (J : Fin n → Finset (Fin D)),
      (∀ i, ‖b i‖ ≤ 1 ∧ ‖u i‖ ≤ 1) → (∀ i, 0 ≤ ω i) → 0 < A →
      FiniteFullPlankCap D b u ω A →
      (∀ i, (D : ℝ) ^ (1 - η) ≤ ((J i).card : ℝ)) →
      ∑ i, ω i * ((J i).card : ℝ) ≤
        C * A * (D : ℝ) ^ ε * ((plankVisited D b u J).card : ℝ) := by
  classical
  obtain ⟨η, hη, C, hC, H⟩ := Hplank ε hε
  refine ⟨η, hη, C, hC, ?_⟩
  intro D hD n b u ω A J hbu hω hA hcap hJ
  let I := {i : Fin n // 0 < ω i}
  let m := Fintype.card I
  let e : Fin m ≃ I := (Fintype.equivFin I).symm
  let g : Fin m → Fin n := fun i => (e i).1
  have hg : Function.Injective g := fun i j hij => e.injective (Subtype.ext hij)
  let b' := b ∘ g
  let u' := u ∘ g
  let ω' := ω ∘ g
  let J' := J ∘ g
  have hcap' : FiniteFullPlankCap D b' u' ω' A := by
    intro c w e₁ e₂ a β he₁ he₂ he ha hab hβ S hS
    calc
      ∑ i ∈ S, ω' i = ∑ i ∈ S.image g, ω i := by
        rw [Finset.sum_image]
        · rfl
        · intro i _ j _ hij
          exact hg hij
      _ ≤ A * a * β := hcap c w e₁ e₂ a β he₁ he₂ he ha hab hβ (S.image g) (by
        intro i hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        exact hS j hj)
  have h := H D hD m b' u' ω' A J' (fun i => hbu (g i)) (fun i => (e i).2)
    hA hcap' (fun i => hJ (g i))
  change (∑ i, ω' i * ((J' i).card : ℝ)) ≤
    C * A * (D : ℝ) ^ ε * ((plankVisited D b' u' J').card : ℝ) at h
  have hsum : (∑ i, ω' i * ((J' i).card : ℝ)) =
      ∑ i : Fin n, ω i * ((J i).card : ℝ) := by
    calc
      _ = ∑ i : I, ω i * ((J i).card : ℝ) :=
        e.sum_comp (fun i : I => ω i * ((J i).card : ℝ))
      _ = _ := by
        have hzero : (∑ i : {i : Fin n // ¬ 0 < ω i}, ω i * ((J i).card : ℝ)) = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          have hz : ω i = 0 := le_antisymm (le_of_not_gt i.2) (hω i)
          simp [hz]
        simpa only [hzero, add_zero] using Fintype.sum_subtype_add_sum_subtype
          (fun i : Fin n => 0 < ω i) (fun i => ω i * ((J i).card : ℝ))
  have hvisited : plankVisited D b' u' J' ⊆ plankVisited D b u J := by
    intro z hz
    obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hz
    apply Finset.mem_image.mpr
    refine ⟨⟨g i, j⟩, ?_, rfl⟩
    simpa only [Finset.mem_sigma, Finset.mem_univ, true_and, J', Function.comp_apply] using hij
  rw [hsum] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr (Finset.card_le_card hvisited)) (by positivity))

end Submission.Lib.K4ContinuousPlanks
