import Submission.Obl.k4_scalar_coefficient_clustering.Grid
import Submission.Lib.K4PlankGeometry

namespace Submission.Obl.k4_scalar_coefficient_clustering

open Submission.Lib.K4PlankGeometry (binTime cellCode)

noncomputable section

def markedCells {ι : Type*} [Fintype ι] {D : ℕ} (b u : ι → Plane)
    (J : ι → Finset (Fin D)) : Finset (ℕ × (Fin 2 → ℤ)) :=
  (Finset.univ.sigma J).image (fun q => cellCode D (b q.1) (u q.1) q.2)

def PlankCap {ι : Type*} (D : ℕ) (b u : ι → Plane) (ω : ι → ℝ) (A : ℝ) : Prop :=
  ∀ (c w e₁ e₂ : Plane) (α β : ℝ), ‖e₁‖ = 1 → ‖e₂‖ = 1 → inner ℝ e₁ e₂ = 0 →
    1 ≤ α → α ≤ β → β ≤ (D : ℝ) → ∀ S : Finset ι,
    (∀ i ∈ S, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |inner ℝ (b i + t • u i - c - t • w) e₁| ≤ α / (D : ℝ) ∧
      |inner ℝ (b i + t • u i - c - t • w) e₂| ≤ β / (D : ℝ)) →
    ∑ i ∈ S, ω i ≤ A * α * β

def PlankEstimate (ε η C : ℝ) : Prop :=
  ∀ (D : ℕ), 1 ≤ D → ∀ (n : ℕ) (b u : Fin n → Plane) (ω : Fin n → ℝ)
    (A : ℝ) (J : Fin n → Finset (Fin D)),
    (∀ i, ‖b i‖ ≤ 1 ∧ ‖u i‖ ≤ 1) → (∀ i, 0 < ω i) → 0 < A →
    PlankCap D b u ω A → (∀ i, (D : ℝ) ^ (1 - η) ≤ ((J i).card : ℝ)) →
    ∑ i, ω i * ((J i).card : ℝ) ≤ C * A * (D : ℝ) ^ ε * ((markedCells b u J).card : ℝ)

def PlankInput : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ PlankEstimate ε η C

theorem markedCells_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] {D : ℕ}
    (e : ι ≃ κ) (b u : κ → Plane) (J : κ → Finset (Fin D)) :
    markedCells (b ∘ e) (u ∘ e) (J ∘ e) = markedCells b u J := by
  classical
  ext q
  simp only [markedCells, Finset.mem_image, Finset.mem_sigma, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i, j⟩, hj, rfl⟩
    exact ⟨⟨e i, j⟩, hj, rfl⟩
  · rintro ⟨⟨i, j⟩, hj, rfl⟩
    exact ⟨⟨e.symm i, j⟩, by simpa using hj, by simp⟩

/-- The input is unchanged when a finite family is indexed by any finite type. -/
theorem plankEstimate_fintype {ε η C : ℝ} (h : PlankEstimate ε η C)
    {ι : Type*} [Fintype ι] (D : ℕ) (hD : 1 ≤ D) (b u : ι → Plane)
    (ω : ι → ℝ) (A : ℝ) (J : ι → Finset (Fin D))
    (hbu : ∀ i, ‖b i‖ ≤ 1 ∧ ‖u i‖ ≤ 1) (hω : ∀ i, 0 < ω i) (hA : 0 < A)
    (hcap : PlankCap D b u ω A)
    (hJ : ∀ i, (D : ℝ) ^ (1 - η) ≤ ((J i).card : ℝ)) :
    ∑ i, ω i * ((J i).card : ℝ) ≤ C * A * (D : ℝ) ^ ε * ((markedCells b u J).card : ℝ) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hcap' : PlankCap D (b ∘ e) (u ∘ e) (ω ∘ e) A := by
    intro c w e₁ e₂ α β he₁ he₂ ho hα hαβ hβ S hS
    have hh := hcap c w e₁ e₂ α β he₁ he₂ ho hα hαβ hβ (S.image e) (by
      intro i hi t ht
      rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
      exact hS j hj t ht)
    rw [Finset.sum_image (by exact e.injective.injOn)] at hh
    exact hh
  have hh := h D hD (Fintype.card ι) (b ∘ e) (u ∘ e) (ω ∘ e) A (J ∘ e)
    (fun i => hbu (e i)) (fun i => hω (e i)) hA hcap' (fun i => hJ (e i))
  change (∑ i, (fun j => ω j * ((J j).card : ℝ)) (e i)) ≤ _ at hh
  calc
    (∑ i, ω i * ((J i).card : ℝ)) =
        ∑ i, (fun j => ω j * ((J j).card : ℝ)) (e i) :=
      (e.sum_comp (fun j => ω j * ((J j).card : ℝ))).symm
    _ ≤ _ := by simpa only [markedCells_equiv] using hh

end
end Submission.Obl.k4_scalar_coefficient_clustering
