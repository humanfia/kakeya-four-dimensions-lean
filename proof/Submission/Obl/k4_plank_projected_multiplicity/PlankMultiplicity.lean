import Submission.Obl.k4_plank_projected_multiplicity.Basic
import Submission.Obl.k4_plank_projected_multiplicity.Multiplicity
import Submission.Obl.k4_scalar_coefficient_clustering.Input

namespace Submission.Obl.k4_plank_projected_multiplicity

open Finset
open Submission.Lib.K4PlankGeometry (Plane cellCode)

noncomputable section

/-- Restrict the plank estimate to any subfamily of traces with sufficiently many marks. -/
theorem plank_rows_bound {ε η C : ℝ}
    (hplank : Submission.Obl.k4_scalar_coefficient_clustering.PlankEstimate ε η C)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ℕ) (hD : 1 ≤ D) (b u : ι → Plane) {A : ℝ} (hA : 0 < A)
    (hbu : ∀ i, ‖b i‖ ≤ 1 ∧ ‖u i‖ ≤ 1)
    (hcap : Submission.Obl.k4_scalar_coefficient_clustering.PlankCap D b u (fun _ => 1) A)
    (J : ι → Finset (Fin D)) (S : Finset ι)
    (hJ : ∀ i ∈ S, (D : ℝ) ^ (1 - η) ≤ ((J i).card : ℝ)) :
    (∑ i ∈ S, ((J i).card : ℝ)) ≤ C * A * (D : ℝ) ^ ε *
      (((S.sigma J).image (fun p => cellCode D (b p.1) (u p.1) p.2)).card : ℝ) := by
  classical
  have hcapS : Submission.Obl.k4_scalar_coefficient_clustering.PlankCap D
      (fun i : S => b i) (fun i : S => u i) (fun _ => 1) A := by
    intro c w e₁ e₂ α β he₁ he₂ ho hα hαβ hβ U hU
    have hh := hcap c w e₁ e₂ α β he₁ he₂ ho hα hαβ hβ (U.image Subtype.val) (by
      intro i hi t ht
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact hU j hj t ht)
    rw [Finset.sum_image (fun i _ j _ h => Subtype.ext h)] at hh
    exact hh
  have hcode : Submission.Obl.k4_scalar_coefficient_clustering.markedCells
      (fun i : S => b i) (fun i : S => u i) (fun i : S => J i) =
        (S.sigma J).image (fun p => cellCode D (b p.1) (u p.1) p.2) := by
    ext z
    simp only [Submission.Obl.k4_scalar_coefficient_clustering.markedCells,
      Finset.mem_image, Finset.mem_sigma, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, j⟩, hj, hz⟩
      exact ⟨⟨i.val, j⟩, ⟨i.property, hj⟩, hz⟩
    · rintro ⟨⟨i, j⟩, ⟨hi, hj⟩, hz⟩
      exact ⟨⟨⟨i, hi⟩, j⟩, hj, hz⟩
  have hh := Submission.Obl.k4_scalar_coefficient_clustering.plankEstimate_fintype hplank D hD
    (fun i : S => b i) (fun i : S => u i) (fun _ => 1) A (fun i : S => J i)
    (fun i => hbu i) (fun _ => zero_lt_one) hA hcapS (fun i => hJ i i.property)
  simp only [one_mul, hcode] at hh
  have hsum : (∑ i : S, ((J i.val).card : ℝ)) = ∑ i ∈ S, ((J i).card : ℝ) :=
    Finset.sum_coe_sort S (fun i => ((J i).card : ℝ))
  rw [hsum] at hh
  exact hh

/-- The weighted plank hypothesis bounds the high-multiplicity incidence tail. -/
theorem plank_high_multiplicity (hplank : PlankEstimate) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (D : ℕ), 1 ≤ D →
        ∀ (b u : ι → Plane) (A : ℝ), 0 < A →
        (∀ i, ‖b i‖ ≤ 1 ∧ ‖u i‖ ≤ 1) →
        Submission.Obl.k4_scalar_coefficient_clustering.PlankCap D b u (fun _ => 1) A →
        ∀ (J : ι → Finset (Fin D)) (M : ℝ), 2 * (C * A * (D : ℝ) ^ ε) ≤ M →
        (∀ q ∈ ((univ : Finset ι).sigma J).image (fun p => cellCode D (b p.1) (u p.1) p.2),
          M ≤ ((((univ : Finset ι).sigma J).filter
            (fun p => cellCode D (b p.1) (u p.1) p.2 = q)).card : ℝ)) →
        (∑ i : ι, ((J i).card : ℝ)) ≤
          2 * (Fintype.card ι : ℝ) * (D : ℝ) ^ (1 - η) := by
  change Submission.Obl.k4_scalar_coefficient_clustering.PlankInput at hplank
  obtain ⟨η, hη, C, hC, hplank⟩ := hplank ε hε
  refine ⟨η, hη, C, hC, ?_⟩
  intro ι _ _ D hD b u A hA hbu hcap J M hM hfiber
  have hDp : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  apply high_multiplicity_pruning J (fun p => cellCode D (b p.1) (u p.1) p.2)
    (Real.rpow_pos_of_pos hDp _).le (by positivity) hM hfiber
  intro S hS
  exact plank_rows_bound hplank D hD b u hA hbu hcap J S hS

end

end Submission.Obl.k4_plank_projected_multiplicity
