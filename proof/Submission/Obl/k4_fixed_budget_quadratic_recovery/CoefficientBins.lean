/- Adapted within this LOT tree from o120/x0402, commit 70956fccdfd7e9924a3fa094355c65a03c16ee9c,
Submission/Obl/k4_unbounded_width_exclusion/CoefficientBins.lean. -/
import Submission.Obl.k4_fixed_budget_quadratic_recovery.QuadraticCoefficients
import Submission.Lib.K4IncidenceWitnesses
import Submission.Lib.K4MeshListRecovery.PosteriorLists

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open Finset MeasureTheory

def coefficientBin (ρ : ℝ) (c : Fin 6 → ℝ) : Fin 6 → ℤ :=
  fun i => ⌊c i / ρ⌋

def binCoefficients (ρ : ℝ) (b : Fin 6 → ℤ) : Fin 6 → ℝ :=
  fun i => ρ * (b i : ℝ)

theorem coefficientBin_error {ρ : ℝ} (hρ : 0 < ρ) (c : Fin 6 → ℝ) (i : Fin 6) :
    |c i - binCoefficients ρ (coefficientBin ρ c) i| ≤ ρ := by
  have hlo := mul_le_mul_of_nonneg_left (Int.floor_le (c i / ρ)) hρ.le
  have hhi := mul_lt_mul_of_pos_left (Int.lt_floor_add_one (c i / ρ)) hρ
  have heq : ρ * (c i / ρ) = c i := by field_simp
  rw [heq] at hlo hhi
  change |c i - ρ * (⌊c i / ρ⌋ : ℝ)| ≤ ρ
  rw [abs_le]
  constructor <;> linarith

theorem coefficientBin_value_error {ρ R t z : ℝ} (hρ : 0 < ρ) (hR : 1 ≤ R)
    (c : Fin 6 → ℝ) (ht : |t| ≤ R) (hz : |z| ≤ R) :
    |quadraticValue c t z - quadraticValue (binCoefficients ρ (coefficientBin ρ c)) t z| ≤
      6 * ρ * R ^ 2 :=
  quadraticValue_sub_bound hρ.le hR (coefficientBin_error hρ c) ht hz

theorem coefficientBin_close {ρ : ℝ} (hρ : 0 < ρ) {c c' : Fin 6 → ℝ}
    (h : ∀ i, |c i - c' i| ≤ ρ) (i : Fin 6) :
    |((coefficientBin ρ c) i : ℝ) - ((coefficientBin ρ c') i : ℝ)| ≤ 3 := by
  have h1 := coefficientBin_error hρ c i
  have h2 := coefficientBin_error hρ c' i
  have htri : |ρ * ((coefficientBin ρ c) i : ℝ) -
      ρ * ((coefficientBin ρ c') i : ℝ)| ≤ 3 * ρ := by
    calc
      _ = |(ρ * ((coefficientBin ρ c) i : ℝ) - c i) + (c i - c' i) +
          (c' i - ρ * ((coefficientBin ρ c') i : ℝ))| := by congr 1; ring
      _ ≤ |ρ * ((coefficientBin ρ c) i : ℝ) - c i| + |c i - c' i| +
          |c' i - ρ * ((coefficientBin ρ c') i : ℝ)| := by
        grw [abs_add_le, abs_add_le]
      _ ≤ 3 * ρ := by
        rw [abs_sub_comm (ρ * _)]
        change |c i - binCoefficients ρ (coefficientBin ρ c) i| + |c i - c' i| +
          |c' i - binCoefficients ρ (coefficientBin ρ c') i| ≤ 3 * ρ
        linarith [h i]
  rw [← mul_sub, abs_mul, abs_of_pos hρ] at htri
  exact (mul_le_mul_iff_of_pos_left hρ).mp (htri.trans_eq (by ring))

def coefficientNeighbors {β : Type*} [Fintype β]
    (code : β → Fin 6 → ℤ) (b : β) : Finset β :=
  Finset.univ.filter (fun a => ∀ i, |(code a i : ℝ) - (code b i : ℝ)| ≤ 3)

/-- Neighbor lists are bounded by a numerical constant, independent of
the number of original candidates or occupied coefficient bins. -/
theorem coefficientNeighbors_card {β : Type*} [Fintype β]
    (code : β → Fin 6 → ℤ) (hcode : Function.Injective code) (b : β) :
    (coefficientNeighbors code b).card ≤ 15 ^ 6 := by
  classical
  let S := (coefficientNeighbors code b).image code
  have hdiam : ∀ p ∈ S, ∀ q ∈ S, ∀ i, |(p i : ℝ) - (q i : ℝ)| ≤ 6 := by
    intro p hp q hq i
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hq
    have h₁ := (Finset.mem_filter.mp ha).2 i
    have h₂ := (Finset.mem_filter.mp ha').2 i
    calc
      _ ≤ |(code a i : ℝ) - (code b i : ℝ)| + |(code b i : ℝ) - (code a' i : ℝ)| :=
        abs_sub_le _ _ _
      _ ≤ 6 := by rw [abs_sub_comm (code b i : ℝ)]; linarith
  have hcard := Submission.Lib.K4IncidenceWitnesses.card_pi_grid_of_diameter S (by norm_num) hdiam
  have heq : S.card = (coefficientNeighbors code b).card :=
    Finset.card_image_of_injective _ hcode
  rw [heq] at hcard
  norm_num at hcard
  exact_mod_cast hcard

/-- Agreement of two independent posterior coefficient bins yields
bounded measurable lists retaining its full unnormalized agreement mass. -/
theorem recover_coefficient_neighbor_mass
    {X β : Type*} [MeasurableSpace X] [Fintype β]
    (μ : Measure X) [IsFiniteMeasure μ]
    (π : X → β → ℝ) (hπmeas : ∀ a, Measurable (fun x => π x a))
    (hπnonneg : ∀ x a, 0 ≤ π x a) (hπmass : ∀ x, ∑ a, π x a ≤ 1)
    (code : β → Fin 6 → ℤ) (hcode : Function.Injective code)
    (mass : ℝ) (hpair : mass ≤ ∫ x,
      ∑ b, π x b * ∑ a ∈ coefficientNeighbors code b, π x a ∂μ) :
    ∃ L : X → Finset β, Submission.Lib.K4OriginalLists.MeasurableLists L ∧
      (∀ x, (L x).card ≤ 15 ^ 6) ∧
      mass ≤ ∫ x, ∑ a ∈ L x, π x a ∂μ := by
  obtain ⟨L, hLmeas, hL, hmass⟩ :=
    Submission.Lib.K4MeshListRecovery.recover_posterior_neighbor_mass μ π hπmeas hπnonneg
      hπmass Finset.univ (15 ^ 6) (coefficientNeighbors code)
      (fun b => ⟨Finset.subset_univ _, coefficientNeighbors_card code hcode b⟩) mass hpair
  exact ⟨L, hLmeas, fun x => (hL x).2, hmass⟩

end Submission.Obl.k4_fixed_budget_quadratic_recovery
