import Mathlib
import ChallengeDeps
import Submission.Obl.k4_directional_jet_path_transfer.Geometry
set_option linter.unusedVariables false

/-!
# `Submission.k4_directional_jet_path_transfer`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_directional_jet_path_transfer`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_directional_jet_path_transfer/`
belong to this obligation.
-/

theorem Submission.k4_directional_jet_path_transfer : ∀ n N s : ℕ, ∀ K : ℝ, 0 < K → ∃ q : ℕ, ∃ L : ℝ, max s N ≤ q ∧ 0 < L ∧ ∀ A : ℝ, 2 ≤ A → ∀ a b c : EuclideanSpace ℂ (Fin n), ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 → ∀ H : EuclideanSpace ℂ (Fin n) → ℂ, (fun U : Set (EuclideanSpace ℂ (Fin n)) => ContDiffOn ℂ ((⊤ : ENat) : WithTop ENat) H U → (∀ p v : EuclideanSpace ℂ (Fin n), (∀ t ∈ Metric.thickening ((8 * A)⁻¹) (segment ℝ (0 : ℂ) 1), p + t • v ∈ U) → ∀ V : ℝ, 0 ≤ V → (∀ j : ℕ, j ≤ N → ‖iteratedDeriv j (fun t : ℂ => H (p + t • v)) 0‖ ≤ V) → ‖H (p + v)‖ ≤ (8 * A) ^ K * V) → ∀ V : ℝ, 0 ≤ V → (((∀ z ∈ Metric.closedBall a ((8 * A)⁻¹), ‖H z‖ ≤ V) → (∀ z ∈ Metric.closedBall c ((8 * A)⁻¹), ‖H z‖ ≤ A ^ L * V) ∧ ∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℂ j H c‖ ≤ A ^ L * V) ∧ ((∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℂ j H c‖ ≤ V) → ∀ z ∈ Metric.closedBall a ((8 * A)⁻¹), ‖H z‖ ≤ A ^ L * V))) (Metric.thickening (A⁻¹) (segment ℝ a b ∪ segment ℝ b c)) := by
  intro n N s K hK
  obtain ⟨J, hJ, hCauchy⟩ := Submission.Obl.k4_directional_jet_path_transfer.exists_cauchy_power (max s N)
  obtain ⟨D, hD, hSlice⟩ := Submission.Obl.k4_directional_jet_path_transfer.exists_slice_power N K
  refine ⟨max s N, 2 * D + 3 * J, le_rfl, by positivity, ?_⟩
  intro A hA a b c ha hb hc H hH hlaw V hV
  let S := segment ℝ a b ∪ segment ℝ b c
  have hball (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ S) :
      Metric.closedBall x ((8 * A)⁻¹) ⊆ Metric.thickening A⁻¹ S :=
    Submission.Obl.k4_directional_jet_path_transfer.closedBall_subset_thickening_of_mem hx
      (Submission.Obl.k4_directional_jet_path_transfer.small_radius hA).2.2
  have haS : a ∈ S := Or.inl (left_mem_segment ℝ a b)
  have hbS : b ∈ S := Or.inl (right_mem_segment ℝ a b)
  have hcS : c ∈ S := Or.inr (right_mem_segment ℝ b c)
  have hab : segment ℝ a b ⊆ S := Set.subset_union_left
  have hbc : segment ℝ b c ⊆ S := Set.subset_union_right
  have hcb : segment ℝ c b ⊆ S := by rw [segment_symm ℝ c b]; exact hbc
  have hba : segment ℝ b a ⊆ S := by rw [segment_symm ℝ b a]; exact hab
  exact Submission.Obl.k4_directional_jet_path_transfer.transfer_along_path
    Metric.isOpen_thickening hH hA (le_max_right s N) hD hJ hlaw (hSlice A hA) (hCauchy A hA)
    (hball a haS) (hball b hbS) (hball c hcS)
    (Submission.Obl.k4_directional_jet_path_transfer.admissibleStep_of_segment hA ha hb hab)
    (Submission.Obl.k4_directional_jet_path_transfer.admissibleStep_of_segment hA hb hc hbc)
    (Submission.Obl.k4_directional_jet_path_transfer.admissibleStep_of_segment hA hc hb hcb)
    (Submission.Obl.k4_directional_jet_path_transfer.admissibleStep_of_segment hA hb ha hba) hV
