import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Basic
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Raw
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Crossing

/-! Original mass and reference-volume budgets for saturation. -/

namespace Submission.Obl.k4_scalar_true_atlas_terminal_lists

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- The assignment budget bounds the sum of all selected original chart
masses, including all dyadic blocks and all original worlds. -/
theorem RawChartData.packet_budget {p : Data} (hp : Exact p)
    {B k T n : ℕ} {r b h ε : ℝ} {isTrue : Bool}
    {γ : Fin n → Fin (worlds p k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set Trajectory} {C : Fin n → Set Incidence} {u v J : Fin n → ℝ}
    {P : Fin n → MvPolynomial (Fin 2) ℝ}
    (hd : RawChartData p B r b h ε isTrue k T n γ j A C u v J P) :
    (∑ i, ENNReal.ofReal (weight p k (γ i)) * mu p k (γ i) (C i)) ≤ 1 := by
  rcases hd with ⟨hT, hn, hm, hdisj, hsub, hchart, hmass⟩
  have hnull := assigned_incidence_inter_null hp γ j A C hdisj
    (fun i => (hsub i).trans inter_subset_right)
  have hfib (a : Fin (worlds p k)) :
      (∑ i ∈ Finset.univ.filter (fun i => γ i = a), mu p k a (C i)) ≤ mu p k a univ := by
    rw [← measure_biUnion_finset₀]
    · exact measure_mono (subset_univ _)
    · intro i hi i' hi' hne
      have hia := (Finset.mem_filter.mp hi).2
      have hi'a := (Finset.mem_filter.mp hi').2
      change mu p k a (C i ∩ C i') = 0
      simpa only [hia] using hnull i i' hne (hia.trans hi'a.symm)
    · intro i _
      exact (hm i).2.nullMeasurableSet
  calc
    _ = ∑ a, ∑ i ∈ Finset.univ.filter (fun i => γ i = a),
        ENNReal.ofReal (weight p k (γ i)) * mu p k (γ i) (C i) :=
      (Finset.sum_fiberwise Finset.univ γ _).symm
    _ = ∑ a, ENNReal.ofReal (weight p k a) *
        (∑ i ∈ Finset.univ.filter (fun i => γ i = a), mu p k a (C i)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ ≤ ∑ a, ENNReal.ofReal (weight p k a) * mu p k a univ := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (hfib a) zero_le
    _ ≤ 1 := hp.weighted_mass_le k

/-- A true chart floor pays for all crossings under the typical density
ceiling. The loss is fourth order in the common slack. -/
theorem crossing_density_budget (a n Λ s q u v J : ℝ)
    (P : MvPolynomial (Fin 2) ℝ) (hn : 0 ≤ n) (hΛ : 0 < Λ)
    (hq : 0 ≤ q) (hJ : 0 ≤ J) {m : ENNReal}
    (hfloor : ENNReal.ofReal (n * J * q / Λ) ≤ m) :
    ENNReal.ofReal (n * Λ) * (volume.prod Measure.count) (crossing a Λ s q u v J P) ≤
      ENNReal.ofReal (2 * Λ ^ 3 * (2 * Λ + 3)) * m := by
  calc
    _ ≤ ENNReal.ofReal (n * Λ) *
        ENNReal.ofReal ((2 * Λ + 3) * (q * (2 * (Λ * J)))) :=
      mul_le_mul_of_nonneg_left (crossing_volume_le a Λ s q u v J P hΛ.le hJ) zero_le
    _ = ENNReal.ofReal (2 * Λ ^ 3 * (2 * Λ + 3)) *
        ENNReal.ofReal (n * J * q / Λ) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hn hΛ.le),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Λ ^ 3 * (2 * Λ + 3))]
      congr 1
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hfloor zero_le

end Submission.Obl.k4_scalar_true_atlas_terminal_lists
