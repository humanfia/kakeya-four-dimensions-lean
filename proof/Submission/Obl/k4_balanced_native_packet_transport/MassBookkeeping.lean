import Submission.Obl.k4_balanced_native_packet_transport.SelectedBlockLaws
import Submission.Obl.k4_balanced_native_packet_transport.WeightedDomination
import Submission.Obl.k4_quadratic_finite_greedy_cover.Terminal

namespace Submission.Obl.k4_balanced_native_packet_transport

open MeasureTheory Set
noncomputable section

theorem selectedBlockLaw_weighted_restore
    (ν : Measure Traj) (A : Set Traj) (t₀ q : ℝ) (hq : 0 < q)
    (w s : ENNReal) (μ : Measure Inc) (H : Set Inc)
    (hA : ν A ≠ 0) (hAfin : ν A ≠ ⊤) :
    (w * (ENNReal.ofReal q * ν A)) •
      Measure.map (fun p : Inc => (p.1, t₀ + q * p.2))
        (selectedBlockLaw ν A t₀ q hq s μ H) = (w * s) • μ.restrict H := by
  rw [mul_smul, selectedBlockLaw_restore ν A t₀ q hq s μ H hA hAfin, smul_smul]

/-- Disjoint analytical selections use exactly the original source weight,
even when several new blocks have the same parent. -/
theorem selected_family_domination
    {C C' : ℕ} (parent : Fin C' → Fin C)
    (ν : Fin C → Measure Traj) (A : Fin C' → Set Traj)
    (t₀ : Fin C' → ℝ) (q : ℝ) (hq : 0 < q)
    (w s : Fin C → ENNReal) (μ : Fin C → Measure Inc)
    (H : Fin C' → Set Inc) (hH : ∀ i, MeasurableSet (H i))
    (hdisj : ∀ i j, i ≠ j → parent i = parent j → Disjoint (H i) (H j))
    (hA : ∀ i, ν (parent i) (A i) ≠ 0)
    (hAfin : ∀ i, ν (parent i) (A i) ≠ ⊤) :
    let law := fun i => selectedBlockLaw (ν (parent i)) (A i) (t₀ i) q hq
      (s (parent i)) (μ (parent i)) (H i)
    ∀ B : Fin C → Set Inc, (∀ a, MeasurableSet (B a)) →
      (∑ i, (w (parent i) * (ENNReal.ofReal q * ν (parent i) (A i))) *
        law i ((fun p : Inc => (p.1, t₀ i + q * p.2)) ⁻¹' B (parent i))) ≤
      ∑ a, (w a * s a) * μ a (B a) := by
  dsimp only
  apply weighted_pullback_domination_of_disjoint parent
    (fun i p => (p.1, t₀ i + q * p.2)) (fun _ => by fun_prop)
    (fun a => w a * s a) μ _ _ H hH hdisj
  intro i
  exact (selectedBlockLaw_weighted_restore (ν (parent i)) (A i) (t₀ i) q hq
    (w (parent i)) (s (parent i)) (μ (parent i)) (H i) (hA i) (hAfin i)).le

/-- Exact original weighted coverage, with no selected-success normalizer. -/
theorem selected_family_mass
    {C C' : ℕ} (parent : Fin C' → Fin C)
    (ν : Fin C → Measure Traj) (A : Fin C' → Set Traj)
    (t₀ : Fin C' → ℝ) (q : ℝ) (hq : 0 < q)
    (w s : Fin C → ENNReal) (μ : Fin C → Measure Inc)
    (H : Fin C' → Set Inc) (hH : ∀ i, MeasurableSet (H i))
    (hdisj : ∀ i j, i ≠ j → parent i = parent j → Disjoint (H i) (H j))
    (hA : ∀ i, ν (parent i) (A i) ≠ 0)
    (hAfin : ∀ i, ν (parent i) (A i) ≠ ⊤) :
    (∑ i, (w (parent i) * (ENNReal.ofReal q * ν (parent i) (A i))) *
      selectedBlockLaw (ν (parent i)) (A i) (t₀ i) q hq
        (s (parent i)) (μ (parent i)) (H i) univ) =
      ∑ a, (w a * s a) * μ a {p | ∃ i, parent i = a ∧ p ∈ H i} := by
  classical
  calc
    _ = ∑ i, (w (parent i) * s (parent i)) * μ (parent i) (H i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_assoc, selectedBlockLaw_budget_mass (ν (parent i)) (A i)
        (t₀ i) q hq (s (parent i)) (μ (parent i)) (H i) (hA i) (hAfin i), ← mul_assoc]
    _ = _ := by
      symm
      simpa only [true_and, ite_true] using
        Submission.Obl.k4_quadratic_finite_greedy_cover.weighted_assignment_union
          μ (fun a => w a * s a) (fun _ : Fin C' => True) parent H
          (fun i _ => hH i) (fun i j _ _ hne heq => hdisj i j hne heq)

/-- Full original assignments have one total budget, including every block. -/
theorem original_assignment_budget
    {W C T : ℕ} (ν : Fin W → Measure Traj) (w : Fin W → ℝ)
    (γ : Fin C → Fin W) (j : Fin C → Fin (2 ^ T)) (A : Fin C → Set Traj)
    (hprob : ∀ a, IsProbabilityMeasure (ν a))
    (hw : ∀ a, 0 ≤ w a) (hw₁ : ∑ a, w a = 1)
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : ∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i')) :
    (∑ i, ENNReal.ofReal (w (γ i)) *
      (ENNReal.ofReal (1 / (2 : ℝ) ^ T) * ν (γ i) (A i))) ≤ 1 := by
  have hbudget :=
    Submission.Obl.k4_quadratic_atlas_normalization.weighted_assignment_budget_ofReal
      ν w γ j A hprob hw hw₁ hA hdisj
  simp only [Fintype.card_fin] at hbudget
  calc
    _ = ENNReal.ofReal (1 / (2 : ℝ) ^ T) *
        ∑ i, ENNReal.ofReal (w (γ i)) * ν (γ i) (A i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ T) * (2 ^ T : ℕ) := mul_le_mul' le_rfl hbudget
    _ = 1 := by
      have heq : ((2 ^ T : ℕ) : ENNReal) = ENNReal.ofReal ((2 : ℝ) ^ T) := by norm_cast
      rw [heq, ← ENNReal.ofReal_mul (by positivity)]
      simp

/- The following light-packet bound is adapted from this LOT tree o178,
   x0639, `PacketBudgets.lean`, commit 584004b954271834a15b62ddaea1097c68953739. -/
theorem light_packet_mass_le {ι : Type*} [Fintype ι]
    (w m : ι → ENNReal) (θ : ENNReal) (hw : ∑ i, w i ≤ 1) :
    (∑ i ∈ Finset.univ.filter (fun i => m i < θ), w i * m i) ≤ θ := by
  classical
  calc
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => m i < θ), w i * θ := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul' le_rfl (Finset.mem_filter.mp hi).2.le
    _ = θ * ∑ i ∈ Finset.univ.filter (fun i => m i < θ), w i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    _ ≤ θ * ∑ i, w i := by
      apply mul_le_mul' le_rfl
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => bot_le)
    _ ≤ θ * 1 := mul_le_mul' le_rfl hw
    _ = θ := mul_one _

theorem mass_le_heavy_add_threshold {ι : Type*} [Fintype ι]
    (w m : ι → ENNReal) (θ : ENNReal) (hw : ∑ i, w i ≤ 1) :
    (∑ i, w i * m i) ≤
      (∑ i ∈ Finset.univ.filter (fun i => θ ≤ m i), w i * m i) + θ := by
  classical
  calc
    _ = (∑ i ∈ Finset.univ.filter (fun i => θ ≤ m i), w i * m i) +
        ∑ i ∈ Finset.univ.filter (fun i => m i < θ), w i * m i := by
      simpa only [not_le] using
        (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => θ ≤ m i)
          (fun i => w i * m i)).symm
    _ ≤ _ := add_le_add le_rfl (light_packet_mass_le w m θ hw)

theorem heavy_packet_mass_lower {ι : Type*} [Fintype ι]
    (w m : ι → ENNReal) {b θ : ENNReal} (hθ : θ ≠ ⊤)
    (hw : ∑ i, w i ≤ 1) (hmass : b + θ ≤ ∑ i, w i * m i) :
    b ≤ ∑ i ∈ Finset.univ.filter (fun i => θ ≤ m i), w i * m i := by
  classical
  exact ENNReal.le_of_add_le_add_right hθ
    (hmass.trans (mass_le_heavy_add_threshold w m θ hw))

end
end Submission.Obl.k4_balanced_native_packet_transport
