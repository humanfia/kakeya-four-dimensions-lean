import Submission.Obl.k4_tempered_grid_selection.SelectionSequence
import Submission.Lib.K4Homogenization.ProfileCompactness

/-! Select the full worlds on which the bounded parameter exponents converge. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- Countably many bounded world parameters can be made asymptotically constant
on a selected family at a subpower loss of incidence mass. -/
theorem world_parameter_selection {Ω Λ : Type*} [MeasurableSpace Ω]
    (N : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (μ : ℕ → Measure Ω) (label : ℕ → Ω → Λ)
    (f : ℕ → ℕ → Λ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k j z, |f k j z| ≤ C) :
    ∃ (ψ : ℕ → ℕ) (B : ℕ → ℕ) (T : ℕ → Set Λ) (a : ℕ → ℝ),
      StrictMono ψ ∧
      Submission.Obl.k4_tempered_grid_selection.Subpower (N ∘ ψ) (fun k => (B k : ℝ)) ∧
      (∀ j, |a j| ≤ C) ∧
      (∀ j ε, 0 < ε → ∀ᶠ k in atTop, ∀ z ∈ T k, |f (ψ k) j z - a j| < ε) ∧
      (∀ k, μ (ψ k) univ ≤ (B k : ENNReal) * μ (ψ k) (label (ψ k) ⁻¹' T k)) := by
  obtain ⟨B, T, a, δ, hB, hBsub, ha, hδ, hδt, hfit, hmass⟩ :=
    Submission.Obl.k4_tempered_grid_selection.countable_type_selection
      N hN hNt μ label f C hC hf
  obtain ⟨a', ψ, hψ, hat, ha'⟩ :=
    Submission.Lib.K4Homogenization.bounded_profile_subsequence a C ha
  refine ⟨ψ, B ∘ ψ, T ∘ ψ, a', hψ, ?_, ha', ?_, fun k => hmass (ψ k)⟩
  · constructor
    · intro k
      exact hBsub.1 (ψ k)
    · intro ε hε
      exact hψ.tendsto_atTop.eventually (hBsub.2 ε hε)
  · intro j ε hε
    have hδlim := hδt.comp hψ.tendsto_atTop
    have halim : Tendsto (fun k => |a (ψ k) j - a' j|) atTop (𝓝 0) := by
      simpa using ((hat j).sub_const (a' j)).abs
    filter_upwards [hψ.tendsto_atTop.eventually (hfit j),
      hδlim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2)),
      halim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))] with k hk hδε haε z hz
    have htri := abs_add_le (f (ψ k) j z - a (ψ k) j) (a (ψ k) j - a' j)
    have hfit' := hk z hz
    simp only [sub_add_sub_cancel] at htri
    change δ (ψ k) < ε / 2 at hδε
    change |f (ψ k) j z - a' j| < ε
    linarith


/-- The selection lemma specialized to a varying finite set of worlds. The
quantity being retained can be the world's weighted incidence mass. -/
theorem finite_world_parameter_selection
    (N : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (W : ℕ → ℕ) (mass : (k : ℕ) → Fin (W k) → ENNReal)
    (f : (k : ℕ) → ℕ → Fin (W k) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k j b, |f k j b| ≤ C) :
    ∃ (ψ : ℕ → ℕ) (B : ℕ → ℕ) (S : (k : ℕ) → Finset (Fin (W (ψ k))))
      (a : ℕ → ℝ),
      StrictMono ψ ∧
      Submission.Obl.k4_tempered_grid_selection.Subpower (N ∘ ψ) (fun k => (B k : ℝ)) ∧
      (∀ j, |a j| ≤ C) ∧
      (∀ j ε, 0 < ε → ∀ᶠ k in atTop, ∀ b ∈ S k, |f (ψ k) j b - a j| < ε) ∧
      (∀ k, (∑ b, mass (ψ k) b) ≤ (B k : ENNReal) * ∑ b ∈ S k, mass (ψ k) b) := by
  classical
  let μ : ℕ → Measure ℕ := fun k => ∑ b : Fin (W k), mass k b • Measure.dirac (b : ℕ)
  let F : ℕ → ℕ → ℕ → ℝ := fun k j b => if hb : b < W k then f k j ⟨b, hb⟩ else 0
  have hF : ∀ k j b, |F k j b| ≤ C := by
    intro k j b
    dsimp [F]
    split_ifs with hb
    · exact hf k j ⟨b, hb⟩
    · simpa using hC
  obtain ⟨ψ, B, T, a, hψ, hB, ha, hfit, hmass⟩ :=
    world_parameter_selection N hN hNt μ (fun _ => id) F C hC hF
  let S : (k : ℕ) → Finset (Fin (W (ψ k))) := fun k =>
    Finset.univ.filter (fun b => (b : ℕ) ∈ T k)
  refine ⟨ψ, B, S, a, hψ, hB, ha, ?_, ?_⟩
  · intro j ε hε
    filter_upwards [hfit j ε hε] with k hk b hb
    have hb' : (b : ℕ) ∈ T k := (Finset.mem_filter.mp hb).2
    simpa only [F, dite_eq_left b.isLt] using hk b hb'
  · intro k
    have hμtop : μ (ψ k) univ = ∑ b, mass (ψ k) b := by
      simp [μ, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
    have hμT : μ (ψ k) (T k) = ∑ b ∈ S k, mass (ψ k) b := by
      simp [μ, S, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul,
        Finset.sum_filter, Measure.dirac_apply', Set.indicator, mul_ite]
    simpa only [preimage_id, hμtop, hμT] using hmass k

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
