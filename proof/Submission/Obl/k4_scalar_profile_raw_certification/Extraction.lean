import Mathlib

/-!
# Extraction of a constant angular flag and a limiting `c` exponent

Compactness step of o127: along a strictly increasing subsequence a Boolean flag is
constant and `log c_k / log N_k` converges, so `c_k` lies between `N_k ^ (C₀ - τ)` and
`N_k ^ (C₀ + τ)` eventually, for every `τ > 0`.
-/

open Filter Set Topology

namespace Submission.Obl.k4_scalar_profile_raw_certification

/-- A Boolean sequence is constant along some strictly increasing subsequence. -/
theorem exists_subseq_bool_const (a : ℕ → Bool) :
    ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ b : Bool, ∀ k, a (θ k) = b := by
  by_cases h : ∃ᶠ k in atTop, a k = true
  · obtain ⟨θ, hθ, hθa⟩ := extraction_of_frequently_atTop h
    exact ⟨θ, hθ, true, hθa⟩
  · have h' : ∃ᶠ k in atTop, a k = false := by
      rw [not_frequently] at h
      exact (h.mono fun k hk => by simpa using hk).frequently
    obtain ⟨θ, hθ, hθa⟩ := extraction_of_frequently_atTop h'
    exact ⟨θ, hθ, false, hθa⟩

/-- If `N ≥ 2` and `N ^ (-C) ≤ c ≤ N ^ C`, then along a strictly increasing subsequence
`c` has a limiting exponent `C₀` relative to `N`. -/
theorem exists_subseq_exponent (N c : ℕ → ℝ) (C : ℝ) (hN : ∀ k, 2 ≤ N k)
    (hc : ∀ k, N k ^ (-C) ≤ c k ∧ c k ≤ N k ^ C) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ C₀ : ℝ, ∀ τ : ℝ, 0 < τ → ∀ᶠ k in atTop,
      N (ψ k) ^ (C₀ - τ) ≤ c (ψ k) ∧ c (ψ k) ≤ N (ψ k) ^ (C₀ + τ) := by
  have hN1 : ∀ k, 1 < N k := fun k => by linarith [hN k]
  have hN0 : ∀ k, 0 < N k := fun k => by linarith [hN k]
  have hc0 : ∀ k, 0 < c k := fun k =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (hN0 k) _) (hc k).1
  obtain ⟨x, hcx⟩ : ∃ x : ℕ → ℝ, ∀ k, c k = N k ^ x k :=
    ⟨fun k => Real.logb (N k) (c k), fun k =>
      (Real.rpow_logb (hN0 k) (hN1 k).ne' (hc0 k)).symm⟩
  have hxmem : ∀ k, x k ∈ Icc (-C) C := by
    intro k
    have h1 := (hc k).1
    have h2 := (hc k).2
    rw [hcx k] at h1 h2
    exact ⟨(Real.rpow_le_rpow_left_iff (hN1 k)).1 h1,
      (Real.rpow_le_rpow_left_iff (hN1 k)).1 h2⟩
  obtain ⟨C₀, -, ψ, hψ, hlim⟩ := isCompact_Icc.tendsto_subseq hxmem
  refine ⟨ψ, hψ, C₀, fun τ hτ => ?_⟩
  have hmem : ∀ᶠ k in atTop, (x ∘ ψ) k ∈ Ioo (C₀ - τ) (C₀ + τ) :=
    hlim (Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [hmem] with k hk
  rw [hcx (ψ k)]
  exact ⟨(Real.rpow_le_rpow_left_iff (hN1 (ψ k))).2 hk.1.le,
    (Real.rpow_le_rpow_left_iff (hN1 (ψ k))).2 hk.2.le⟩

/-- Extraction of a constant angular flag and a limiting `c` exponent, in the shape of
the conclusion of o127. -/
theorem exists_subseq_flag_exponent (N c : ℕ → ℝ) (C : ℝ) (hN : ∀ k, 2 ≤ N k)
    (hc : ∀ k, N k ^ (-C) ≤ c k ∧ c k ≤ N k ^ C) (angular : ℕ → Bool) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (angular₀ : Bool) (C₀ : ℝ),
      (∀ k, angular (φ k) = angular₀) ∧
      (∀ τ : ℝ, 0 < τ → ∀ᶠ k in atTop,
        N (φ k) ^ (C₀ - τ) ≤ c (φ k) ∧ c (φ k) ≤ N (φ k) ^ (C₀ + τ)) := by
  obtain ⟨θ, hθ, b, hb⟩ := exists_subseq_bool_const angular
  obtain ⟨ψ, hψ, C₀, hC₀⟩ := exists_subseq_exponent (N ∘ θ) (c ∘ θ) C
    (fun k => hN (θ k)) (fun k => hc (θ k))
  exact ⟨θ ∘ ψ, hθ.comp hψ, b, C₀, fun k => hb (ψ k), hC₀⟩

end Submission.Obl.k4_scalar_profile_raw_certification
