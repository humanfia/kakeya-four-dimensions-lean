import Submission.Obl.k4_scalar_profile_raw_certification.Certification
import Submission.Obl.k4_discrete_of_terminal_charts.Horizon

open MeasureTheory Set Filter
open scoped ENNReal

namespace Submission.Obl.k4_scalar_profile_raw_certification

lemma homogeneous_comp {N : ℕ → ℝ} {s V : ℝ} {ν : ℕ → Measure State}
    {F : ℝ → ℝ → ℝ} (h : Homogeneous N s V ν F)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) : Homogeneous (N ∘ φ) s V (ν ∘ φ) F := by
  obtain ⟨g, G, hg, hG, ht, hT⟩ := h
  refine ⟨fun k => g (φ k), fun k => G (φ k), ?_, ?_, ?_, ?_⟩
  · intro k r hr hrs
    exact hg (φ k) r hr hrs
  · intro k r u hr hrs hu huV
    exact hG (φ k) r u hr hrs hu huV
  · intro r τ hr hrs hτ
    obtain ⟨c, hc, htail⟩ := ht r τ hr hrs hτ
    exact ⟨c, hc, hφ.tendsto_atTop.eventually htail⟩
  · intro r u τ hr hrs hu huV hτ
    obtain ⟨c, hc, htail⟩ := hT r u τ hr hrs hu huV hτ
    exact ⟨c, hc, hφ.tendsto_atTop.eventually htail⟩

theorem numerical_on_subsequence {N K L c : ℕ → ℝ}
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : Subpower N K) (hL : Subpower N L)
    {d s m S U C₀ : ℝ} (hs : 0 < s) (hsm : s < m) (hU : U < m)
    {angular : ℕ → Bool} {angular₀ : Bool} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hangular : ∀ k, angular (φ k) = angular₀)
    {μ ν : ℕ → Measure State} (hdom : ∀ k, ν k ≤ μ k)
    (hmass : ∀ k, ENNReal.ofReal ((L k)⁻¹) ≤ ν k univ)
    (hraw : ∀ k, Raw (N k) (K k) d s m S U (c k) (angular k) (μ k))
    (hc : HasExponent (N ∘ φ) (c ∘ φ) C₀) {F : ℝ → ℝ → ℝ}
    (hhom : Homogeneous N s (4 * (m + s + 1)) ν F) :
    Numerical d s m S U C₀ angular₀ F := by
  exact numerical_of_raw (fun k => hN (φ k)) (hNt.comp hφ.tendsto_atTop)
    ⟨fun k => hK.1 (φ k),
      Submission.Obl.k4_discrete_of_terminal_charts.subpower_subsequence hK.2 hφ⟩
    ⟨fun k => hL.1 (φ k),
      Submission.Obl.k4_discrete_of_terminal_charts.subpower_subsequence hL.2 hφ⟩
    hs hsm hU hangular (fun k => hdom (φ k)) (fun k => hmass (φ k))
    (fun k => hraw (φ k)) hc (homogeneous_comp hhom hφ)

end Submission.Obl.k4_scalar_profile_raw_certification
