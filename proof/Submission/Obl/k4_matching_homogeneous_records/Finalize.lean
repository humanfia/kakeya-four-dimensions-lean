import Submission.Obl.k4_matching_homogeneous_records.Select
import Submission.Obl.k4_matching_homogeneous_records.Numerics

namespace Submission.Obl.k4_matching_homogeneous_records

lemma cofinal_selected_direct {J q : ℕ} {d : ℝ} {β : ℕ → ℝ}
    (hs : 0 ≤ d + radius J β 1)
    (hraw : ∀ η : ℝ, 0 < η → ∀ R : ℝ, 2 ≤ R →
      ∃ N : ℝ, R ≤ N ∧ RawRecords J d β q η N) :
    ∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 2 ≤ R → ∃ N : ℝ, R ≤ N ∧
      ∃ u : ℕ → ℝ,
        ((∀ k : ℕ, k ≤ q → 0 ≤ u k) ∧
          (∀ a b : ℕ, a ≤ b → b ≤ q → u a ≤ u b) ∧
          u q ≤ d + radius J β 1 + ε) ∧ Records J d β q u ε N := by
  intro ε hε R hR
  obtain ⟨R₀, hR₀, hbound⟩ := log_loss_threshold q (d + radius J β 1 + ε / 2) (ε / 2)
    (by linarith) (by positivity)
  obtain ⟨N, hRN, hrawN⟩ := hraw (ε / 2) (by positivity) (max R R₀)
    (hR.trans (le_max_left _ _))
  have hN₂ : 2 ≤ N := hR.trans ((le_max_left _ _).trans hRN)
  obtain ⟨u, hu₀, humono, huq, hrec⟩ := records_of_raw
    (by linarith : 1 < N) (by positivity : 0 ≤ ε / 2) (by positivity : 0 ≤ ε / 2)
    (by linarith) (hbound N ((le_max_right _ _).trans hRN)) hrawN
  have he : ε / 2 + ε / 2 = ε := by ring
  exact ⟨N, (le_max_left _ _).trans hRN, u, ⟨hu₀, humono, by linarith⟩,
    by simpa only [he] using hrec⟩

end Submission.Obl.k4_matching_homogeneous_records
