import Submission.Obl.k4_matching_cofinal_palette_selection.Data

namespace Submission.Obl.k4_matching_cofinal_palette_selection

open MeasureTheory

theorem Records.mono {J : ℕ} {d : ℝ} {β : ℕ → ℝ} {r : ℝ → ℝ}
    {l : ℕ → ℝ → ℝ} {q : ℕ} {u : ℕ → ℝ} {ε ε' N : ℝ}
    {n₁ n₂ : ℕ} {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ}
    {π₁ : Fin n₁ → ℝ} {π₂ : Fin n₂ → ℝ}
    {μ : Measure ((Fin n₁ × Fin n₂) × ℝ)} {h : ℕ → ℕ}
    {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}
    (hN : 1 ≤ N) (hε : ε ≤ ε')
    (hr : Records J d β r l q u ε N n₁ n₂ f₁ f₂ π₁ π₂ μ h F S) :
    Records J d β r l q u ε' N n₁ n₂ f₁ f₂ π₁ π₂ μ h F S := by
  rcases hr with ⟨hs₁, hs₂, hc₁, hc₂, hj₁, hj₂, hp₁, hp₂, hsum₁, hsum₂,
    hprob, hm₁, hm₂, hS, hμS, hsupp, hmono, hdyad, hmeas, hrec, hcard, hdesc⟩
  have hpow := Real.rpow_le_rpow_of_exponent_le hN hε
  refine ⟨hs₁.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)),
    hs₂.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)), hc₁, hc₂,
    (fun i j hj t ht => (hj₁ i j hj t ht).trans hpow),
    (fun i j hj t ht => (hj₂ i j hj t ht).trans hpow),
    hp₁, hp₂, hsum₁, hsum₂, hprob, ?_, ?_, hS, hμS, ?_,
    hmono, hdyad, hmeas, hrec, ?_, ?_⟩
  · intro i E hE
    apply (hm₁ i E hE).trans
    gcongr
    exact hp₁ i
  · intro i E hE
    apply (hm₂ i E hE).trans
    gcongr
    exact hp₂ i
  · intro p hp
    obtain ⟨ht, hgap, hjet⟩ := hsupp p hp
    refine ⟨ht, hgap.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)), ?_⟩
    intro j hj hjJ
    obtain ⟨hup, hlo⟩ := hjet j hj hjJ
    refine ⟨hup.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)), ?_⟩
    intro hb
    exact (Real.rpow_le_rpow_of_exponent_le hN (by linarith : -β j - ε' ≤ -β j - ε)).trans
      (hlo hb)
  · intro k hk
    exact (hcard k hk).trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
  · intro a b hab hb x hx
    exact (hdesc a b hab hb x hx).trans
      (Real.rpow_le_rpow_of_exponent_le hN (by linarith))

theorem GoodRecordData.mono {J : ℕ} {d : ℝ} {β : ℕ → ℝ} {r : ℝ → ℝ}
    {l : ℕ → ℝ → ℝ} {q : ℕ} {u : ℕ → ℝ} {ε ε' N θ : ℝ}
    {m z : ℕ → ℕ} {G : Finset ℕ} (hN : 1 ≤ N) (hε : ε ≤ ε')
    (hr : GoodRecordData J d β r l q u ε N m z G θ) :
    GoodRecordData J d β r l q u ε' N m z G θ := by
  rcases hr with ⟨n₁, n₂, f₁, f₂, π₁, π₂, μ, h, F, S, hr, hg⟩
  exact ⟨n₁, n₂, f₁, f₂, π₁, π₂, μ, h, F, S, hr.mono hN hε, hg⟩

end Submission.Obl.k4_matching_cofinal_palette_selection
