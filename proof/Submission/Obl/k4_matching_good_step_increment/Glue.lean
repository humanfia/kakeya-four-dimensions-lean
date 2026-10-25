import Submission.Obl.k4_matching_cofinal_palette_selection
import Submission.Obl.k4_matching_switching_target_certificate
import Submission.Obl.k4_matching_good_step_increment.Numerics

namespace Submission.Obl.k4_matching_good_step_increment

theorem good_step_from_children (hp : PaletteBound) (hEnd : EndpointBound)
    (D J : ℕ) (hD : 1 ≤ D) (hDJ : D < J) (d : ℝ) (hd : 0 ≤ d)
    (β : ℕ → ℝ) (hβ : BetaValid D J β) :
    ∀ γ : ℝ, 0 < γ → ∀ δ : ℝ, 0 < δ → ∃ Q : ℕ,
      ∀ q : ℕ, Q ≤ q → 1 ≤ q →
      ∀ (A : Finset ℕ) (m z : ℕ → ℕ) (u : ℕ → ℝ),
      Admissible J β (radius J β) (accuracy (radius J β)) q A m z γ →
      (∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 2 ≤ R →
        ∃ N : ℝ, R ≤ N ∧ RecordData J d β (radius J β) (accuracy (radius J β)) q u ε N) →
      ∃ G : Finset ℕ, G ⊆ A ∧ ((A \ G).card : ℝ) / (q : ℝ) ≤ δ ∧
        ∀ k ∈ G, (1 + 1 / (m k : ℝ) - δ) / (q : ℝ) ≤ u (k + 1) - u k := by
  let r := radius J β
  let l := accuracy r
  intro γ hγ δ hδ
  have hselect : ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 1 ≤ q →
      ∀ (A : Finset ℕ) (m z : ℕ → ℕ) (u : ℕ → ℝ),
      Admissible J β r l q A m z γ →
      (∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 2 ≤ R →
        ∃ N : ℝ, R ≤ N ∧ RecordData J d β r l q u ε N) →
      ∃ G : Finset ℕ, G ⊆ A ∧ ((A \ G).card : ℝ) / (q : ℝ) ≤ δ ∧
        ∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 2 ≤ R →
        ∃ N : ℝ, R ≤ N ∧ GoodRecordData J d β r l q u m z G
          (δ / (4 * ((J : ℝ) + 1) * (q : ℝ))) ε N :=
    Submission.k4_matching_cofinal_palette_selection hp D J hD hDJ d hd β hβ γ hγ δ hδ
  obtain ⟨Q, hQ⟩ := hselect
  obtain ⟨Qγ, hQγ⟩ := exists_nat_ge (4 / γ)
  refine ⟨max Q Qγ, ?_⟩
  intro q hqQ hq A m z u hAdm hRecords
  have hQq : Q ≤ q := (le_max_left Q Qγ).trans hqQ
  have hQγq : Qγ ≤ q := (le_max_right Q Qγ).trans hqQ
  have hmargin : 4 ≤ γ * (q : ℝ) := by
    have h4q := (div_le_iff₀ hγ).mp (hQγ.trans (Nat.cast_le.mpr hQγq))
    simpa only [mul_comm] using h4q
  obtain ⟨G, hGA, hcard, hGood⟩ := hQ q hQq hq A m z u hAdm hRecords
  refine ⟨G, hGA, hcard, ?_⟩
  intro k hk
  have hstep : StepAdmissible J β r l q k (m k) (z (m k)) γ :=
    hAdm.2 k (hGA hk)
  have hm : 1 ≤ m k := hstep.2.1
  have hmJ : m k ≤ J := hstep.2.2.1
  let θ := δ / (4 * ((J : ℝ) + 1) * (q : ℝ))
  have hqR : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  apply (targetExponent_sub_loss_le J (m k) q hm hmJ hq δ hδ).trans
  apply increment_of_cofinal_certificates hEnd (m k) q hm (u (k + 1) - u k) θ
  intro κ hκ R hR
  obtain ⟨ε₀, hε₀, R₀, hR₀, hconstruct⟩ :=
    Submission.k4_matching_switching_target_certificate D J hD hDJ d hd β hβ
      γ hγ q hq hmargin k (m k) (z (m k)) u hstep κ hκ θ hθ
  obtain ⟨N, hN, hData⟩ := hGood (ε₀ / 2) (by positivity)
    (max R R₀) (hR.trans (le_max_left R R₀))
  obtain ⟨n₁, n₂, f₁, f₂, π₁, π₂, μ, h, F, S, hRecord, hPalette⟩ := hData
  refine ⟨N, (le_max_left R R₀).trans hN, ?_⟩
  exact hconstruct (ε₀ / 2) (by positivity) (by linarith) N
    ((le_max_right R R₀).trans hN) n₁ n₂ f₁ f₂ π₁ π₂ μ h F S hRecord (hPalette k hk)

end Submission.Obl.k4_matching_good_step_increment
