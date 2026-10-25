import Submission.Obl.k4_extremal_profile_setup.Horizon

namespace Submission.Obl.k4_extremal_profile_setup

open Filter

/-- Restrict an exact problem to a new resolution sequence. -/
def Data.reindex (p : Data) (φ : ℕ → ℕ) : Data where
  N k := p.N (φ k)
  K k := p.K (φ k)
  L := p.L
  d := p.d
  S := p.S
  η := p.η
  W k := p.W (φ k)
  ω k := p.ω (φ k)
  ν k := p.ν (φ k)
  E k := p.E (φ k)
  P k := p.P (φ k)
  B k := p.B (φ k)
  f := p.f
  g k := p.g (φ k)
  G k := p.G (φ k)

theorem Data.Valid.reindex {p : Data} (hp : p.Valid) {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) : (p.reindex φ).Valid := by
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, htemp, hg, hG, hinc,
    htyp, hcap, hang⟩
  refine ⟨fun k => hN (φ k), hNt.comp hφ,
    ⟨fun k => hK.1 (φ k), fun ε hε => hφ.eventually (hK.2 ε hε)⟩,
    hL, hd, hd1, hS, hη, ?_, ?_, ?_, hinc, ?_, hcap, ?_⟩
  · obtain ⟨M, D, htemp⟩ := htemp
    exact ⟨M, D, fun k => htemp (φ k)⟩
  · exact fun k γ r hr hrL => hg (φ k) γ r hr hrL
  · exact fun k γ u hu huL => hG (φ k) γ u hu huL
  · intro r τ hr hrL hτ
    obtain ⟨c, hc, ht⟩ := htyp r τ hr hrL hτ
    exact ⟨c, hc, hφ.eventually ht⟩
  · intro u τ hu huL hτ
    obtain ⟨c, hc, ht⟩ := hang u τ hu huL hτ
    exact ⟨c, hc, hφ.eventually ht⟩

/-- A terminal witness at a selected resolution is already an original witness. -/
theorem TerminalAt.of_reindex {p : Data} {φ : ℕ → ℕ} {M D k : ℕ} {h ε : ℝ}
    (ht : TerminalAt (p.reindex φ) M D h ε k) : TerminalAt p M D h ε (φ k) := by
  rcases ht with ⟨⟨κ, T, C, γ, j, c, u, Q, R, A, F⟩, hκ, hK, hε, hT, htrue⟩
  exact ⟨⟨κ, T, C, γ, j, c, u, Q, R, A, F⟩, hκ, hK, hε, hT, htrue⟩

theorem Terminal.of_reindex {p : Data} {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) {h : ℝ} (ht : Terminal (p.reindex φ) h) :
    Terminal p h := by
  obtain ⟨M, D, ht⟩ := ht
  refine ⟨M, D, fun ε hε => ?_⟩
  have hf : ∃ᶠ k in atTop, TerminalAt p M D h ε (φ k) :=
    (ht ε hε).mono fun _ hk => hk.of_reindex
  by_contra hn
  exact hf (hφ.eventually (not_frequently.mp hn))

/-- Passing to a subsequence may increase the infimal horizon. -/
theorem horizon_le_reindex (hi : InitialHorizon) {p : Data} (hp : p.Valid)
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) : horizon p ≤ horizon (p.reindex φ) := by
  apply le_csInf (terminal_nonempty hi (hp.reindex hφ))
  intro h hh
  exact horizon_le hp (hh.of_reindex hφ)

end Submission.Obl.k4_extremal_profile_setup
