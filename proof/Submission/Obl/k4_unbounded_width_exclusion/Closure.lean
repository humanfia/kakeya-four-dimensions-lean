import Submission.Obl.k4_unbounded_width_exclusion.ReductionInterfaces

noncomputable section

namespace Submission.Obl.k4_unbounded_width_exclusion

/-- Forgetting a restored slack lower bound changes no chart or list. -/
theorem known_to_weakKnown
    {N K L W ω ν E B r h} (hk : known N K L W ω ν E B r h) (f : ℝ → ℝ) :
    weakKnown N K L W ω ν E B f r h := by
  obtain ⟨M, D, hMD⟩ := hk
  refine ⟨M, D, fun ε hε => (hMD ε hε).mono fun k hk => ?_⟩
  obtain ⟨κ, hκ, hKκ, hκN, rest⟩ := hk
  exact ⟨κ, hκ, hκN, rest⟩

/-- o147 with the original cap d is the composition principle needed here. -/
theorem composition_of_localRemainderTransfer
    (ht : LocalRemainderTransfer) : KnownAtlasComposition := by
  intro N K L d S η W ω ν E P B f g G hp r h hr hrL hk e he
  have hcopy := hp
  obtain ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hrest⟩ := hcopy
  dsimp only at hrest
  obtain ⟨hdata, hg, hG, hLip, htyp, hcap, hang⟩ := hrest
  obtain ⟨N₂, K₂, W₂, ω₂, ν₂, E₂, P₂, B₂, f₂, g₂, G₂, hp₂, hH⟩ :=
    ht N K L d S η W ω ν E P B f g G hp r h d hr hrL hd hd1
      (fun s hrs hsL => hcap s (hr.trans hrs) hsL) (known_to_weakKnown hk f)
  exact ⟨N₂, K₂, L - r, d, W₂, ω₂, ν₂, E₂, P₂, B₂, f₂, g₂, G₂,
    hp₂, rfl, rfl, hH.trans (by linarith)⟩

/-- This numerical corollary does not hide the normalization step: its only
extra hypothesis is the explicit residual-problem composition principle. -/
theorem knownAtlasExclusion_of_composition
    (hcomp : KnownAtlasComposition) : KnownAtlasExclusion := by
  intro ds kr S η hS hη hes c hc hc1
  let m : ℝ := kr * c / 16
  have hkr : 0 < kr := hes.2.2.1
  have hm : 0 < m := by dsimp [m]; positivity
  obtain ⟨a₀, ha₀, hrate⟩ := hes.2.2.2.2.2.1 m hm
  refine ⟨min a₀ m, lt_min ha₀ hm, ?_⟩
  intro N K d W ω ν E P B f g G hp hd hh hknown
  obtain ⟨N', K', L', d', W', ω', ν', E', P', B', f', g', G',
      hp', hL', hd', hH⟩ :=
    hcomp N K 1 d S η W ω ν E P B f g G hp
      c (kr * c / 2) hc.le hc1 hknown m hm
  have hdcap : d' < ds + a₀ := by
    rw [hd']
    exact hd.trans_le (by linarith [min_le_left a₀ m])
  have hupper := hrate N' K' L' d' W' ω' ν' E' P' B' f' g' G' hp' hdcap
  rw [hL'] at hupper hH
  have hmc : m * (1 - c) ≤ m := by nlinarith
  have hn : kr * c / 2 + (kr + m) * (1 - c) + m ≤ kr - 2 * m := by
    dsimp [m] at *
    nlinarith [mul_pos hkr hc]
  have hHbound : H N K 1 W ω ν E B f ≤ kr - 2 * m :=
    (hH.trans (by linarith [hupper])).trans hn
  have ha : min a₀ m ≤ m := min_le_right _ _
  linarith

end Submission.Obl.k4_unbounded_width_exclusion
