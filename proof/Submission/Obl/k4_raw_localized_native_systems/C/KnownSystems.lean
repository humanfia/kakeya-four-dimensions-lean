import Submission.Obl.k4_raw_localized_native_systems.C.Problems

/-
Adapted from this LOT tree, o178, session x0596, `KnownSystems.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- A known atlas at depth `r`, with lists at the original terminal observation.
The format bounds are fixed before the exponent tolerance. -/
def KnownSystem (p : Data) (r h : ℝ) : Prop :=
  ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
    ∃ κ : ℝ, 1 ≤ κ ∧ p.K k ≤ κ ∧ κ ≤ p.N k ^ ε ∧
      ∃ a : Atlas p k, (2 : ℝ) ^ a.T ≤ p.N k ^ (h + ε) ∧ a.KnownAt M D κ r

/-- Failure of a known atlas provides a late-sample exclusion after any fixed
output format is specified.  This keeps the two quantifier orders separate. -/
theorem not_knownSystem_eventually {p : Data} {r h : ℝ}
    (hn : ¬ KnownSystem p r h) (M D : ℕ) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ k in atTop,
      ∀ κ : ℝ, 1 ≤ κ → p.K k ≤ κ → κ ≤ p.N k ^ τ →
        ∀ a : Atlas p k, (2 : ℝ) ^ a.T ≤ p.N k ^ (h + τ) →
          ¬ a.KnownAt M D κ r := by
  classical
  have hnot : ¬ (∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
      ∃ κ : ℝ, 1 ≤ κ ∧ p.K k ≤ κ ∧ κ ≤ p.N k ^ ε ∧
        ∃ a : Atlas p k, (2 : ℝ) ^ a.T ≤ p.N k ^ (h + ε) ∧ a.KnownAt M D κ r) :=
    fun hall => hn ⟨M, D, hall⟩
  push Not at hnot
  obtain ⟨τ, hτ, hlate⟩ := hnot
  refine ⟨τ, hτ, hlate.mono ?_⟩
  intro k hk κ hκ hKκ hκε a hT ha
  exact hk κ hκ hKκ hκε a hT ha

/-- Known atlases persist under increasing the allowed time horizon. -/
theorem KnownSystem.mono {p : Data} (hp : Valid p) {r h h' : ℝ}
    (hh : h ≤ h') (hk : KnownSystem p r h) : KnownSystem p r h' := by
  obtain ⟨M, D, hk⟩ := hk
  refine ⟨M, D, fun ε hε => (hk ε hε).mono ?_⟩
  rintro k ⟨κ, hκ, hKκ, hκε, a, hT, ha⟩
  refine ⟨κ, hκ, hKκ, hκε, a, hT.trans ?_, ha⟩
  exact Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one k) (by linarith)

end
end Submission.Obl.k4_raw_localized_native_systems.C
