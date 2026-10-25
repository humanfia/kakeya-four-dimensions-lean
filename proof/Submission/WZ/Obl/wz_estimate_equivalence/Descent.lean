-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_estimate_equivalence.Descent.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_estimate_equivalence.Estimates

namespace WangZahlLot.Obl.wz_estimate_equivalence

/-- Increasing the scale exponent weakens `E`. -/
theorem e_mono_omega {σ ω ω' : ℝ} (hω : ω ≤ ω') (hE : E σ ω) : E σ ω' := by
  intro ε hε
  obtain ⟨a, ha, η, hη, h⟩ := hE ε hε
  refine ⟨a, ha, η, hη, ?_⟩
  intro δ hδ hδmax m l hm hl n x v Y hn hv hT hsep hY hYT hdens hK hF
  have hbound := h δ hδ hδmax m l hm hl n x v Y hn hv hT hsep hY hYT hdens hK hF
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hbound
  have hδ1 : δ ≤ 1 := le_trans hδmax (by norm_num)
  have hpow : δ ^ (ω' + ε) ≤ δ ^ (ω + ε) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hl0 : 0 < l := lt_of_lt_of_le zero_lt_one hl
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  gcongr

/-- No uniformity of the constants in the approximating estimates is needed at a limit. -/
theorem e_of_forall_pos_add {σ ω : ℝ} (h : ∀ t : ℝ, 0 < t → E σ (ω + t)) :
    E σ ω := by
  intro ε hε
  obtain ⟨a, ha, η, hη, hbound⟩ := h (ε / 2) (by positivity) (ε / 2) (by positivity)
  refine ⟨a, ha, η, hη, ?_⟩
  intro δ hδ hδmax m l hm hl n x v Y hn hv hT hsep hY hYT hdens hK hF
  have heq : (ω + ε / 2) + ε / 2 = ω + ε := by ring
  simpa only [heq] using
    hbound δ hδ hδmax m l hm hl n x v Y hn hv hT hsep hY hYT hdens hK hF

/-- Abstract form of the finite descent followed by the limiting argument in Proposition 1.6.

The geometric work supplies a starting estimate and the uniform improvement in `hstep`.
The decrement can depend on the positive gap `t`, but not on the current exponent `ω'`.
-/
theorem e_of_uniform_descent {σ ω : ℝ}
    (hbase : ∃ ω₀ : ℝ, E σ ω₀)
    (hstep : ∀ t : ℝ, 0 < t → ∃ α : ℝ, 0 < α ∧
      ∀ ω' : ℝ, ω + t ≤ ω' → E σ ω' → E σ (ω' - α)) : E σ ω := by
  apply e_of_forall_pos_add
  intro t ht
  obtain ⟨ω₀, hbase⟩ := hbase
  obtain ⟨α, hα, hstep⟩ := hstep t ht
  obtain ⟨k, hk⟩ := exists_nat_gt ((ω₀ - (ω + t)) / α)
  have hk' : ω₀ - (k : ℝ) * α < ω + t := by
    have hmul := (div_lt_iff₀ hα).mp hk
    linarith
  have hind : ∀ j : ℕ, E σ (ω + t) ∨ E σ (ω₀ - (j : ℝ) * α) := by
    intro j
    induction j with
    | zero => exact Or.inr (by simpa using hbase)
    | succ j ih =>
      rcases ih with hdone | hcurrent
      · exact Or.inl hdone
      · by_cases hle : ω + t ≤ ω₀ - (j : ℝ) * α
        · right
          have himproved := hstep _ hle hcurrent
          convert himproved using 1
          push_cast
          ring
        · exact Or.inl (e_mono_omega (le_of_not_ge hle) hcurrent)
  rcases hind k with hdone | hlast
  · exact hdone
  · exact e_mono_omega hk'.le hlast

end WangZahlLot.Obl.wz_estimate_equivalence
