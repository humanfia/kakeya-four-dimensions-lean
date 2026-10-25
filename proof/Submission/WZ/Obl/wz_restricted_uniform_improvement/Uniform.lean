-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_restricted_uniform_improvement.Uniform.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_restricted_uniform_improvement.Estimates

namespace WangZahlLot.Obl.wz_restricted_uniform_improvement

/-- A pointwise improvement of a closed, upward monotone family of estimates
has a uniform decrement above any strictly larger threshold. No uniformity
of the pointwise decrement or of the constants in the estimates is required. -/
theorem uniform_decrement_of_pointwise
    (E R : ℝ → Prop) (ω t : ℝ) (ht : 0 < t)
    (hEmono : ∀ u v, u ≤ v → E u → E v)
    (hRmono : ∀ u v, u ≤ v → R u → R v)
    (hEclosed : ∀ u, (∀ ε > 0, E (u + ε)) → E u)
    (hpoint : ∀ u, ω < u → E u → ∃ α > 0, R (u - α)) :
    ∃ α : ℝ, 0 < α ∧ α ≤ t / 2 ∧
      ∀ u : ℝ, ω + t ≤ u → E u → R (u - α) := by
  classical
  let S : Set ℝ := {u | ω + t / 2 ≤ u ∧ E u}
  by_cases hne : S.Nonempty
  · have hbounded : BddBelow S := ⟨ω + t / 2, fun _ hu => hu.1⟩
    let c : ℝ := sInf S
    have hc : ω + t / 2 ≤ c := le_csInf hne (fun _ hu => hu.1)
    have hEc : E c := by
      apply hEclosed
      intro ε hε
      obtain ⟨u, hu, hue⟩ := exists_lt_of_csInf_lt hne
        (show sInf S < c + ε by dsimp [c]; linarith)
      exact hEmono u (c + ε) hue.le hu.2
    obtain ⟨g, hg, hRg⟩ := hpoint c (by linarith) hEc
    refine ⟨min g (t / 2), lt_min hg (by positivity), min_le_right _ _, ?_⟩
    intro u hu hEu
    have hcu : c ≤ u := csInf_le hbounded (show u ∈ S from ⟨by linarith, hEu⟩)
    apply hRmono (c - g) (u - min g (t / 2)) _ hRg
    linarith [min_le_left g (t / 2)]
  · refine ⟨t / 2, by positivity, le_rfl, ?_⟩
    intro u hu hEu
    exact (hne ⟨u, by dsimp [S]; exact ⟨by linarith, hEu⟩⟩).elim

/-- For the frozen estimates, the only geometric result needed for a uniform
improvement is a positive, possibly nonuniform, pointwise improvement. -/
theorem uniform_improvement_of_pointwise {σ ω : ℝ}
    (hpoint : ∀ u : ℝ, ω < u → Full σ u → ∃ α > 0, Restricted σ (u - α))
    (t : ℝ) (ht : 0 < t) :
    ∃ α : ℝ, 0 < α ∧ α ≤ t / 2 ∧
      ∀ u : ℝ, ω + t ≤ u → Full σ u → Restricted σ (u - α) := by
  exact uniform_decrement_of_pointwise (Full σ) (Restricted σ) ω t ht
    (fun _ _ huv h => h.mono_omega huv) (fun _ _ huv h => h.mono_omega huv)
    (fun _ h => Full.closed_omega h) hpoint

end WangZahlLot.Obl.wz_restricted_uniform_improvement
