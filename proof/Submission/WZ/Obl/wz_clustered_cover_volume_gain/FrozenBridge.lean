-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.FrozenBridge.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Definitions
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainTransfer

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

/-- The frozen estimate is definitionally the accepted body's tube-estimate input. -/
theorem tubeEstimate_of_E {σ ω : ℝ} (hE : E σ ω) :
    WangZahlLot.Obl.wz_flat_factored_improvement.TubeEstimate σ ω := hE

theorem assignedFiber_eq_supported {n N : ℕ} {S : Finset (Fin n)}
    {Z : Fin n → Set V} (f : Fin n → Fin N)
    (hsupport : ∀ i, i ∉ S → Z i = ∅) (k : Fin N) :
    assignedFiber f Z k = {p | ∃ i ∈ S, f i = k ∧ p ∈ Z i} := by
  ext p
  constructor
  · rintro ⟨i, hik, hi⟩
    have hiS : i ∈ S := by
      by_contra hnot
      simpa only [hsupport i hnot, Set.mem_empty_iff_false] using hi
    exact ⟨i, hiS, hik, hi⟩
  · rintro ⟨i, _, hik, hi⟩
    exact ⟨i, hik, hi⟩

/-- Remove the inert indices outside `S` from the frozen uniform fine level.
The level can always be chosen nonnegative, including for the empty shading. -/
theorem fine_level_of_UF {n N : ℕ} {S : Finset (Fin n)}
    {Z : Fin n → Set V} {f : Fin n → Fin N}
    (hsupport : ∀ i, i ∉ S → Z i = ∅) (hUF : UF n S Z N f) :
    ∃ m : ℝ, 0 ≤ m ∧ ∀ k p, p ∈ assignedFiber f Z k →
      m ≤ fiberBodyCount f Z k p ∧ fiberBodyCount f Z k p ≤ 2 * m := by
  obtain ⟨m, hm⟩ := hUF
  refine ⟨max m 0, le_max_right _ _, ?_⟩
  intro k p hp
  have hpS := (assignedFiber_eq_supported f hsupport k).subset hp
  have hh := hm k p hpS
  have hm0 : 0 ≤ m := by linarith [hh.1, hh.2]
  have he : {i : Fin n | f i = k ∧ p ∈ Z i} =
      {i : Fin n | i ∈ S ∧ f i = k ∧ p ∈ Z i} := by
    ext i
    constructor
    · intro hi
      have hiS : i ∈ S := by
        by_contra hnot
        have hip := hi.2
        simpa only [hsupport i hnot, Set.mem_empty_iff_false] using hip
      exact ⟨hiS, hi⟩
    · exact fun hi => hi.2
  rw [max_eq_left hm0, fiberBodyCount_eq_ncard, he]
  exact hh

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
