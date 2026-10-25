/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/SaturationInterface.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/SaturationInterface.lean. Earlier provenance is retained below. -/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.SaturationTransfer
import Submission.Obl.k4_balanced_native_packet_transport.CPF.CoarsenedProblem

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open Filter

/-- Measurable own-depth lists remain measurable at the terminal observation
under the exact dyadic coarsening. -/
theorem Atlas.SaturatedAt.terminal_lists {p : Data} {k M D : ℕ} {r : ℝ}
    {a : Atlas p k} (ha : a.SaturatedAt M D r) (hN : 1 ≤ p.N k) (hrL : r ≤ p.L) :
    ∃ lst : Fin (p.W k) → Observation → Finset (Fin a.C),
      (∀ γ o, ((lst γ o).card : ℝ) ≤ a.κ) ∧
      (∀ b q, q ∈ a.F b →
        b ∈ lst (a.γ b) (obs (p.B k (a.γ b)) (δ (p.N k) p.L) q)) ∧
      ∀ γ b, MeasurableSet {o | b ∈ lst γ o} := by
  obtain ⟨_, _, lst, hcard, hlist, hmeas⟩ := ha
  let q : Observation → Observation :=
    Submission.Lib.K4Homogenization.coarsenObservation (p.N k) r p.L
  refine ⟨fun γ o => lst γ (q o), fun γ o => hcard γ _, ?_, ?_⟩
  · intro b z hz
    have hpoint := obs_coarsen hN hrL (B := p.B k (a.γ b)) (q := z)
    change b ∈ lst (a.γ b)
      (Submission.Lib.K4Homogenization.coarsenObservation (p.N k) r p.L
        (obs (p.B k (a.γ b)) (δ (p.N k) p.L) z))
    rw [← hpoint]
    exact hlist b z hz
  · intro γ b
    exact (hmeas γ b).preimage
      (Submission.Lib.K4Homogenization.measurable_coarsenObservation _ _ _)

/-- Own-depth knowledge also gives the terminal-observation knowledge used by
normalization, through the exact dyadic coarsening map. -/
theorem Atlas.SaturatedAt.knownAt {p : Data} {k M D : ℕ} {r h ε : ℝ}
    {a : Atlas p k} (ha : a.SaturatedAt M D r) (hN : 1 ≤ p.N k) (hrL : r ≤ p.L)
    (hκ : 1 ≤ a.κ) (hκN : a.κ ≤ p.N k ^ ε)
    (hT : (2 : ℝ) ^ a.T ≤ p.N k ^ (h + ε)) : KnownAt p M D r h ε k := by
  obtain ⟨htrue, _, lst, hcard, hlist, _⟩ := ha
  let lst' := fun γ o => lst γ
    (Submission.Lib.K4Homogenization.coarsenObservation (p.N k) r p.L o)
  refine ⟨a, lst', hκ, hκN, hT, htrue.1, htrue.2.1, fun γ o => hcard γ _,
    fun b => ?_, htrue.2.2.2⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, _⟩ := htrue.2.2.1 b
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_⟩
  intro q hq
  have hc := hlist b q hq
  change b ∈ lst (a.γ b) (Submission.Lib.K4Homogenization.coarsenObservation (p.N k) r p.L
    (obs (p.B k (a.γ b)) (δ (p.N k) p.L) q))
  rw [← obs_coarsen hN hrL]
  exact hc

/-- Coarsened true terminal systems can be prepared as saturated true systems
of the original problem, retaining the same time horizon. -/
theorem saturated_atlases_of_coarsened_terminal {p : Data} (hp : p.Valid) {r d h : ℝ}
    (hr : 0 ≤ r) (hrL : r ≤ p.L) (ht : Terminal (p.coarsen r d) h) :
    ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
      ∃ a : Atlas p k, 1 ≤ a.κ ∧ p.K k ≤ a.κ ∧ a.κ ≤ p.N k ^ ε ∧
        (2 : ℝ) ^ a.T ≤ p.N k ^ h ∧ a.SaturatedAt M D r := by
  obtain ⟨M, D, hs⟩ := true_systems_of_coarsened_terminal ht
  apply saturated_atlases_of_true_at_depth hp hr hrL
  refine ⟨M, D, fun σ hσ => (hs σ hσ).mono fun k hk => ?_⟩
  obtain ⟨a, hκ, _, hσ, hT, ha⟩ := hk
  exact ⟨a, hκ, hσ, hT, ha⟩

end Submission.Obl.k4_balanced_native_packet_transport.CPF
