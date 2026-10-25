import Submission.Obl.k4_local_remainder_horizon_transfer.PureRemainder

/-!
The terminal/initial-horizon bridges are adapted from this LOT tree,
o118, x0439 split s051, k4_extremal_profile_setup/Bridges.lean,
itself adapted from o105/x0351,x0367 split s042. The known-atlas and
pure-remainder bridges unpack the concrete data of this split.
-/

namespace Submission.Obl.k4_local_remainder_horizon_transfer

open MeasureTheory Filter

theorem terminalAt_iff_expanded (p : Data) (M D : ℕ) (h ε : ℝ) (k : ℕ) :
    TerminalAt p M D h ε k ↔
      ∃ κ : ℝ, 1 ≤ κ ∧ p.K k ≤ κ ∧ κ ≤ p.N k ^ ε ∧
      ∃ T C : ℕ, ∃ (γ : Fin C → Fin (p.W k)) (j : Fin C → Fin (2 ^ T))
      (c u : Fin C → Spatial) (Q : Fin C → Frame) (R : Fin C → Test)
      (A : Fin C → Set Trajectory) (F : Fin C → Set Incidence),
      (2 : ℝ) ^ T ≤ p.N k ^ h ∧ (C : ℝ) ≤ p.N k ^ M ∧
      (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧
      (∀ b, Chart (p.N k) M D κ T (j b : ℝ) p.L (p.B k (γ b)) (p.E k (γ b))
        (c b) (u b) (Q b) (R b) (A b) (F b)
        (ENNReal.ofReal (p.N k ^ (-p.f p.L) * |Matrix.det (Q b)| /
          ((2 : ℝ) ^ T * κ)) ≤ ((p.ν k (γ b)).prod volume) (F b))) ∧
      ENNReal.ofReal κ⁻¹ ≤ ∑ b, ENNReal.ofReal (p.ω k (γ b)) *
        ((p.ν k (γ b)).prod volume) (F b) := by
  constructor
  · rintro ⟨a, hκ, hK, hε, hT, hC, hdis, hcharts, hmass⟩
    exact ⟨a.κ, hκ, hK, hε, a.T, a.C, a.γ, a.j, a.c, a.u, a.Q, a.R,
      a.A, a.F, hT, hC, hdis, hcharts, hmass⟩
  · rintro ⟨κ, hκ, hK, hε, T, C, γ, j, c, u, Q, R, A, F,
      hT, hC, hdis, hcharts, hmass⟩
    exact ⟨⟨κ, T, C, γ, j, c, u, Q, R, A, F⟩,
      hκ, hK, hε, hT, hC, hdis, hcharts, hmass⟩

theorem terminalExpanded_iff (p : Data) (h : ℝ) :
    TerminalExpanded p.N p.K p.L p.W p.ω p.ν p.E p.B p.f h ↔ Terminal p h := by
  constructor
  · rintro ⟨M, D, hs⟩
    exact ⟨M, D, fun ε hε => (hs ε hε).mono fun k hk =>
      (terminalAt_iff_expanded p M D h ε k).mpr hk⟩
  · rintro ⟨M, D, hs⟩
    exact ⟨M, D, fun ε hε => (hs ε hε).mono fun k hk =>
      (terminalAt_iff_expanded p M D h ε k).mp hk⟩

theorem horizonExpanded_eq (p : Data) :
    HorizonExpanded p.N p.K p.L p.W p.ω p.ν p.E p.B p.f = horizon p := by
  unfold HorizonExpanded horizon
  congr 1
  ext h
  exact terminalExpanded_iff p h

theorem initialHorizon_iff : InitialHorizonExpanded ↔ InitialHorizon := by
  constructor
  · intro hi p hp h hh
    exact (terminalExpanded_iff p h).mp
      (hi p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G hp h hh)
  · intro hi N K L d S η W ω ν E P B f g G hp h hh
    let p : Data := ⟨N, K, L, d, S, η, W, ω, ν, E, P, B, f, g, G⟩
    exact (terminalExpanded_iff p h).mpr (hi p hp h hh)

theorem knownExpanded_iff (p : Data) (r h : ℝ) :
    KnownExpanded p.N p.K p.L p.W p.ω p.ν p.E p.B p.f r h ↔ Known p r h := by
  constructor
  · rintro ⟨M, D, hs⟩
    refine ⟨M, D, fun ε hε => (hs ε hε).mono ?_⟩
    rintro k ⟨κ, hκ, hε, T, C, γ, j, c, u, Q, R, A, F, lst,
      hT, hC, hsep, hlist, hchart, hmass⟩
    exact ⟨⟨κ, T, C, γ, j, c, u, Q, R, A, F⟩,
      hκ, hε, hT, lst, hC, hsep, hlist, hchart, hmass⟩
  · rintro ⟨M, D, hs⟩
    refine ⟨M, D, fun ε hε => (hs ε hε).mono ?_⟩
    rintro k ⟨a, hκ, hε, hT, lst, hC, hsep, hlist, hchart, hmass⟩
    exact ⟨a.κ, hκ, hε, a.T, a.C, a.γ, a.j, a.c, a.u, a.Q, a.R, a.A, a.F,
      lst, hT, hC, hsep, hlist, hchart, hmass⟩

/-- The first frozen child constructs exactly the computed pure-remainder interface. -/
theorem pure_remainder_of_expanded (hh : PureNormalizationExpanded)
    {p : Data} (hp : p.Valid) {r h cap : ℝ} (hr : 0 ≤ r) (hrL : r < p.L)
    (hcap : 0 < cap) (hcap1 : cap < 1)
    (hc : ∀ s : ℝ, r ≤ s → s ≤ p.L → p.f p.L - p.f s ≤ cap * (p.L - s))
    (hk : Known p r h) :
    ∃ M D : ℕ, ∃ s : KnownSequence p M D r h, Nonempty (PureRemainder s cap) := by
  obtain ⟨M, D, ψ, κ, T, C, γ, j, c, u, Q, R, A, F, K₂, E₂, f₂, g₂, G₂,
    hseq, hrem⟩ := hh p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G
      (splitProblem_of_valid hp) r h cap hr hrL hcap hcap1 hc
      ((knownExpanded_iff p r h).mpr hk)
  rcases hseq with ⟨hψ, hκ, hK, hsub, htime, hvalid⟩
  let s : KnownSequence p M D r h := {
    index := ψ
    strictMono := hψ
    atlas := fun k => ⟨κ k, T k, C k, γ k, j k, c k, u k, Q k, R k, A k, F k⟩
    slack_one := hκ
    slack_ambient := hK
    slack_subpower := hsub
    time_upper := htime
    valid := hvalid }
  rcases hrem with ⟨hcore, hE, hν, hZ, hcompare⟩
  exact ⟨M, D, s, ⟨{
    K := K₂
    E := E₂
    f := f₂
    g := g₂
    G := G₂
    valid := hcore
    event_subset := hE
    prior_positive := hν
    normalizer_subpower := hZ
    terminal_comparison := hcompare }⟩⟩

/-- The second child supplies precisely the missing final problem clause. -/
theorem angular_of_expanded (hh : AngularTransportExpanded)
    {p : Data} (hp : p.Valid) {M D : ℕ} {r h cap : ℝ}
    {s : KnownSequence p M D r h} (q : PureRemainder s cap)
    (hr : 0 ≤ r) (hrL : r < p.L) : q.data.Angular := by
  exact hh p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G
    (splitProblem_of_valid hp) r h cap hr hrL M D s.index
    (fun k => (s.atlas k).κ) (fun k => (s.atlas k).T) (fun k => (s.atlas k).C)
    (fun k => (s.atlas k).γ) (fun k => (s.atlas k).j)
    (fun k => (s.atlas k).c) (fun k => (s.atlas k).u) (fun k => (s.atlas k).Q)
    (fun k => (s.atlas k).R) (fun k => (s.atlas k).A) (fun k => (s.atlas k).F)
    q.K q.E q.f q.g q.G (sequenceExpanded_of_knownSequence s)
    (certificateExpanded_of_pureRemainder q)

end Submission.Obl.k4_local_remainder_horizon_transfer
