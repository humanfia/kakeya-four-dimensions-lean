import Submission.Obl.k4_local_remainder_horizon_transfer.Expanded

/- The pure record below adapts this tree's o147/x0498 ca51f14,
RemainderData.lean, by separating its last angular-cap clause. -/

namespace Submission.Obl.k4_local_remainder_horizon_transfer

open MeasureTheory Filter

/-- Every complete-problem clause except the terminal angular upper tail. -/
noncomputable def Data.PureValid (p : Data) : Prop :=
  PureProblem p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G

/-- The one angular clause omitted from `PureValid`. -/
noncomputable def Data.Angular (p : Data) : Prop :=
  AngularProblem p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G

theorem valid_iff_pure_angular (p : Data) : p.Valid ↔ p.PureValid ∧ p.Angular := by
  simp only [Data.Valid, Problem, Data.PureValid, PureProblem, Data.Angular, AngularProblem]
  tauto

theorem splitProblem_of_valid {p : Data} (hp : p.Valid) :
    SplitProblem p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G :=
  (valid_iff_pure_angular p).mp hp

/-- The analytic output before angular transport; all priors and weights are computed. -/
structure PureRemainder {p : Data} {M D : ℕ} {r h : ℝ}
    (s : KnownSequence p M D r h) (cap : ℝ) where
  K : ℕ → ℝ
  E : (k : ℕ) → Fin (s.atlas k).C → Set Incidence
  f : ℝ → ℝ
  g : (k : ℕ) → Fin (s.atlas k).C → ℝ → Observation → ENNReal
  G : (k : ℕ) → Fin (s.atlas k).C → ℝ → JointObservation → ENNReal
  valid : (s.remainingData cap K E f g G).PureValid
  event_subset : ∀ k c, E k c ⊆ (s.atlas k).system.normEventOf c
  prior_positive : ∀ k c,
    0 < (p.ν (s.index k) ((s.atlas k).γ c) ((s.atlas k).A c)).toReal
  normalizer_subpower : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
    ((s.atlas k).system.normZ (p.ω (s.index k)) (p.ν (s.index k)))⁻¹ ≤
      p.N (s.index k) ^ ε
  terminal_comparison : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ c,
    p.N (s.index k) ^ (-p.f p.L) * |((s.atlas k).Q c).det| ≤
      p.N (s.index k) ^ ε *
        (p.ν (s.index k) ((s.atlas k).γ c) ((s.atlas k).A c)).toReal *
        p.N (s.index k) ^ (-f (p.L - r))

noncomputable def PureRemainder.data {p : Data} {M D : ℕ} {r h cap : ℝ}
    {s : KnownSequence p M D r h} (q : PureRemainder s cap) : Data :=
  s.remainingData cap q.K q.E q.f q.g q.G

/-- Once the angular clause is established, the existing terminal-lifting interface applies. -/
noncomputable def PureRemainder.complete {p : Data} {M D : ℕ} {r h cap : ℝ}
    {s : KnownSequence p M D r h} (q : PureRemainder s cap) (ha : q.data.Angular) :
    NormalizedRemainder s cap where
  K := q.K
  E := q.E
  f := q.f
  g := q.g
  G := q.G
  valid := (valid_iff_pure_angular q.data).mpr ⟨q.valid, ha⟩
  event_subset := q.event_subset
  prior_positive := q.prior_positive
  normalizer_subpower := q.normalizer_subpower
  terminal_comparison := q.terminal_comparison

/-- Unpacking the sequence record is exactly the closed frozen sequence predicate. -/
theorem sequenceExpanded_of_knownSequence {p : Data} {M D : ℕ} {r h : ℝ}
    (s : KnownSequence p M D r h) :
    SequenceExpanded p.N p.K p.L p.W p.ω p.ν p.E p.B p.f r h M D s.index
      (fun k => (s.atlas k).κ) (fun k => (s.atlas k).T) (fun k => (s.atlas k).C)
      (fun k => (s.atlas k).γ) (fun k => (s.atlas k).j)
      (fun k => (s.atlas k).c) (fun k => (s.atlas k).u) (fun k => (s.atlas k).Q)
      (fun k => (s.atlas k).R) (fun k => (s.atlas k).A) (fun k => (s.atlas k).F) :=
  ⟨s.strictMono, s.slack_one, s.slack_ambient, s.slack_subpower, s.time_upper, s.valid⟩

/-- All formulas in the frozen certificate are the actual affine normalization formulas. -/
theorem certificateExpanded_of_pureRemainder {p : Data} {M D : ℕ} {r h cap : ℝ}
    {s : KnownSequence p M D r h} (q : PureRemainder s cap) :
    PureCertificateExpanded p.N p.K p.L p.W p.ω p.ν p.E p.B p.f r h M D s.index
      (fun k => (s.atlas k).κ) (fun k => (s.atlas k).T) (fun k => (s.atlas k).C)
      (fun k => (s.atlas k).γ) (fun k => (s.atlas k).j)
      (fun k => (s.atlas k).c) (fun k => (s.atlas k).u) (fun k => (s.atlas k).Q)
      (fun k => (s.atlas k).R) (fun k => (s.atlas k).A) (fun k => (s.atlas k).F)
      p.S p.η cap q.K q.E q.f q.g q.G :=
  ⟨q.valid, q.event_subset, q.prior_positive, q.normalizer_subpower, q.terminal_comparison⟩

end Submission.Obl.k4_local_remainder_horizon_transfer
