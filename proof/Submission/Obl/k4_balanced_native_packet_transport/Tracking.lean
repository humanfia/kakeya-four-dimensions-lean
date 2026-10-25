import Submission.Obl.k4_balanced_native_packet_transport.CPF.ExtremalPacketProfiles

/-!
# Tracked normalization

The accepted o184 normalization pipeline (`Known.exists_prepared_sequence`,
`Known.exists_ratio_samples`) and the calibrated remainder of o105/x0351
(`CPF.BalancedNormalization`) only delete whole charts, enlarge slacks and pass
to subsequences.  The copies below start from a GIVEN known sequence instead of
the existential `Known` hypothesis and record that every chart of the final
sequence is, unchanged, a chart of the given sequence at the same original
sample index.  The proofs follow the cited sources line by line:
`Submission/Obl/k4_remainder_pure_profile_normalization/{SequenceBounds,
Preparation,RatioCharts}.lean` (accepted o184) and
`CPF/BalancedNormalization.lean` (o105, x0351, commit 2ab1efa2).
-/

namespace Submission.Obl.k4_balanced_native_packet_transport.Tracking

open MeasureTheory Filter Set
open Submission.Obl.k4_remainder_pure_profile_normalization

/-- `a` consists of charts of `b`, unchanged, at the same original sample index
and with the same dyadic partition. The slacks may differ. -/
def SubOf {p : Data} {k k' : ℕ} (a : Atlas p k) (b : Atlas p k') : Prop :=
  k = k' ∧ a.T = b.T ∧ ∃ ι : Fin a.C → Fin b.C, ∀ c,
    (a.γ c : ℕ) = (b.γ (ι c) : ℕ) ∧ (a.j c : ℕ) = (b.j (ι c) : ℕ) ∧
    a.c c = b.c (ι c) ∧ a.u c = b.u (ι c) ∧ a.Q c = b.Q (ι c) ∧ a.R c = b.R (ι c) ∧
    a.A c = b.A (ι c) ∧ a.F c = b.F (ι c)

theorem SubOf.refl {p : Data} {k : ℕ} (a : Atlas p k) : SubOf a a :=
  ⟨rfl, rfl, id, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem SubOf.trans {p : Data} {k k' k'' : ℕ} {a : Atlas p k} {b : Atlas p k'}
    {c : Atlas p k''} (hab : SubOf a b) (hbc : SubOf b c) : SubOf a c := by
  obtain ⟨hk, hT, ι, hι⟩ := hab
  obtain ⟨hk', hT', ι', hι'⟩ := hbc
  refine ⟨hk.trans hk', hT.trans hT', ι' ∘ ι, fun x => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hι x
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := hι' (ι x)
  exact ⟨h1.trans g1, h2.trans g2, h3.trans g3, h4.trans g4, h5.trans g5, h6.trans g6,
    h7.trans g7, h8.trans g8⟩

theorem select_subOf {p : Data} {k : ℕ} (a : Atlas p k) (S : Finset (Fin a.C)) :
    SubOf (a.select S) a :=
  ⟨rfl, rfl, a.selectIndex S, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem withSlack_subOf {p : Data} {k : ℕ} (a : Atlas p k) (κ : ℝ) :
    SubOf (a.withSlack κ) a :=
  ⟨rfl, rfl, id, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- A known sequence obtained from `s₀` by deleting charts and passing to a
subsequence. -/
def SeqSubOf {p : Data} {M D M₀ D₀ : ℕ} {r h r₀ h₀ : ℝ}
    (s : KnownSequence p M D r h) (s₀ : KnownSequence p M₀ D₀ r₀ h₀) : Prop :=
  ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ n, s.index n = s₀.index (σ n) ∧
    SubOf (s.atlas n) (s₀.atlas (σ n))

theorem SeqSubOf.trans {p : Data} {M D M₁ D₁ M₀ D₀ : ℕ} {r h r₁ h₁ r₀ h₀ : ℝ}
    {s : KnownSequence p M D r h} {s₁ : KnownSequence p M₁ D₁ r₁ h₁}
    {s₀ : KnownSequence p M₀ D₀ r₀ h₀}
    (h01 : SeqSubOf s s₁) (h12 : SeqSubOf s₁ s₀) : SeqSubOf s s₀ := by
  obtain ⟨σ, hσ, hs⟩ := h01
  obtain ⟨σ', hσ', hs'⟩ := h12
  exact ⟨σ' ∘ σ, hσ'.comp hσ, fun n => ⟨(hs n).1.trans (hs' (σ n)).1,
    (hs n).2.trans (hs' (σ n)).2⟩⟩

/-- Tracked copy of o184 `Known.exists_prepared_sequence` (with the inlined
`KnownSequence.exists_bounded`), started from a given sequence. -/
theorem prepared_sequence_of {p : Data} (hp : p.Valid) {M D : ℕ} {r h : ℝ}
    (s₀ : KnownSequence p M D r h) :
    ∃ s : KnownSequence p M D r h,
      (∀ k, (2 : ℝ) ^ (s.atlas k).T ≤ p.N (s.index k) ^ (h + 1)) ∧
      (∀ k c, (p.N (s.index k) ^ (M + 2))⁻¹ ≤
        (p.ν (s.index k) ((s.atlas k).γ c) ((s.atlas k).A c)).toReal) ∧
      SeqSubOf s s₀ := by
  classical
  have he := (s₀.slack_subpower 1 (by norm_num)).and (s₀.time_upper 1 (by norm_num))
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp he
  let ψ : ℕ → ℕ := fun k => k + k₀
  have hψ : StrictMono ψ := by intro i j hij; dsimp [ψ]; omega
  let s := s₀.reindex ψ hψ
  have hsκ : ∀ k, (s.atlas k).κ ≤ p.N (s.index k) := by
    intro k
    have h1 := (hk₀ (ψ k) (by dsimp [ψ]; omega)).1
    rw [Real.rpow_one] at h1
    exact h1
  have hstime : ∀ k, (2 : ℝ) ^ (s.atlas k).T ≤ p.N (s.index k) ^ (h + 1) := by
    intro k
    exact (hk₀ (ψ k) (by dsimp [ψ]; omega)).2
  obtain ⟨Mₚ, Dₚ, hsample⟩ := hp.sampleProblem
  have hkeep := fun k => (s.valid k).discard_light (hsample (s.index k))
    (hp.1 (s.index k)) (s.slack_one k) (hsκ k)
  choose S hS hν using hkeep
  let atlas : (k : ℕ) → Atlas p (s.index k) :=
    fun k => (((s.atlas k).select (S k)).withSlack (2 * (s.atlas k).κ))
  have hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, (atlas k).κ ≤ p.N (s.index k) ^ ε := by
    intro ε hε
    have hNt := hp.2.1.comp s.strictMono.tendsto_atTop
    have htwo : ∀ᶠ k in atTop, 2 ≤ p.N (s.index k) ^ (ε / 2) :=
      ((tendsto_rpow_atTop (half_pos hε)).comp hNt).eventually_ge_atTop 2
    filter_upwards [s.slack_subpower (ε / 2) (half_pos hε), htwo] with k hk htwo
    change 2 * (s.atlas k).κ ≤ p.N (s.index k) ^ ε
    calc 2 * (s.atlas k).κ ≤ p.N (s.index k) ^ (ε / 2) * p.N (s.index k) ^ (ε / 2) :=
          mul_le_mul htwo hk (by linarith [s.slack_one k]) (by positivity)
      _ = p.N (s.index k) ^ ε := by
        rw [← Real.rpow_add (by linarith [hp.1 (s.index k)])]
        congr 1
        ring
  let s' : KnownSequence p M D r h := {
    index := s.index
    strictMono := s.strictMono
    atlas := atlas
    slack_one := fun k => by change 1 ≤ 2 * (s.atlas k).κ; linarith [s.slack_one k]
    slack_ambient := fun k => by
      change p.K (s.index k) ≤ 2 * (s.atlas k).κ
      linarith [s.slack_ambient k, s.slack_one k]
    slack_subpower := hsub
    time_upper := fun ε hε => s.time_upper ε hε
    valid := hS }
  refine ⟨s', hstime, hν, ψ, hψ, fun n => ⟨rfl, ?_⟩⟩
  exact (withSlack_subOf _ _).trans (select_subOf _ _)

/-- Tracked copy of o184 `Known.exists_ratio_samples`, started from a given
sequence. -/
theorem ratio_samples_of {p : Data} (hp : p.Valid) {M D : ℕ} {r h : ℝ}
    (s₀ : KnownSequence p M D r h) (hr : 0 ≤ r) :
    ∃ t : RatioSamples p r h, SeqSubOf t.samples.sequence s₀ := by
  classical
  obtain ⟨s, htime, hprior, hss₀⟩ := prepared_sequence_of hp s₀
  obtain ⟨Mₚ, Dₚ, hsample⟩ := hp.sampleProblem
  let M₀ := M + Nat.ceil (h + 1)
  let A₀ := M + 2
  let s₂ : KnownSequence p M₀ D r h := {
    index := s.index
    strictMono := s.strictMono
    atlas := s.atlas
    slack_one := s.slack_one
    slack_ambient := s.slack_ambient
    slack_subpower := s.slack_subpower
    time_upper := s.time_upper
    valid := fun k => (s.valid k).mono_format
      (by linarith [hp.1 (s.index k)]) (by linarith [s.slack_one k])
      (fun γ => ((hsample (s.index k)).scale_pos γ).le) (by dsimp [M₀]; omega) le_rfl }
  let ratio (k : ℕ) (b : Fin (s.atlas k).C) : ℝ :=
    |((s.atlas k).Q b).det| /
      (p.ν (s.index k) ((s.atlas k).γ b) ((s.atlas k).A b)).toReal
  let weight (k : ℕ) (b : Fin (s.atlas k).C) : ENNReal :=
    ENNReal.ofReal (p.ω (s.index k) ((s.atlas k).γ b)) *
      ((p.ν (s.index k) ((s.atlas k).γ b)).prod volume) ((s.atlas k).F b)
  let bound : ℕ := 2 * M₀ + 1 + A₀
  have hrat : ∀ k b, p.N (s.index k) ^ (-(bound : ℝ)) ≤ ratio k b ∧
      ratio k b ≤ p.N (s.index k) ^ (bound : ℝ) := by
    intro k b
    have hN : 2 ≤ p.N (s.index k) := hp.1 _
    have hN0 : 0 < p.N (s.index k) := by linarith
    have : IsProbabilityMeasure (p.ν (s.index k) ((s.atlas k).γ b)) :=
      (hsample (s.index k)).prob _
    have hlo : (p.N (s.index k) ^ A₀)⁻¹ ≤
        (p.ν (s.index k) ((s.atlas k).γ b) ((s.atlas k).A b)).toReal := hprior k b
    have hpos : 0 < (p.ν (s.index k) ((s.atlas k).γ b) ((s.atlas k).A b)).toReal :=
      (inv_pos.mpr (pow_pos hN0 _)).trans_le hlo
    have hle1 : (p.ν (s.index k) ((s.atlas k).γ b) ((s.atlas k).A b)).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal (by norm_num) (by
        simpa using (measure_mono (μ := p.ν (s.index k) ((s.atlas k).γ b))
          (Set.subset_univ ((s.atlas k).A b))))
    obtain ⟨_, _, _, _, hchart, _⟩ := s₂.valid k
    have hframe := hchart b
    have hb := jacobian_prior_ratio_bounds ((s.atlas k).Q b) hN hframe.1
      hframe.2.2.1 hpos hle1 hlo
    refine ⟨?_, ?_⟩
    · refine (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ p.N (s.index k)) ?_).trans hb.1
      have hh : ((2 * M₀ + 1 : ℕ) : ℝ) ≤ (bound : ℝ) := by
        exact_mod_cast (show 2 * M₀ + 1 ≤ bound by dsimp [bound]; omega)
      linarith
    · simpa only [Real.rpow_natCast] using hb.2
  obtain ⟨ψ, S, loss, α, hψ, hloss, hretain, hfit⟩ :=
    select_finite_ratios (fun k => p.N (s.index k)) (fun k => hp.1 _)
      (hp.2.1.comp s.strictMono.tendsto_atTop) (fun k => (s.atlas k).C)
      weight ratio bound (Nat.cast_nonneg _) hrat
  let κ (k : ℕ) := (s.atlas (ψ k)).κ * loss k
  let a (k : ℕ) := ((s.atlas (ψ k)).select (S k)).withSlack (κ k)
  have hslack : Submission.Obl.k4_tempered_grid_selection.Subpower
      (fun k => p.N (s.index (ψ k))) κ :=
    Submission.Obl.k4_tempered_grid_selection.subpower_mul
      (fun k => by linarith [hp.1 (s.index (ψ k))])
      ⟨fun k => s.slack_one (ψ k), fun ε hε =>
        hψ.tendsto_atTop.eventually (s.slack_subpower ε hε)⟩ hloss
  have hmass (k : ℕ) : ENNReal.ofReal (κ k)⁻¹ ≤ ((s.atlas (ψ k)).select (S k)).mass := by
    have hκ : 0 < (s.atlas (ψ k)).κ := by linarith [s.slack_one (ψ k)]
    have hl : 0 < loss k := by linarith [hloss.1 k]
    have hret : (s.atlas (ψ k)).mass ≤ ENNReal.ofReal (loss k) *
        ((s.atlas (ψ k)).select (S k)).mass := by
      rw [Atlas.select_mass]
      exact hretain k
    have hlow : ENNReal.ofReal ((s.atlas (ψ k)).κ)⁻¹ ≤ (s.atlas (ψ k)).mass := by
      obtain ⟨_, _, _, _, _, hm⟩ := s.valid (ψ k)
      exact hm
    calc
      ENNReal.ofReal (κ k)⁻¹ = (ENNReal.ofReal (loss k))⁻¹ *
          ENNReal.ofReal ((s.atlas (ψ k)).κ)⁻¹ := by
        dsimp only [κ]
        rw [mul_inv_rev, ENNReal.ofReal_mul (inv_nonneg.mpr hl.le),
          ENNReal.ofReal_inv_of_pos hl]
      _ ≤ (ENNReal.ofReal (loss k))⁻¹ * (ENNReal.ofReal (loss k) *
          ((s.atlas (ψ k)).select (S k)).mass) := mul_le_mul' le_rfl (hlow.trans hret)
      _ = _ := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hl))
          ENNReal.ofReal_ne_top, one_mul]
  let s₁ : KnownSequence p M₀ D r h := {
    index := s.index ∘ ψ
    strictMono := s.strictMono.comp hψ
    atlas := a
    slack_one := hslack.1
    slack_ambient := fun k => by
      change p.K (s.index (ψ k)) ≤ (s.atlas (ψ k)).κ * loss k
      exact (s.slack_ambient _).trans (le_mul_of_one_le_right
        (by linarith [s.slack_one (ψ k)]) (hloss.1 k))
    slack_subpower := hslack.2
    time_upper := fun ε hε => hψ.tendsto_atTop.eventually (s.time_upper ε hε)
    valid := fun k => (s₂.valid (ψ k)).select (S k)
      (by linarith [hp.1 (s.index (ψ k))]) (by linarith [s.slack_one (ψ k)])
      (le_mul_of_one_le_right (by linarith [s.slack_one (ψ k)]) (hloss.1 k))
      (fun γ => ((hsample (s.index (ψ k))).scale_pos γ).le) (hmass k) }
  have hprior₁ (k : ℕ) (b : Fin (s₁.atlas k).C) :
      (p.N (s₁.index k) ^ A₀)⁻¹ ≤
        (p.ν (s₁.index k) ((s₁.atlas k).γ b) ((s₁.atlas k).A b)).toReal :=
    hprior (ψ k) ((s.atlas (ψ k)).selectIndex (S k) b)
  have htime₁ (k : ℕ) : (2 : ℝ) ^ (s₁.atlas k).T ≤ p.N (s₁.index k) ^ M₀ := by
    refine (htime (ψ k)).trans ?_
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [hp.1 (s.index (ψ k))])
    have hc : h + 1 ≤ (Nat.ceil (h + 1) : ℝ) := Nat.le_ceil _
    have hm : (Nat.ceil (h + 1) : ℝ) ≤ M₀ := by exact_mod_cast
      (show Nat.ceil (h + 1) ≤ M₀ by dsimp [M₀]; omega)
    linarith
  let t : NormalizedSamples p r h := {
    atlasM := M₀
    atlasD := D
    sequence := s₁
    priorPower := A₀
    prior_lower := hprior₁
    formatM := Mₚ + 7 * M₀ + A₀ + Nat.ceil r + 20
    formatD := max (max Dₚ D) 1
    sample := fun k => (s₁.valid k).normalize_sample (hsample (s₁.index k)) (hp.1 _)
      hr (s₁.slack_one k) (htime₁ k) (fun b => by
        have hpow : 0 < p.N (s₁.index k) ^ A₀ := by
          exact pow_pos (by linarith [hp.1 (s₁.index k)]) _
        simpa only [mul_comm] using (inv_le_iff_one_le_mul₀ hpow).mp (hprior₁ k b)) }
  refine ⟨⟨t, α, fun ε hε => ?_⟩, ?_⟩
  · filter_upwards [hfit ε hε] with k hk b
    exact hk ((s.atlas (ψ k)).selectIndex (S k) b) (((S k).equivFin.symm b).property)
  · refine SeqSubOf.trans ⟨ψ, hψ, fun n => ⟨rfl, ?_⟩⟩ hss₀
    exact (withSlack_subOf _ _).trans (select_subOf _ _)

open Submission.Obl.k4_balanced_native_packet_transport.CPF.BalancedNormalization in
/-- Tracked copy of x0351's `exists_calibrated_normalization`, given ratio
samples. -/
theorem calibrated_normalization_of_samples {p : Data} (hp : p.Valid) {r h cap : ℝ}
    (t : RatioSamples p r h) (hr : 0 ≤ r) (hrL : r < p.L)
    (hc : 0 < cap) (hc₁ : cap < 1)
    (hcap : ∀ s, r ≤ s → s ≤ p.L → p.f p.L - p.f s ≤ cap * (p.L - s)) :
    ∃ u : HomogeneousSelection (t.samples.rawData hp cap),
      u.selection.data.PureValid ∧
      u.selection.f (p.L - r) = p.f p.L - t.exponent ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ b,
        p.N (t.samples.sequence.index (u.selection.index k)) ^ (t.exponent - ε) ≤
          |((t.samples.sequence.atlas (u.selection.index k)).Q b).det| /
            (p.ν (t.samples.sequence.index (u.selection.index k))
              ((t.samples.sequence.atlas (u.selection.index k)).γ b)
              ((t.samples.sequence.atlas (u.selection.index k)).A b)).toReal ∧
        |((t.samples.sequence.atlas (u.selection.index k)).Q b).det| /
            (p.ν (t.samples.sequence.index (u.selection.index k))
              ((t.samples.sequence.atlas (u.selection.index k)).γ b)
              ((t.samples.sequence.atlas (u.selection.index k)).A b)).toReal ≤
          p.N (t.samples.sequence.index (u.selection.index k)) ^ (t.exponent + ε) := by
  obtain ⟨u⟩ := MultiHomog.pureHomogenization (t.samples.rawData hp cap)
    (fun k => hp.1 _)
    (hp.2.1.comp t.samples.sequence.strictMono.tendsto_atTop)
    (t.samples.rawData_subpower hp cap) (sub_pos.mpr hrL)
    ⟨t.samples.formatM, t.samples.formatD, t.samples.rawData_samples hp cap⟩
  exact ⟨u, pure_valid hp t hr hrL hc hc₁ hcap u, terminal_exponent hp t hr hrL u,
    fun ε hε => u.selection.strictMono.tendsto_atTop.eventually (t.ratios ε hε)⟩

open Submission.Obl.k4_balanced_native_packet_transport.CPF.BalancedNormalization in
/-- Tracked copy of x0351's `exists_calibrated_remainder`: the calibrated
remainder is built on a subsequence of the given ratio samples. -/
theorem calibrated_remainder_of_samples {p : Data} (hp : p.Valid) {r h cap : ℝ}
    (t : RatioSamples p r h) (hr : 0 ≤ r) (hrL : r < p.L)
    (hc : 0 < cap) (hc₁ : cap < 1)
    (hcap : ∀ s, r ≤ s → s ≤ p.L → p.f p.L - p.f s ≤ cap * (p.L - s)) :
    ∃ q : CalibratedRemainder p r h cap, SeqSubOf q.sequence t.samples.sequence := by
  obtain ⟨u, hvalid, hterminal, hratio⟩ :=
    calibrated_normalization_of_samples hp t hr hrL hc hc₁ hcap
  let s := t.samples.sequence.reindex u.selection.index u.selection.strictMono
  have hprior (k : ℕ) (b : Fin (s.atlas k).C) :
      0 < (p.ν (s.index k) ((s.atlas k).γ b) ((s.atlas k).A b)).toReal :=
    t.samples.prior_pos hp (u.selection.index k) b
  have hZ := s.normalizer_subpower hp
  have hcompare : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ b,
      p.N (s.index k) ^ (-p.f p.L) * |((s.atlas k).Q b).det| ≤
        p.N (s.index k) ^ ε *
          (p.ν (s.index k) ((s.atlas k).γ b) ((s.atlas k).A b)).toReal *
            p.N (s.index k) ^ (-u.selection.f (p.L - r)) := by
    intro ε hε
    filter_upwards [hratio ε hε] with k hk b
    exact terminal_floor_of_ratio (by linarith [hp.1 (s.index k)])
      (hprior k b) hterminal (hk b).2
  have hang : (s.remainingData cap u.selection.K u.selection.E u.selection.f
      u.selection.g u.selection.G).AngularValid := by
    exact Submission.Obl.k4_remainder_angular_cap_transport.transport
      p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G
      ((p.valid_iff_pure_angular).mp hp) r h cap hr hrL
      t.samples.atlasM t.samples.atlasD s.index
      (fun k => (s.atlas k).κ) (fun k => (s.atlas k).T) (fun k => (s.atlas k).C)
      (fun k => (s.atlas k).γ) (fun k => (s.atlas k).j)
      (fun k => (s.atlas k).c) (fun k => (s.atlas k).u) (fun k => (s.atlas k).Q)
      (fun k => (s.atlas k).R) (fun k => (s.atlas k).A) (fun k => (s.atlas k).F)
      u.selection.K u.selection.E u.selection.f u.selection.g u.selection.G
      ⟨s.strictMono, s.slack_one, s.slack_ambient, s.slack_subpower, s.time_upper, s.valid⟩
      ⟨hvalid, u.event_subset, hprior, hZ, hcompare⟩
  refine ⟨⟨t.samples.atlasM, t.samples.atlasD, s, {
    K := u.selection.K
    E := u.selection.E
    f := u.selection.f
    g := u.selection.g
    G := u.selection.G
    valid := ?_
    event_subset := u.event_subset
    prior_positive := hprior
    normalizer_subpower := hZ
    terminal_comparison := hcompare }, t.exponent, hterminal, hratio⟩,
    u.selection.index, u.selection.strictMono, fun n => ⟨rfl, SubOf.refl _⟩⟩
  exact (Data.valid_iff_pure_angular _).mpr ⟨hvalid, hang⟩

open Submission.Obl.k4_balanced_native_packet_transport.CPF.BalancedNormalization in
/-- Tracked copy of x0351's `exists_depth_zero_calibrated_remainder`: a GIVEN
depth-zero known sequence yields a calibrated remainder whose parent charts are
unchanged charts of that sequence. -/
theorem calibrated_remainder_of_sequence {p : Data} (hp : p.Valid) {M D : ℕ} {h : ℝ}
    (s₀ : KnownSequence p M D 0 h) :
    ∃ q : CalibratedRemainder p 0 h p.d, SeqSubOf q.sequence s₀ := by
  have hp₀ := hp
  rcases hp with ⟨_, _, _, hL, hd, hd₁, _, _, _, _, _, _, _, hcap, _⟩
  obtain ⟨t, ht⟩ := ratio_samples_of hp₀ s₀ le_rfl
  obtain ⟨q, hq⟩ := calibrated_remainder_of_samples hp₀ t le_rfl hL hd hd₁ hcap
  exact ⟨q, hq.trans ht⟩

end Submission.Obl.k4_balanced_native_packet_transport.Tracking

namespace Submission.Obl.k4_balanced_native_packet_transport.Tracking

open MeasureTheory Filter Set
open Submission.Obl.k4_remainder_pure_profile_normalization
open Submission.Obl.k4_balanced_native_packet_transport.CPF.BalancedPacketSystems

/-- Tracked version of x0351's `ExtremalPacketProfiles.exists_packets_from_known_zero`
(o105, commit 2ab1efa2): the depth-zero known atlas is replaced by a GIVEN known
sequence `s₀`, and the parent charts of the calibrated remainder are unchanged
charts of `s₀` at the same original indices. The relative profile of the
original problem is also returned. -/
theorem tracked_packets (hi : CPF.InitialHorizonExpanded)
    {ds kr S η b D err : ℝ} (es : CPF.ExtremalSetup ds kr S η)
    (hb : 0 < b) (hb₁ : 2 * b ≤ 1) (herr : 0 < err)
    (hD : 0 < D) (hD₁ : D < 1) (hdD : ds < D)
    (hsmall : 2 * err ≤ (D - ds) * b) :
    ∃ tolerance : ℝ, 0 < tolerance ∧ ∀ p : SourceData, p.Valid → p.L = 1 →
      p.S = S → p.η = η → p.d < ds + tolerance →
      kr - tolerance < CPF.CalibratedHorizon.horizon p →
      ∀ {M₀ D₀ : ℕ} (s₀ : KnownSequence p M₀ D₀ 0 0),
      (∀ r ∈ Icc (0 : ℝ) 1, |p.f r - p.f 0 - ds * r| ≤ err) ∧
      ∃ q : Certificate p, SeqSubOf q.sequence s₀ ∧
      ∃ r ∈ Icc b (2 * b), ∀ h : ℝ, 2 * b < h →
        ∃ M₁ D₁ : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
          ∃ a : CPF.Atlas (normalizedData q) k,
            1 ≤ a.κ ∧ (normalizedData q).K k ≤ a.κ ∧
            a.κ ≤ (normalizedData q).N k ^ ε ∧
            (2 : ℝ) ^ a.T ≤ (normalizedData q).N k ^ h ∧ a.SaturatedAt M₁ D₁ r ∧
            ENNReal.ofReal (p.N (q.sequence.index k) ^ (-ε)) ≤
              CPF.OriginalPacketCoverage.originalCoveredMass q k a ∧
            ∀ c, MeasurableSet (originalAssignment q k a c) ∧
              MeasurableSet (CPF.OriginalPacketCoverage.originalEvent q k a c) ∧
              CPF.OriginalPacketCoverage.originalEvent q k a c ⊆
                p.E (q.sequence.index k) ((q.sequence.atlas k).γ (a.γ c)) ∧
              CPF.OriginalPacketCoverage.originalEvent q k a c ⊆
                originalAssignment q k a c ×ˢ (univ : Set ℝ) ∧
              p.N (q.sequence.index k) ^ (-ds * r - (3 * err + ε)) ≤
                originalMass q k a c /
                  (p.N (q.sequence.index k) ^ (-p.f 0) * |(composedFrame q k a c).det|) ∧
              originalMass q k a c /
                  (p.N (q.sequence.index k) ^ (-p.f 0) * |(composedFrame q k a c).det|) ≤
                p.N (q.sequence.index k) ^ (-ds * r + (3 * err + ε)) := by
  obtain ⟨tolerance, htol, hprofiles⟩ :=
    CPF.ExtremalPacketProfiles.relative_profiles hi es herr
  refine ⟨tolerance, htol, fun p hp hL hS hη hd hnear M₀ D₀ s₀ => ?_⟩
  obtain ⟨q, hq⟩ := calibrated_remainder_of_sequence hp s₀
  obtain ⟨hold, hnew⟩ := hprofiles p hp hL hS hη hd hnear
  refine ⟨hold, q, hq, ?_⟩
  exact CPF.RelativePacketBalance.exists_balanced_covered_systems
    (CPF.initialHorizon_iff.mp hi) hp hL q hb hb₁ hD hD₁ hdD
    (by simpa only [mul_one] using hold 1 (by norm_num)) (hnew q) hsmall

end Submission.Obl.k4_balanced_native_packet_transport.Tracking
