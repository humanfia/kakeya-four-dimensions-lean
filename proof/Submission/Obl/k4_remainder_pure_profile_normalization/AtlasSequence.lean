/-
Adapted from this LOT tree, o147, session x0498, commit 5dd59d875729,
Submission/Obl/k4_local_remainder_horizon_transfer/AtlasSequence.lean.
Earlier provenance is preserved below.
-/
import Submission.Obl.k4_remainder_pure_profile_normalization.Definitions
import Submission.Obl.k4_quadratic_atlas_normalization.ChartMonotonicity

/-!
The fixed-format, frequently available known atlas is extracted once. Its
slack dominates the ambient slack, and both its slack and its time error
are subpower along the resulting exact subsequence.
-/

namespace Submission.Obl.k4_remainder_pure_profile_normalization

open Filter MeasureTheory

/-- The list and geometric conditions of a terminal-known atlas. -/
def Atlas.KnownAt {p : Data} {k : ℕ} (a : Atlas p k) (M D : ℕ) (r : ℝ) : Prop :=
  ∃ lst : Fin (p.W k) → Observation → Finset (Fin a.C),
    (a.C : ℝ) ≤ p.N k ^ M ∧ a.Separated ∧
    (∀ γ o, ((lst γ o).card : ℝ) ≤ a.κ) ∧
    (∀ b, Chart (p.N k) M D a.κ a.T (a.j b : ℝ) r
      (p.B k (a.γ b)) (p.E k (a.γ b)) (a.c b) (a.u b) (a.Q b) (a.R b) (a.A b) (a.F b)
      (∀ q ∈ a.F b, b ∈ lst (a.γ b) (obs (p.B k (a.γ b)) (δ (p.N k) p.L) q))) ∧
    ENNReal.ofReal a.κ⁻¹ ≤ a.mass

/-- The exact quantifier order of the frozen known-atlas hypothesis. -/
def Known (p : Data) (r h : ℝ) : Prop :=
  ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
    ∃ a : Atlas p k, 1 ≤ a.κ ∧ a.κ ≤ p.N k ^ ε ∧
      (2 : ℝ) ^ a.T ≤ p.N k ^ (h + ε) ∧ a.KnownAt M D r

/-- Increasing only the geometric slack preserves a chart and its extra test. -/
theorem Chart.mono_slack {N κ κ' r B j : ℝ} {M D T : ℕ}
    {E F : Set Incidence} {A : Set Trajectory} {c u : Spatial} {Q : Frame} {R : Test}
    {ex : Prop} (hc : Chart N M D κ T j r B E c u Q R A F ex)
    (hN : 1 ≤ N) (hκ : 0 < κ) (hκ' : κ ≤ κ') (hB : 0 ≤ B) :
    Chart N M D κ' T j r B E c u Q R A F ex :=
  Submission.Obl.k4_quadratic_atlas_normalization.chart_mono
    hN le_rfl le_rfl hκ hκ' hB hc id

/-- Replace the slack, retaining every geometric and assignment datum. -/
def Atlas.withSlack {p : Data} {k : ℕ} (a : Atlas p k) (κ : ℝ) : Atlas p k :=
  { a with κ := κ }

theorem Atlas.KnownAt.mono_slack {p : Data} {k M D : ℕ} {a : Atlas p k}
    {r κ : ℝ} (ha : a.KnownAt M D r) (hN : 1 ≤ p.N k) (hκ : 0 < a.κ) (hκ' : a.κ ≤ κ)
    (hB : ∀ γ, 0 ≤ p.B k γ) : (a.withSlack κ).KnownAt M D r := by
  rcases ha with ⟨lst, hC, hsep, hlist, hchart, hmass⟩
  refine ⟨lst, hC, hsep, fun γ o => (hlist γ o).trans hκ', ?_, ?_⟩
  · intro b
    exact (hchart b).mono_slack hN hκ hκ' (hB _)
  · exact (ENNReal.ofReal_le_ofReal (inv_anti₀ hκ hκ')).trans hmass

/-- A single cofinal sequence of full known atlases, with one pair of format bounds. -/
structure KnownSequence (p : Data) (M D : ℕ) (r h : ℝ) where
  index : ℕ → ℕ
  strictMono : StrictMono index
  atlas : (k : ℕ) → Atlas p (index k)
  slack_one : ∀ k, 1 ≤ (atlas k).κ
  slack_ambient : ∀ k, p.K (index k) ≤ (atlas k).κ
  slack_subpower : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, (atlas k).κ ≤ p.N (index k) ^ ε
  time_upper : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
    (2 : ℝ) ^ (atlas k).T ≤ p.N (index k) ^ (h + ε)
  valid : ∀ k, (atlas k).KnownAt M D r

/-- Extract a diagonal, enlarging slack by `max κ K` before the extraction. -/
theorem Known.exists_sequence {p : Data} (hp : p.Valid) {r h : ℝ} (ha : Known p r h) :
    ∃ M D : ℕ, Nonempty (KnownSequence p M D r h) := by
  classical
  rcases ha with ⟨M, D, ha⟩
  have hB : ∀ k γ, 0 ≤ p.B k γ := by
    obtain ⟨_, _, hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
    intro k γ
    exact (hfmt k).2.2.2.1 γ |>.2.1.le
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun _ => by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hf : ∀ n : ℕ, ∃ᶠ k in atTop,
      ∃ a : Atlas p k, 1 ≤ a.κ ∧ p.K k ≤ a.κ ∧ a.κ ≤ p.N k ^ ε n ∧
        (2 : ℝ) ^ a.T ≤ p.N k ^ (h + ε n) ∧ a.KnownAt M D r := by
    intro n
    have hK := hp.2.2.1.2 (ε n) (hε n)
    apply (ha (ε n) (hε n)).and_eventually hK |>.mono
    rintro k ⟨⟨a, h1, hκ, ht, hv⟩, hK⟩
    refine ⟨a.withSlack (max a.κ (p.K k)), h1.trans (le_max_left _ _),
      le_max_right _ _, max_le hκ hK, ht, ?_⟩
    exact hv.mono_slack (by linarith [hp.1 k]) (by linarith) (le_max_left _ _) (hB k)
  obtain ⟨ψ, hψ, hψgood⟩ := extraction_forall_of_frequently hf
  choose a h1 hK hκ ht hv using hψgood
  refine ⟨M, D, ⟨⟨ψ, hψ, a, h1, hK, ?_, ?_, hv⟩⟩⟩
  · intro e he
    filter_upwards [hεlim.eventually (gt_mem_nhds he)] with k hk
    exact (hκ k).trans (Real.rpow_le_rpow_of_exponent_le
      (by linarith [hp.1 (ψ k)]) hk.le)
  · intro e he
    filter_upwards [hεlim.eventually (gt_mem_nhds he)] with k hk
    exact (ht k).trans (Real.rpow_le_rpow_of_exponent_le
      (by linarith [hp.1 (ψ k)]) (by linarith))

end Submission.Obl.k4_remainder_pure_profile_normalization
