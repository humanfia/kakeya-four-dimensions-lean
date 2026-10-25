import Submission.Obl.k4_raw_critical_segment_forests.NestedInterface
import Submission.Obl.k4_coarsened_outer_horizon_composition.Observations

/-!
# Nested normalization through prepared parents

The forest layers handed to the normalization are prepared by o191's interface: true
floors at their own depth `r`, the upper prior bound, and labels known by the
observation at depth `r` (paper, Lemma 2.10 `a01:saturation`).  `PreparedParent`
records exactly this, with the lists stored in the o153 atlas.

`NestedNormalizationPrepared` asks for nested normalization through such parents.  It
follows from `NestedNormalization` by refining the own-depth lists to the terminal
observation of `G` (the observation at depth `G.L` determines the one at `r`).
-/

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

/-- A prepared parent at depth `r`: slack `κ`, time partition bounded by the format,
true floors at depth `r`, the upper prior bound, and labels known by the observation
at the own depth `r` through `a.lst`. -/
def PreparedParent (G : Data) (M D : ℕ) (r ε κ : ℝ) {k : ℕ} (a : Atlas G k) : Prop :=
  1 ≤ κ ∧ G.K k ≤ κ ∧ κ ≤ G.N k ^ ε ∧ (2 : ℝ) ^ a.T ≤ G.N k ^ M ∧
    a.Regular M D κ r (fun b =>
      ENNReal.ofReal (G.N k ^ (-G.f r) * |Matrix.det (a.Q b)| / ((2 : ℝ) ^ a.T * κ)) ≤
          priorMass G k (a.γ b) (a.F b) ∧
        G.ν k (a.γ b) (a.A b) ≤ ENNReal.ofReal (κ * G.N k ^ (-G.f r) * |Matrix.det (a.Q b)|) ∧
        ∀ z ∈ a.F b, b ∈ a.lst (a.γ b) (obs (G.B k (a.γ b)) (δ (G.N k) r) z)) ∧
    ∀ γ o, ((a.lst γ o).card : ℝ) ≤ κ

/-- **Nested normalization through prepared parents.** -/
def NestedNormalizationPrepared : Prop :=
  ∀ (G : Data), Valid G → ∀ r : ℝ, 0 ≤ r → r < G.L →
  ∀ (M D : ℕ) (φ : ℕ → ℕ) (ε κ : ℕ → ℝ) (par : (n : ℕ) → Atlas G (φ n)),
    StrictMono φ → (∀ n, 0 < ε n) → Tendsto ε atTop (nhds 0) →
    (∀ n, PreparedParent G M D r (ε n) (κ n) (par n)) →
    ∃ (q : Data) (ψ : ℕ → ℕ), Valid q ∧ q.L = G.L - r ∧ q.d = G.d ∧ q.S = G.S ∧
      q.η = G.η ∧ StrictMono ψ ∧ (∀ n, q.N n = G.N (φ (ψ n))) ∧
      ∀ M' D' : ℕ, ∃ M'' D'' : ℕ, ∀ e : ℝ, 0 < e → ∃ e' : ℝ, 0 < e' ∧
        ∀ᶠ n in atTop, ∀ (κ' : ℝ) (a : Atlas q n), 1 ≤ κ' → q.K n ≤ κ' →
          κ' ≤ q.N n ^ e' → a.TrueAt M' D' κ' →
          ∃ (κ'' : ℝ) (c : Atlas G (φ (ψ n))) (pmap : Fin c.C → Fin (par (ψ n)).C)
            (cmap : Fin c.C → Fin a.C),
            1 ≤ κ'' ∧ G.K (φ (ψ n)) ≤ κ'' ∧ κ'' ≤ G.N (φ (ψ n)) ^ e ∧
            c.T = (par (ψ n)).T + a.T ∧ c.TrueAt M'' D'' κ'' ∧
            NestedIn c (par (ψ n)) pmap ∧
            ∀ b, |Matrix.det (c.Q b)| * (4 : ℝ) ^ c.T =
              (|Matrix.det ((par (ψ n)).Q (pmap b))| * (4 : ℝ) ^ (par (ψ n)).T) *
                (|Matrix.det (a.Q (cmap b))| * (4 : ℝ) ^ a.T)

/-- The same atlas with its own-depth lists refined to the terminal observation of `G`. -/
noncomputable def refineLists {G : Data} {k : ℕ} (r : ℝ) (a : Atlas G k) : Atlas G k :=
  { a with lst := fun γ o =>
      a.lst γ (Submission.Lib.K4Homogenization.coarsenObservation (G.N k) r G.L o) }

/-- The own-depth observation is a function of the terminal one. -/
theorem obs_own_depth {G : Data} (hG : Valid G) {k : ℕ} {r : ℝ} (hr : r ≤ G.L) (B : ℝ)
    (z : Point) :
    obs B (δ (G.N k) r) z = Submission.Lib.K4Homogenization.coarsenObservation (G.N k) r G.L
      (obs B (δ (G.N k) G.L) z) :=
  congrFun (Submission.Obl.k4_coarsened_outer_horizon_composition.obs_factorization
    (hG.scale_ge_one k) hr B) z

/-- A prepared parent is a known parent once its lists are refined. -/
theorem knownParent_of_preparedParent {G : Data} (hG : Valid G) {M D : ℕ} {r ε κ : ℝ}
    (hr : r ≤ G.L) {k : ℕ} {a : Atlas G k} (ha : PreparedParent G M D r ε κ a) :
    KnownParent G M D r ε κ (refineLists r a) := by
  obtain ⟨hκ1, hK, hκε, hT, ⟨hC, hsep, hcharts, hmass⟩, hlst⟩ := ha
  refine ⟨hκ1, hK, hκε, hT, ⟨hC, hsep, fun b => ?_, hmass⟩, fun γ o => hlst γ _⟩
  have hc := hcharts b
  apply chart_enlarge (lt_of_lt_of_le zero_lt_one hκ1) le_rfl (hG.B_pos k (a.γ b)).le _ hc
  rintro ⟨-, -, hmem⟩ z hz
  change b ∈ a.lst (a.γ b) (Submission.Lib.K4Homogenization.coarsenObservation (G.N k) r G.L
    (obs (G.B k (a.γ b)) (δ (G.N k) G.L) z))
  rw [← obs_own_depth hG hr]
  exact hmem z hz

/-- Nested normalization through prepared parents follows from nested normalization
through known parents. -/
theorem nestedNormalizationPrepared_of_nestedNormalization
    (hNN : NestedNormalization) : NestedNormalizationPrepared := by
  intro G hG r hr hrL M D φ ε κ par hφ hε hεlim hpar
  exact hNN G hG r hr hrL M D φ ε κ (fun n => refineLists r (par n)) hφ hε hεlim
    (fun n => knownParent_of_preparedParent hG hrL.le (hpar n))

end Submission.Obl.k4_raw_critical_segment_forests
