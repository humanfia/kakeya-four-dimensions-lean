/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/Kappa.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/Kappa.lean. Earlier provenance is retained below. -/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.Horizon
import Submission.Obl.k4_balanced_native_packet_transport.CPF.Monotonicity

/-! Monotonicity of the chart conditions in the slack `κ`.

Every conjunct of `Chart` that mentions `κ` weakens as `κ` grows (the derivative scale
`Bv` being nonnegative), and so do the true floor and the mass bound of a terminal
system.  Hence the lower bound `K k ≤ κ` of the frozen conclusion can always be restored
by enlarging the slack to `max κ (K k)`, as `K` is subpower. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open MeasureTheory Filter

theorem δ_pos (Nk r : ℝ) : 0 < δ Nk r := by
  unfold δ
  positivity

theorem Chart.mono_kappa {Nk : ℝ} {M D : ℕ} {κ κ' : ℝ} {T : ℕ} {j r Bv : ℝ}
    {Ev : Set Incidence} {c u : Spatial} {Q : Frame} {R : Test}
    {A : Set Trajectory} {F : Set Incidence} {ex ex' : Prop}
    (hκ : 0 < κ) (hκκ' : κ ≤ κ') (hB : 0 ≤ Bv) (hex : ex → ex')
    (h : Chart Nk M D κ T j r Bv Ev c u Q R A F ex) :
    Chart Nk M D κ' T j r Bv Ev c u Q R A F ex' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  refine ⟨h1, h2, h3, ?_, h5, h6, h7, h8, h9, ?_, ?_, hex h12⟩
  · exact h4.trans (div_le_div_of_nonneg_right hκκ' (by positivity))
  · intro l hl
    obtain ⟨a1, a2, a3⟩ := h10 l hl
    refine ⟨a1, a2, fun t ht => ?_⟩
    obtain ⟨b1, b2, b3, b4⟩ := a3 t ht
    have hδ := δ_pos Nk r
    refine ⟨b1.trans hκκ', b2.trans (mul_le_mul_of_nonneg_right hκκ' hδ.le),
      b3.trans (mul_le_mul_of_nonneg_right hκκ' hB), b4.trans ?_⟩
    gcongr
  · intro p hp
    obtain ⟨c1, c2, c3, c4⟩ := h11 p hp
    exact ⟨c1, c2, c3, le_trans (div_le_div_of_nonneg_left hB hκ hκκ') c4⟩

theorem Data.Valid.K_one {p : Data} (hp : p.Valid) (k : ℕ) : 1 ≤ p.K k := hp.2.2.1.1 k

theorem Data.Valid.K_subpower {p : Data} (hp : p.Valid) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, p.K k ≤ p.N k ^ ε := hp.2.2.1.2 ε hε

theorem Data.Valid.N_tendsto {p : Data} (hp : p.Valid) : Tendsto p.N atTop atTop := hp.2.1

/-- The same atlas with a larger slack. -/
def Atlas.withKappa {p : Data} {k : ℕ} (a : Atlas p k) (κ' : ℝ) : Atlas p k :=
  { a with κ := κ' }

theorem Atlas.TrueAt.mono_kappa {p : Data} (hp : p.Valid) {k : ℕ} {a : Atlas p k}
    {M D : ℕ} {r : ℝ} {κ' : ℝ} (hκ : 0 < a.κ) (hκκ' : a.κ ≤ κ')
    (ha : a.TrueAt M D r) : (a.withKappa κ').TrueAt M D r := by
  obtain ⟨hC, hsep, hcharts, hmass⟩ := ha
  refine ⟨hC, hsep, fun b => ?_, ?_⟩
  · refine Chart.mono_kappa hκ hκκ' (hp.B_pos k _).le (fun hfl => le_trans ?_ hfl) (hcharts b)
    apply ENNReal.ofReal_le_ofReal
    have h2 : (0 : ℝ) < 2 ^ a.T := by positivity
    have hN : 0 ≤ p.N k ^ (-p.f r) * |Matrix.det (a.Q b)| := by
      have : 0 < p.N k := lt_of_lt_of_le (by norm_num) (hp.N_ge k)
      positivity
    exact div_le_div_of_nonneg_left hN (by positivity)
      (mul_le_mul_of_nonneg_left hκκ' h2.le)
  · refine le_trans ?_ hmass
    exact ENNReal.ofReal_le_ofReal (inv_anti₀ hκ hκκ')

/-- A true terminal system with slack at most `N^ε` gives a sample of the frozen
conclusion once `K k ≤ N^ε`: the slack is enlarged to `max κ (K k)`. -/
theorem TerminalAt.of_trueAt {p : Data} (hp : p.Valid) {M D : ℕ} {h ε : ℝ} {k : ℕ}
    (a : Atlas p k) (h1 : 1 ≤ a.κ) (hε : a.κ ≤ p.N k ^ ε) (hK : p.K k ≤ p.N k ^ ε)
    (hT : (2 : ℝ) ^ a.T ≤ p.N k ^ h) (ha : a.TrueAt M D p.L) :
    TerminalAt p M D h ε k := by
  refine ⟨a.withKappa (max a.κ (p.K k)), le_trans h1 (le_max_left _ _),
    le_max_right _ _, max_le hε hK, hT, ?_⟩
  exact ha.mono_kappa hp (lt_of_lt_of_le one_pos h1) (le_max_left _ _)

end Submission.Obl.k4_balanced_native_packet_transport.CPF
