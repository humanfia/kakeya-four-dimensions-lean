import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.DeepVariation
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.DeepPrune
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Menus

set_option linter.unusedVariables false

/-!
# Fine states of a coarse block and their velocity domination

A fine state of an incidence of a coarse true block records its normalized base cell, its
transverse cell and its residual cell.  On a deep atlas block nested in the coarse block the
fine state takes at most `81` values, so the deep-block pruning gives conditional velocity
domination at every fine state.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

/-- The four normalized coordinates of an incidence. -/
def coords (F : Frame) (b : Fin 6 → ℝ) (t : ℝ) : Fin 4 → ℝ :=
  ![F.zt t, F.zZ b t, F.tr b t, F.resid b t]

/-- The fine state at resolutions `δz` (base), `δU` (transverse), `δX` (residual). -/
def sigmaState (F : Frame) (δz δU δX : ℝ) (b : Fin 6 → ℝ) (t : ℝ) : Fin 4 → ℤ :=
  fun i => ⌊coords F b t i / (![δz, δz, δU, δX] : Fin 4 → ℝ) i⌋

theorem measurable_coords {α : Type} [MeasurableSpace α] (F : Frame) {b : α → Fin 6 → ℝ}
    (hb : Measurable b) : Measurable (fun p : α × ℝ => coords F (b p.1) p.2) := by
  have hbi : ∀ i, Measurable fun p : α × ℝ => b p.1 i :=
    fun i => (measurable_pi_apply i).comp (hb.comp measurable_fst)
  have ht : Measurable fun p : α × ℝ => p.2 := measurable_snd
  apply measurable_pi_lambda
  intro i
  fin_cases i
  all_goals simp [coords, Frame.zt, Frame.zZ, Frame.tr, Frame.resid]
  all_goals fun_prop

theorem measurable_sigmaState {α : Type} [MeasurableSpace α] (F : Frame) (δz δU δX : ℝ)
    {b : α → Fin 6 → ℝ} (hb : Measurable b) :
    Measurable (fun p : α × ℝ => sigmaState F δz δU δX (b p.1) p.2) := by
  apply measurable_pi_lambda
  intro i
  exact (((measurable_pi_apply i).comp (measurable_coords F hb)).div_const _).floor

/-- **Velocity domination at fine states.**  If the four coordinate variations on deep blocks
fit in the resolutions, the deep-block pruning gives domination at every fine state. -/
theorem sigma_prune {α : Type} [MeasurableSpace α] {cfg : Data α} {k : ℕ} {s se R v' : ℝ}
    (hν : IsProbabilityMeasure (cfg.ν k)) (hK1 : 1 ≤ cfg.K k) (hN : 0 < cfg.N k)
    (hb : Measurable (cfg.b k))
    (hμ : cfg.μ k ≤ ENNReal.ofReal (cfg.K k) • (cfg.ν k).prod volume)
    (hB : BlocksAt cfg k s R) (hBe : BlocksAt cfg k se R)
    (hnest : ∀ j : Fin (cfg.n k se), ∃ h : Fin (cfg.n k s), cfg.A k se j ⊆ cfg.A k s h ∧
      Data.I (cfg.T k se) (cfg.j k se j) ⊆ Data.I (cfg.T k s) (cfg.j k s h))
    (hv'1 : R⁻¹ ≤ v') (hv'2 : v' ≤ R)
    (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) (hL : HorizontalForm (cfg.F k s i) L)
    (θ : Measure (α × ℝ)) (hθ : θ ≤ cfg.μ k)
    (hθsupp : ∀ᵐ p ∂θ, p.1 ∈ cfg.B k s i ∧ p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i))
    {δz δU δX : ℝ} (hδz : 0 < δz) (hδU : 0 < δU) (hδX : 0 < δX)
    (F : Frame) (hF : F = blockFrame cfg k s i L)
    (qe ge ae K W : ℝ) (hqe : qe = ((2 : ℝ) ^ cfg.T k se)⁻¹) (hge : ge = cfg.N k ^ (-cfg.κ * se))
    (hae : ae = cfg.N k ^ (-se)) (hKd : K = cfg.K k)
    (hW : W = 14 * K ^ 2 * qe ^ 2 + 2 * K * qe * ge)
    (hvz : qe / F.q ≤ δz) (hvZ : 5 * K * qe / F.q ≤ δz)
    (hvU : (10 * K ^ 2 * qe + 2 * K * qe * ge) / (F.q * F.g) ≤ δU)
    (hvX : (K * (1 + ae / qe) * (5 * K * qe) + K * (1 + ae / qe ^ 2) * W + 2 * K * ae +
        K * (1 + F.a / F.q) * (5 * K * qe) + K * (1 + F.a / F.q ^ 2) * W) / F.a ≤ δX)
    (δp : ℝ≥0∞) (hδ0 : δp ≠ 0) (hδtop : δp ≠ ⊤) :
    ∃ θ' : Measure (α × ℝ), θ' ≤ θ ∧
      θ univ ≤ θ' univ + δp * (((81 : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal ((2 : ℝ) ^ cfg.T k s)⁻¹ * cfg.ν k (cfg.A k s i))) ∧
      ∀ (σ₀ : Fin 4 → ℤ) (A : Set ℤ),
        θ' {p | sigmaState F δz δU δX (cfg.b k p.1) p.2 = σ₀ ∧
            vbin (cfg.N k ^ (-v')) (cfg.b k p.1 3) ∈ A} ≤
          (ENNReal.ofReal (cfg.K k) / δp) *
            θ' ((fun p : α × ℝ => sigmaState F δz δU δX (cfg.b k p.1) p.2) ⁻¹' {σ₀}) *
            paletteBins (cfg.π k) (cfg.N k ^ (-v')) A := by
  classical
  let par : Fin (cfg.n k se) → Fin (cfg.n k s) := fun j => Classical.choose (hnest j)
  have hpar : ∀ j, cfg.A k se j ⊆ cfg.A k s (par j) ∧
      Data.I (cfg.T k se) (cfg.j k se j) ⊆ Data.I (cfg.T k s) (cfg.j k s (par j)) :=
    fun j => Classical.choose_spec (hnest j)
  let r : Fin 4 → ℝ := ![δz, δz, δU, δX]
  have hr : ∀ e, 0 < r e := by
    intro e; fin_cases e <;> simp [r, hδz, hδU, hδX]
  let G : Set (α × ℝ) := cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i)
  have hmenu_ex : ∀ j : Fin (cfg.n k se), ∃ M : Finset (Fin 4 → ℤ), M.card ≤ 3 ^ 4 ∧
      ∀ p ∈ (cfg.B k se j ×ˢ Data.I (cfg.T k se) (cfg.j k se j)) ∩ G,
        (fun e => ⌊coords F (cfg.b k p.1) p.2 e / r e⌋) ∈ M := by
    intro j
    apply exists_floor_menu _ G (fun p => coords F (cfg.b k p.1) p.2) r hr
    rintro ⟨l, t⟩ ⟨⟨hl, ht⟩, -⟩ ⟨l', t'⟩ ⟨⟨hl', ht'⟩, hl'i, ht'i⟩ e
    obtain ⟨h1, h2, h3, h4⟩ := deep_coord_variation hK1 hN hB hBe i L hL j hl hl' ht ht' hl'i ht'i
      F hF qe ge ae K W hqe hge hae hKd hW
    fin_cases e
    · simpa [coords, r] using h1.trans hvz
    · simpa [coords, r] using h2.trans hvZ
    · simpa [coords, r] using h3.trans hvU
    · simpa [coords, r] using h4.trans hvX
  choose menu hmenu_card hmenu_mem using hmenu_ex
  have hstate : Measurable fun p : α × ℝ => sigmaState F δz δU δX (cfg.b k p.1) p.2 :=
    measurable_sigmaState F δz δU δX hb
  have hmenu : ∀ᵐ p ∂θ, ∀ j, p.1 ∈ cfg.B k se j → p.2 ∈ Data.I (cfg.T k se) (cfg.j k se j) →
      sigmaState F δz δU δX (cfg.b k p.1) p.2 ∈ menu j := by
    filter_upwards [hθsupp] with p hp j hj1 hj2
    exact hmenu_mem j p ⟨⟨hj1, hj2⟩, hp⟩
  exact deep_prune hν hK1 hμ hB hBe par hpar hv'1 hv'2 i θ hθ hθsupp _ hstate 81 menu
    (fun j => (hmenu_card j).trans (by norm_num)) hmenu δp hδ0 hδtop

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
