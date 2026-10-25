import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.AsymptoticBudget
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ModelScales
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.LabelBounds

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

open Submission.Lib.K4QuadraticSheetCore

open Filter

variable {α : Type*} [MeasurableSpace α] (p : Model α)

/-- All numerical hypotheses for the three-entry label adapter at one fixed depth. -/
structure PaletteBudgetAt (H : ℕ → ℝ) (C s v ε : ℝ) (k : ℕ) : Prop where
  card : (3 : ℝ) ≤ p.N k ^ ε
  theta_pos : 0 < p.N k ^ (-v)
  theta_le_one : p.N k ^ (-v) ≤ 1
  lam_pos : 0 < fineLam (p.K k) (H k)
  lam_le_one : fineLam (p.K k) (H k) ≤ 1
  contact : p.N k ^ (-p.e₀) ≤ p.q k s
  proximity : p.N k ^ (-40 * s) + 6 * p.K k ^ 2 * p.q k p.U ≤ p.N k ^ (-30 * s)
  loss : fineLoss C (p.K k) (H k) (p.N k ^ (-v)) ≤ p.N k ^ ε
  smallness : fineLoss C (p.K k) (H k) (p.N k ^ (-v)) *
    (p.N k ^ (-p.e₀) / (p.q k s * labelμ (p.K k) (p.N k ^ (-v))) +
      7 * p.K k * p.N k ^ (-30 * s) / p.q k s ^ 2) ≤ 1

/-- The separation exponent can be chosen after the requested palette allowance. -/
theorem eventually_palette_budget (hp : p.Valid)
    (H : ℕ → ℝ) (hH : ∀ k, 1 ≤ H k)
    (hHsub : ∀ e : ℝ, 0 < e → ∀ᶠ k in atTop, H k ≤ p.N k ^ e)
    {C s ε : ℝ} (hC : 0 ≤ C) (hs : 0 < s) (hsU : s ≤ p.U)
    (hdeep : 30 * s < p.κ * p.U) (hcontact : 2 * s < p.e₀) (hε : 0 < ε) :
    ∃ v : ℝ, 0 < v ∧ ∀ᶠ k in atTop, p.PaletteBudgetAt H C s v ε k := by
  let v : ℝ := min ε s / 1000
  have hv : 0 < v := div_pos (lt_min hε hs) (by norm_num)
  have hve : 240 * v < ε := by
    have := min_le_left ε s
    dsimp [v]
    linarith
  have hvs : 240 * v < s := by
    have := min_le_right ε s
    dsimp [v]
    linarith
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [hp.N_ge k]
  let R : ℝ := 2 + s⁻¹ + p.U⁻¹
  have hsip : 0 < s⁻¹ := inv_pos.mpr hs
  have hUip : 0 < p.U⁻¹ := inv_pos.mpr hp.U_pos
  have hR : 1 < R := by dsimp [R]; linarith
  have hsR : R⁻¹ ≤ s := by
    have h : s⁻¹ ≤ R := by dsimp [R]; linarith
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le hsip h
  have hUR : R⁻¹ ≤ p.U := by
    have h : p.U⁻¹ ≤ R := by dsimp [R]; linarith
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le hUip h
  have hcard : ∀ᶠ k in atTop, (3 : ℝ) ≤ p.N k ^ ε :=
    ((tendsto_rpow_atTop hε).comp hp.N_lim).eventually (eventually_ge_atTop 3)
  refine ⟨v, hv, ?_⟩
  filter_upwards [hp.labels R hR, hcard,
    eventually_fine_loss p.N p.K H hN1 hp.N_lim hp.K_ge hH hp.K_sub hHsub hC hve,
    eventually_fine_loss p.N p.K H hN1 hp.N_lim hp.K_ge hH hp.K_sub hHsub hC hvs,
    eventually_fine_proximity p.N p.K hN1 hp.N_lim hp.K_ge hp.K_sub hs hdeep,
    eventually_fine_smallness p.N p.K hN1 hp.N_lim hp.K_ge hp.K_sub hs hp.κ_le_one hcontact]
    with k hlabels hcard hloss hlosss hprox hsmall
  obtain ⟨hlo, hhi, _⟩ := hlabels s hsR hsU
  obtain ⟨hloU, hhiU, _⟩ := hlabels p.U hUR le_rfl
  have hqs := q_bounds_of_resolution p hp hlo hhi
  have hqU := q_bounds_of_resolution p hp hloU hhiU
  have htheta : p.N k ^ (-v) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (hN1 k) (by linarith)
  have htheta0 : 0 < p.N k ^ (-v) := Real.rpow_pos_of_pos (Valid.N_pos p hp k) _
  have hlam := fineLam_bounds (hp.K_ge k) (hH k)
  have hmu : 1 ≤ labelμ (p.K k) (p.N k ^ (-v)) :=
    fine_normalization_ge_one (hp.K_ge k) htheta0 htheta
  have hE : 0 ≤ fineLoss C (p.K k) (H k) (p.N k ^ (-v)) := by
    unfold fineLoss
    exact mul_nonneg hC (by positivity)
  have hsmall' := hsmall (p.q k s) (labelμ (p.K k) (p.N k ^ (-v)))
    (fineLoss C (p.K k) (H k) (p.N k ^ (-v))) (p.q_pos k s) hqs.1 hmu hE hlosss
  exact ⟨hcard, htheta0, htheta, hlam.1, hlam.2, hsmall'.1,
    hprox (p.q k p.U) hqU.2, hloss, hsmall'.2⟩

/-- One fixed positive depth range leaves margins for both the deep witnesses and contact error. -/
theorem exists_fine_depth_range (hp : p.Valid) :
    ∃ U₁ : ℝ, 0 < U₁ ∧ U₁ ≤ p.U ∧ ∀ s : ℝ, 0 < s → s ≤ U₁ →
      s < p.U ∧ 30 * s < p.κ * p.U ∧ 2 * s < p.e₀ := by
  let U₁ : ℝ := min (p.κ * p.U / 100) (p.e₀ / 4)
  have hprod : 0 < p.κ * p.U := mul_pos hp.κ_pos hp.U_pos
  have hprodU : p.κ * p.U ≤ p.U := by
    simpa using mul_le_mul_of_nonneg_right hp.κ_le_one hp.U_pos.le
  have hU1 : 0 < U₁ := lt_min (div_pos hprod (by norm_num))
    (div_pos hp.e₀_pos (by norm_num))
  have hU1U : U₁ ≤ p.U := by
    have : U₁ ≤ p.κ * p.U / 100 := min_le_left _ _
    linarith
  refine ⟨U₁, hU1, hU1U, fun s hs hsU => ?_⟩
  have h1 : s ≤ p.κ * p.U / 100 := hsU.trans (min_le_left _ _)
  have h2 : s ≤ p.e₀ / 4 := hsU.trans (min_le_right _ _)
  exact ⟨by linarith, by linarith, by linarith⟩

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model
