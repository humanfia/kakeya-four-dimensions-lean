import Submission.Obl.k4_critical_affine_derivative_preparation.Expanded

namespace Submission.Obl.k4_critical_affine_derivative_preparation

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal
open Submission.Obl.k4_affine_skew_row_fit

/-- Attach the completed row list and enlarge only the numerical loss.
All functions and both measures are exactly the supplied continuous ones. -/
def completePreRow {S a η ε N : ℝ} {α : Type} [MeasurableSpace α]
    (prior : Measure α) (active : Measure (α × ℝ))
    (intercept velocity evaluation : α → ℝ) (row : α × ℝ → Fin 2 → ℝ)
    (palette : Measure ℝ) (error : ℝ)
    (lists : (Fin 2 → ℤ) → ℤ → Finset ℤ)
    (h : PreRowInputs S a η N α prior active intercept velocity evaluation row palette error lists)
    (hN : 1 ≤ N) (hη : η ≤ ε)
    (bins : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ))
    (hcard : ∀ q, ((bins q).card : ℝ) ≤ N ^ ε)
    (hbin : ∀ᵐ p ∂active, (fun e => ⌊row p e / error⌋) ∈ bins
      (fun e => ⌊(![p.2, intercept p.1 + p.2 * velocity p.1] : Fin 2 → ℝ) e /
        (N ^ (-a))⌋)) : IncidenceData S a ε N α := by
  rcases h with ⟨hb, hv, heval, hrowmeas, hprior, hpalette, herrlo, herrhi,
    htraj, hdom, hsupport, hmass, hpal, hjoint, hrow, _hlistcard, _hlist, _hcond⟩
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hpow : N ^ η ≤ N ^ ε := Real.rpow_le_rpow_of_exponent_le hN hη
  have hneg : N ^ (-ε) ≤ N ^ (-η) :=
    Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hη)
  have hE : 0 ≤ error := (Real.rpow_pos_of_pos hNpos (-a)).le.trans herrlo
  exact {
    prior := prior
    active := active
    intercept := intercept
    velocity := velocity
    evaluation := evaluation
    row := row
    palette := palette
    error := error
    bins := bins
    measurable_intercept := hb
    measurable_velocity := hv
    measurable_evaluation := heval
    measurable_row := hrowmeas
    prior_probability := hprior
    palette_probability := hpalette
    error_lower := herrlo
    error_upper := herrhi
    trajectory_bound := fun l => (htraj l).trans hpow
    domination := hdom.trans (by
      intro s
      exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hpow) zero_le)
    time_support := hsupport
    mass_lower := (ENNReal.ofReal_le_ofReal hneg).trans hmass
    palette_cap := fun x r hr hr1 => (hpal x r hr hr1).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hpow
        (Real.rpow_nonneg ((Real.rpow_pos_of_pos hNpos (-a)).le.trans hr) _)))
    joint_cap := fun q j => (hjoint q j).trans
      (mul_le_mul_of_nonneg_right
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hpow (sq_nonneg _))) zero_le)
    bins_card := hcard
    row_constraint := by
      filter_upwards [hrow, hbin] with p hp hbp
      exact ⟨fun j => (hp.1 j).trans hpow, hbp,
        hp.2.trans (mul_le_mul_of_nonneg_right hpow hE)⟩
  }

namespace Data

variable {α : Type} [MeasurableSpace α]

/-- Interpolation supplies the sole missing Row field, at every requested loss. -/
theorem prepared_rows_of_conditional (hcomplete : RowListCompletion)
    (cfg : Data α) (h : cfg.Valid) (s : ℝ) (hs : 0 < s)
    (hconditional : ∀ η : ℝ, 0 < η → ∃ᶠ k in atTop, cfg.ConditionalRowAt k s η) :
    ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
      Nonempty (cfg.PreparedRowAt k s (200 * s) ε) := by
  intro ε hε
  obtain ⟨η, hη, hηε, N₀, hN₀, hlist⟩ :=
    hcomplete cfg.S (200 * s) ε h.palette_pos (by positivity) hε
  have hlarge : ∀ᶠ k in atTop, N₀ ≤ cfg.N k :=
    h.scale_limit.eventually (eventually_ge_atTop N₀)
  apply ((hconditional η hη).and_eventually hlarge).mono
  rintro k ⟨hk, hNk⟩
  rcases hk with ⟨i, current, t₀, Z₀, intercept, velocity, evaluation, row, lists,
    hinputs, ht₀, hZ₀, hW, hcurrent, hcoords, hbounds, htime⟩
  obtain ⟨bins, hcard, hbin⟩ := hlist (cfg.N k) hNk α
    ((cfg.ν k (cfg.A k s i))⁻¹ • (cfg.ν k).restrict (cfg.A k s i))
    (ENNReal.ofReal (cfg.timeLength k s * (cfg.ν k).real (cfg.A k s i))⁻¹ •
      current.map (unitTimeMap t₀ (cfg.timeLength k s)))
    intercept velocity evaluation row (cfg.π k) (cfg.N k ^ (-s)) lists hinputs
  let incidence := completePreRow
    ((cfg.ν k (cfg.A k s i))⁻¹ • (cfg.ν k).restrict (cfg.A k s i))
    (ENNReal.ofReal (cfg.timeLength k s * (cfg.ν k).real (cfg.A k s i))⁻¹ •
      current.map (unitTimeMap t₀ (cfg.timeLength k s)))
    intercept velocity evaluation row (cfg.π k) (cfg.N k ^ (-s)) lists
    hinputs (by linarith [h.scale k]) hηε bins hcard hbin
  exact ⟨{
    label := i
    incidence := incidence
    current := current
    time_origin := t₀
    horizontal_origin := Z₀
    time_origin_bound := ht₀
    horizontal_origin_bound := hZ₀
    prior_eq := rfl
    palette_eq := rfl
    reference_pos := hW
    current_le := hcurrent
    normalized_eq := rfl
    coordinates := hcoords
    native_bounds := hbounds
    error_eq := rfl
    time_upper := htime
  }⟩

end Data

/-- All hard work is exposed as the three child propositions. The recovery
of coefficients, derivative precision and original mass is already proved. -/
theorem derivative_preparation_from_three
    (hlists : DerivativeListPreparation)
    (hconditional : ConditionalRowPreparation)
    (hcomplete : RowListCompletion)
    (hRow : Row) (hMatch : Match) : DerivativePreparation := by
  apply derivative_preparation_of_packed
  intro α inst cfg h
  obtain ⟨s, hs, hsU, hse₀, hsone, hlist⟩ := hlists hRow hMatch α cfg h
  have hcond := hconditional α cfg h s hs hsU hse₀ hsone hlist
  exact cfg.primitive_of_prepared_rows h hRow s (200 * s) hs hsU hse₀ hsone
    (by positivity) (Data.prepared_rows_of_conditional hcomplete cfg h s hs hcond)

end

end Submission.Obl.k4_critical_affine_derivative_preparation
