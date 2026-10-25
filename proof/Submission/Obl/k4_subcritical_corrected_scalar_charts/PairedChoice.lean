/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/PairedChoice.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.PairedInterface
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeBlockChoice
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeLevel

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory
open Submission.Obl.k4_critical_intercept_concentration.Data

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α]

/-- One of the full original endpoint families after comparison. The chart
domains and every floor remain those of the original residual measure. -/
structure PairedLayer (cfg : Data α) (k : ℕ) (M s ε : ℝ) where
  charts : ChartFamily α
  paired : Fin charts.n → Fin (cfg.n k s) → Prop
  measurable : ∀ c, MeasurableSet (charts.G c)
  disjoint : ∀ c c', c ≠ c' → Disjoint (charts.G c) (charts.G c')
  labels : ∀ c, ∀ l ∈ charts.G c,
    ⌊cfg.b k l 3 / cfg.N k ^ (-M)⌋ = charts.q c 0 ∧
    ⌊cfg.b k l 0 / cfg.N k ^ (-(2 * cfg.κ * s))⌋ = charts.q c 1 ∧
    ⌊cfg.b k l 1 / cfg.N k ^ (-(2 * cfg.κ * s))⌋ = charts.q c 2
  box : ∀ c, ∀ t ∈ Icc (0 : ℝ) 1,
    ∀ p ∈ Icc ((charts.q c 1 : ℝ) * cfg.N k ^ (-(2 * cfg.κ * s)))
      (((charts.q c 1 : ℝ) + 1) * cfg.N k ^ (-(2 * cfg.κ * s))),
    ∀ q ∈ Icc ((charts.q c 2 : ℝ) * cfg.N k ^ (-(2 * cfg.κ * s)))
      (((charts.q c 2 : ℝ) + 1) * cfg.N k ^ (-(2 * cfg.κ * s))),
      |parameterPredictor (charts.g c) t p q| ≤ cfg.N k ^ ε
  fit : ∀ c, ∀ l ∈ charts.G c, ∀ t ∈ Icc (0 : ℝ) 1,
    |cfg.b k l 2 + t * cfg.b k l 5 -
      parameterPredictor (charts.g c) t (cfg.b k l 0) (cfg.b k l 1)| ≤
        cfg.N k ^ ε * cfg.N k ^ (-s)
  floor : ∀ c,
    ENNReal.ofReal ((cfg.N k ^ (-(2 * cfg.κ * s))) ^ 2 *
      (cfg.N k ^ (-s)) ^ cfg.d / cfg.N k ^ ε) *
      cfg.π k (Ico ((charts.q c 0 : ℝ) * cfg.N k ^ (-M))
        (((charts.q c 0 : ℝ) + 1) * cfg.N k ^ (-M))) ≤
      cfg.ρ k (charts.G c ×ˢ Icc (0 : ℝ) 1)
  comparison : ∀ c i, paired c i →
    ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
    ∀ p ∈ Icc ((charts.q c 1 : ℝ) * cfg.N k ^ (-(2 * cfg.κ * s)))
      (((charts.q c 1 : ℝ) + 1) * cfg.N k ^ (-(2 * cfg.κ * s))),
    ∀ q ∈ Icc ((charts.q c 2 : ℝ) * cfg.N k ^ (-(2 * cfg.κ * s)))
      (((charts.q c 2 : ℝ) + 1) * cfg.N k ^ (-(2 * cfg.κ * s))),
      |cfg.nativeParameter k s i ((charts.q c 0 : ℝ) * cfg.N k ^ (-M)) t p q -
        predictor (charts.g c) t p q| ≤ cfg.N k ^ ε * cfg.N k ^ (-s)
  list_card : ∀ c (j₀ : Fin (2 ^ cfg.T k s)),
    ({i : Fin (cfg.n k s) | paired c i ∧ cfg.j k s i = j₀}.ncard : ℝ) ≤ cfg.N k ^ ε

/-- One actual coarse native entry is now fixed on each chart/time block.
The fine endpoint family is only used as a linewise time-polynomial row. -/
structure ChosenPairedSample (cfg : Data α) (k : ℕ) (M s₀ ε : ℝ) where
  σ : Measure (α × ℝ)
  le_rho : σ ≤ cfg.ρ k
  mass : ENNReal.ofReal (cfg.N k ^ (-(2 * ε))) ≤ σ univ
  coarse : cfg.PairedLayer k M s₀ ε
  fine : cfg.PairedLayer k M (3 * s₀ / 2) ε
  choice : Fin coarse.charts.n → Fin (2 ^ cfg.T k s₀) → Option (Fin (cfg.n k s₀))
  choice_good : ∀ c j i, choice c j = some i → coarse.paired c i ∧ cfg.j k s₀ i = j
  coarse_cover : ∀ᵐ p ∂σ, ∃ c i,
    p.1 ∈ coarse.charts.G c ∧ p.1 ∈ cfg.B k s₀ i ∧
      p.2 ∈ I (cfg.T k s₀) (cfg.j k s₀ i) ∧ choice c (cfg.j k s₀ i) = some i
  fine_cover : ∀ᵐ p ∂σ, ∃ c i,
    p.1 ∈ fine.charts.G c ∧ p.1 ∈ cfg.B k (3 * s₀ / 2) i ∧
      p.2 ∈ I (cfg.T k (3 * s₀ / 2)) (cfg.j k (3 * s₀ / 2) i) ∧ fine.paired c i

variable {cfg : Data α}

/-- The short paired lists furnish a chosen sample at a single additional
loss. No selection of a fine native representative is necessary. -/
theorem PairedAt.exists_chosen_sample (h : cfg.Prepared) {k : ℕ} {M RE s₀ ε : ℝ}
    (parent : cfg.NativeLevel k s₀) (hp : cfg.PairedAt k M RE s₀ ε) :
    Nonempty (cfg.ChosenPairedSample k M s₀ ε) := by
  classical
  obtain ⟨σ, nH, AH, qH, hH, paired, hσ, hmass, hlayers, hcover⟩ := hp
  let C₀ : ChartFamily α := ⟨nH 0, AH 0, qH 0, hH 0⟩
  let Cb : ChartFamily α := ⟨nH 1, AH 1, qH 1, hH 1⟩
  obtain ⟨hm₀, hd₀, hf₀, hc₀, hl₀⟩ := hlayers 0
  obtain ⟨hmb, hdb, hfb, hcb, hlb⟩ := hlayers 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_mul] at hf₀ hc₀ hl₀ hfb hcb hlb
  let coarse : cfg.PairedLayer k M s₀ ε := {
    charts := C₀, paired := paired 0, measurable := hm₀, disjoint := hd₀
    labels := fun c => (hf₀ c).1
    box := fun c => (hf₀ c).2.2.1
    fit := fun c => (hf₀ c).2.2.2.1
    floor := fun c => (hf₀ c).2.2.2.2
    comparison := hc₀, list_card := hl₀
  }
  let fine : cfg.PairedLayer k M (3 * s₀ / 2) ε := {
    charts := Cb, paired := paired 1, measurable := hmb, disjoint := hdb
    labels := fun c => (hfb c).1
    box := fun c => (hfb c).2.2.1
    fit := fun c => (hfb c).2.2.2.1
    floor := fun c => (hfb c).2.2.2.2
    comparison := hcb, list_card := hlb
  }
  letI : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  have hdom : σ ≤ ENNReal.ofReal (cfg.K k) • ((cfg.ν k).prod volume) :=
    hσ.trans ((h.basic k).2.2.2.2.1.trans (h.basic k).2.2.2.1)
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  obtain ⟨choice, hchoice, σ', hσ', hmass', hcoarse⟩ := exists_native_block_choice (cfg.ν k)
    σ (ENNReal.ofReal (cfg.K k)) hdom (cfg.T k s₀) C₀.n (cfg.n k s₀)
    C₀.G hm₀ hd₀ (cfg.B k s₀) parent.fitted_measurable (cfg.j k s₀) (paired 0)
    (Real.rpow_pos_of_pos hN ε).le hl₀
    (by filter_upwards [hcover] with p hp; exact hp 0)
  have hcancel : ENNReal.ofReal (cfg.N k ^ (-ε)) * ENNReal.ofReal (cfg.N k ^ ε) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hN]
    simp
  have hfloor : ENNReal.ofReal (cfg.N k ^ (-(2 * ε))) ≤ σ' univ := by
    calc
      _ = ENNReal.ofReal (cfg.N k ^ (-ε)) * ENNReal.ofReal (cfg.N k ^ (-ε)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hN]
        congr 1
        congr 1
        ring
      _ ≤ ENNReal.ofReal (cfg.N k ^ (-ε)) * σ univ := mul_le_mul' le_rfl hmass
      _ ≤ ENNReal.ofReal (cfg.N k ^ (-ε)) * (ENNReal.ofReal (cfg.N k ^ ε) * σ' univ) :=
        mul_le_mul' le_rfl hmass'
      _ = _ := by rw [← mul_assoc, hcancel, one_mul]
  refine ⟨{
    σ := σ', le_rho := hσ'.trans hσ, mass := hfloor
    coarse := coarse, fine := fine, choice := choice, choice_good := hchoice
    coarse_cover := hcoarse, fine_cover := ?_
  }⟩
  filter_upwards [ae_mono hσ' hcover] with p hp
  exact hp 1

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
