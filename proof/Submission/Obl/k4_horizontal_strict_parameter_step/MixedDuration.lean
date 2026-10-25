import Submission.Obl.k4_horizontal_strict_parameter_step.InstantaneousCaps
import Submission.Obl.k4_horizontal_strict_parameter_step.FirstJet.Statement

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d50c59d5b1367f287a76eef33f4c400a8e312ee2,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/MixedDuration.lean`.
The namespace and internal imports are changed to o272. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4Homogenization

noncomputable section

/-- One fixed finite time partition, chosen below the finest scalar width,
turns integrated affine mixed caps into the exact fixed-prior grid cap. -/
theorem affine_mixed_cap_from_duration {α J : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (lam : Measure (α × ℝ))
    (y : α → Fin 2 → ℝ) (β γ : α → ℝ)
    (hy : Measurable y) (hβ : Measurable β) (hγ : Measurable γ)
    {E E₀ : Set (α × ℝ)} (hE : MeasurableSet E) (hE₀ : MeasurableSet E₀)
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (left : J → ℝ) {τ V ζ δ K B d : ℝ}
    (hτ : 0 < τ) (hζ : 0 < ζ) (hδ : 0 < δ) (hK : 0 < K) (hB : 0 ≤ B)
    (hγV : ∀ l, |γ l| ≤ V) (hsmall : V * τ ≤ ζ)
    (hcover : ∀ t ∈ Icc (0 : ℝ) 1, ∃ i, t ∈ Icc (left i) (left i + τ))
    (hweighted : ENNReal.ofReal δ • (ν.prod volume).restrict E₀ ≤ lam)
    (hduration : ∀ p ∈ E, ∀ i, p.2 ∈ Icc (left i) (left i + τ) →
      ENNReal.ofReal (τ / K) ≤
        incidenceDuration volume (E₀.indicator 1) (Icc (left i) (left i + τ)) p.1)
    (hcap : ∀ (i : J) (r w : ℝ), ζ ≤ r → r ≤ 1 → ζ ≤ w → w ≤ 1 →
      ∀ (x₀ : ℝ) (y₀ : Fin 2 → ℝ),
      lam {p | p.2 ∈ Icc (left i) (left i + τ) ∧
        |FirstJet.xbar β γ p.1 p.2 - x₀| ≤ 2 * w ∧
        |y p.1 0 - y₀ 0| ≤ r ∧ |y p.1 1 - y₀ 1| ≤ r} ≤
        ENNReal.ofReal ((B * r ^ 2 * w ^ d) * τ)) :
    ∀ t r w : ℝ, ζ ≤ r → r ≤ 1 → ζ ≤ w → w ≤ 1 →
      ∀ (z : Fin 2 → ℤ) (j : ℤ),
      ν {l | (l, t) ∈ E ∧ ⌊FirstJet.xbar β γ l t / w⌋ = j ∧
        ⌊y l 0 / r⌋ = z 0 ∧ ⌊y l 1 / r⌋ = z 1} ≤
        ENNReal.ofReal ((K * B / δ) * r ^ 2 * w ^ d) := by
  intro t r w hr hr1 hw hw1 z j
  have hrp : 0 < r := hζ.trans_le hr
  have hwp : 0 < w := hζ.trans_le hw
  let C : Set α := {l | (l, t) ∈ E ∧ ⌊FirstJet.xbar β γ l t / w⌋ = j ∧
    ⌊y l 0 / r⌋ = z 0 ∧ ⌊y l 1 / r⌋ = z 1}
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  swap
  · have hempty : C = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro l hl
      exact ht (hunit hl.1).2
    change ν C ≤ _
    rw [hempty, measure_empty]
    exact zero_le
  obtain ⟨i, hi⟩ := hcover t ht
  let Cplus : Set (α × ℝ) := {p |
    |FirstJet.xbar β γ p.1 p.2 - (j : ℝ) * w| ≤ 2 * w ∧
    |y p.1 0 - (z 0 : ℝ) * r| ≤ r ∧ |y p.1 1 - (z 1 : ℝ) * r| ≤ r}
  have hCm : MeasurableSet C := by
    have he : Measurable (fun l : α => (l, t)) := measurable_id.prodMk measurable_const
    have hx : Measurable (fun l => ⌊FirstJet.xbar β γ l t / w⌋) := by
      unfold FirstJet.xbar
      fun_prop
    have h0 : Measurable (fun l => ⌊y l 0 / r⌋) := by fun_prop
    have h1 : Measurable (fun l => ⌊y l 1 / r⌋) := by fun_prop
    exact (hE.preimage he).inter ((hx (measurableSet_singleton j)).inter
      ((h0 (measurableSet_singleton (z 0))).inter (h1 (measurableSet_singleton (z 1)))))
  have hfloor {x a : ℝ} {k : ℤ} (ha : 0 < a) (hk : ⌊x / a⌋ = k) :
      |x - (k : ℝ) * a| ≤ a := by
    have hh := Int.floor_eq_iff.mp hk
    rw [le_div_iff₀ ha, div_lt_iff₀ ha] at hh
    rw [abs_of_nonneg (sub_nonneg.mpr hh.1)]
    nlinarith [hh.2]
  have himp : ∀ l ∈ C, ∀ u ∈ Icc (left i) (left i + τ), (l, u) ∈ Cplus := by
    intro l hl u hu
    refine ⟨?_, hfloor hrp hl.2.2.1, hfloor hrp hl.2.2.2⟩
    have hh := affine_constraint_over_interval hi hu (hγV l) (hfloor hwp hl.2.1)
    change |β l + u * γ l - (j : ℝ) * w| ≤ 2 * w
    exact hh.trans (by linarith)
  have hG : Measurable (E₀.indicator (1 : α × ℝ → ENNReal)) :=
    measurable_const.indicator hE₀
  have hweighted' : ENNReal.ofReal δ •
      (ν.prod volume).withDensity (E₀.indicator 1) ≤ lam := by
    simpa only [withDensity_indicator_one hE₀] using hweighted
  have hb := instantaneous_cap_of_weighted_duration ν lam hG measurableSet_Icc hCm Cplus himp
    hδ hτ hK (by positivity : 0 ≤ B * r ^ 2 * w ^ d) hweighted' (by
      have hevent : Cplus ∩ (univ ×ˢ Icc (left i) (left i + τ)) =
          {p | p.2 ∈ Icc (left i) (left i + τ) ∧
            |FirstJet.xbar β γ p.1 p.2 - (j : ℝ) * w| ≤ 2 * w ∧
            |y p.1 0 - (z 0 : ℝ) * r| ≤ r ∧ |y p.1 1 - (z 1 : ℝ) * r| ≤ r} := by
        ext p
        simp only [Cplus, mem_inter_iff, mem_setOf_eq, mem_prod, mem_univ, true_and]
        tauto
      rw [hevent]
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using
        hcap i r w hr hr1 hw hw1 ((j : ℝ) * w) ![(z 0 : ℝ) * r, (z 1 : ℝ) * r])
  change ν C ≤ _
  calc
    _ ≤ ν (durationRetained volume (E₀.indicator 1) (Icc (left i) (left i + τ))
        (ENNReal.ofReal (τ / K)) ∩ C) := by
      apply measure_mono
      intro l hl
      exact ⟨hduration (l, t) hl.1 i hi, hl⟩
    _ ≤ ENNReal.ofReal (K * (B * r ^ 2 * w ^ d) / δ) := hb
    _ = _ := by congr 1; ring

end

end Submission.Obl.k4_horizontal_strict_parameter_step
