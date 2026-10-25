import Submission.Obl.k4_subcritical_endpoint_native_pairing.Interface

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing

open Set MeasureTheory Filter
open scoped ENNReal
open Submission.Obl.k4_critical_intercept_concentration.Data

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α]

def parameterWidth (cfg : Data α) (k : ℕ) (s : ℝ) : ℝ := cfg.N k ^ (-2 * cfg.κ * s)

def hiddenWidth (cfg : Data α) (k : ℕ) (s : ℝ) : ℝ := cfg.N k ^ (-s)

def velocityWeight (cfg : Data α) (k : ℕ) (χ : ℝ) (v : ℤ) : ENNReal :=
  cfg.π k (Ico ((v : ℝ) * χ) (((v : ℝ) + 1) * χ))

/-- An endpoint family keeps its full domains and its floors in the original
residual measure. Incidence restrictions do not change these certificates. -/
structure EndpointLevel (cfg : Data α) (k : ℕ) (s M RE ζ : ℝ) where
  count : ℕ
  A : Fin count → Set α
  tag : Fin count → Fin 3 → ℤ
  coeff : Fin count → Fin 6 → ℝ
  measurable : ∀ i, MeasurableSet (A i)
  disjoint : Pairwise (fun i j => Disjoint (A i) (A j))
  bins : ∀ i, ∀ l ∈ A i,
    ⌊cfg.b k l 3 / (cfg.N k ^ (-M))⌋ = tag i 0 ∧
    ⌊cfg.b k l 0 / cfg.parameterWidth k s⌋ = tag i 1 ∧
    ⌊cfg.b k l 1 / cfg.parameterWidth k s⌋ = tag i 2
  coefficient_bound : ∀ i e, |coeff i e| ≤ cfg.N k ^ RE
  norm_bound : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1,
    ∀ p ∈ Icc ((tag i 1 : ℝ) * cfg.parameterWidth k s)
      (((tag i 1 : ℝ) + 1) * cfg.parameterWidth k s),
    ∀ q ∈ Icc ((tag i 2 : ℝ) * cfg.parameterWidth k s)
      (((tag i 2 : ℝ) + 1) * cfg.parameterWidth k s),
      |predictor (coeff i) t p q| ≤ cfg.N k ^ ζ
  fit : ∀ i, ∀ l ∈ A i, ∀ t ∈ Icc (0 : ℝ) 1,
    |(cfg.x k l t) 3 - predictor (coeff i) t (cfg.b k l 0) (cfg.b k l 1)| ≤
      cfg.N k ^ ζ * cfg.hiddenWidth k s
  floor : ∀ i,
    ENNReal.ofReal (cfg.parameterWidth k s ^ 2 * cfg.hiddenWidth k s ^ cfg.d /
      cfg.N k ^ ζ) * cfg.velocityWeight k (cfg.N k ^ (-M)) (tag i 0) ≤
      cfg.ρ k (A i ×ˢ Icc (0 : ℝ) 1)

variable {cfg : Data α}

/-- Package any finite simultaneous endpoint call without changing its law or
the original endpoint domains. -/
theorem eventually_endpoint_levels {M sMax RE : ℝ}
    (hE : cfg.EndpointWith M sMax RE) (m : ℕ) (depth : Fin m → ℝ)
    (hdepth : ∀ r, 0 < depth r ∧ depth r < sMax) {ζ : ℝ} (hζ : 0 < ζ) :
    ∀ᶠ k in atTop, ∃ (σ : Measure (α × ℝ)), σ ≤ cfg.ρ k ∧
      ENNReal.ofReal (cfg.N k ^ (-ζ)) ≤ σ univ ∧
      ∃ H : (r : Fin m) → cfg.EndpointLevel k (depth r) M RE ζ,
        ∀ᵐ p ∂σ, ∀ r, ∃ i, p.1 ∈ (H r).A i := by
  filter_upwards [hE.2.2.2.2 m depth hdepth ζ hζ] with k hk
  obtain ⟨σ, hσ, hmass, nH, AH, qH, hH, hlevels⟩ := hk
  let H (r : Fin m) : cfg.EndpointLevel k (depth r) M RE ζ := {
    count := nH r
    A := AH r
    tag := qH r
    coeff := hH r
    measurable := (hlevels r).1
    disjoint := (hlevels r).2.1
    bins := fun i => ((hlevels r).2.2.1 i).1
    coefficient_bound := fun i => ((hlevels r).2.2.1 i).2.1
    norm_bound := fun i => ((hlevels r).2.2.1 i).2.2.1
    fit := fun i => ((hlevels r).2.2.1 i).2.2.2.1
    floor := fun i => (((hlevels r).2.2.1 i).2.2.2.2).trans (hσ _) }
  refine ⟨σ, hσ, hmass, H, ae_all_iff.mpr ?_⟩
  intro r
  rw [ae_iff]
  exact (hlevels r).2.2.2

/-- Full original endpoint floors bound the total list references. This sum
is unchanged when the incidence law is restricted by matching. -/
theorem EndpointLevel.reference_budget {k : ℕ} {s M RE ζ : ℝ}
    (H : cfg.EndpointLevel k s M RE ζ) (hN : 0 < cfg.N k) :
    (∑ i, ENNReal.ofReal (cfg.parameterWidth k s ^ 2 * cfg.hiddenWidth k s ^ cfg.d) *
      cfg.velocityWeight k (cfg.N k ^ (-M)) (H.tag i 0)) ≤
        ENNReal.ofReal (cfg.N k ^ ζ) * cfg.ρ k univ := by
  have hpow : 0 < cfg.N k ^ ζ := Real.rpow_pos_of_pos hN _
  have hterm (i : Fin H.count) :
      ENNReal.ofReal (cfg.parameterWidth k s ^ 2 * cfg.hiddenWidth k s ^ cfg.d) *
        cfg.velocityWeight k (cfg.N k ^ (-M)) (H.tag i 0) ≤
      ENNReal.ofReal (cfg.N k ^ ζ) * cfg.ρ k (H.A i ×ˢ Icc (0 : ℝ) 1) := by
    have h := mul_le_mul' (le_refl (ENNReal.ofReal (cfg.N k ^ ζ))) (H.floor i)
    convert h using 1
    rw [← mul_assoc, ← ENNReal.ofReal_mul hpow.le]
    congr 2
    field_simp
  have hdisj : Pairwise (fun i j => Disjoint (H.A i ×ˢ Icc (0 : ℝ) 1)
      (H.A j ×ˢ Icc (0 : ℝ) 1)) := fun i j hij =>
    (H.disjoint hij).set_prod_left _ _
  have hsum : (∑ i, cfg.ρ k (H.A i ×ˢ Icc (0 : ℝ) 1)) =
      cfg.ρ k (⋃ i, H.A i ×ˢ Icc (0 : ℝ) 1) := by
    rw [measure_iUnion hdisj (fun i => (H.measurable i).prod measurableSet_Icc),
      tsum_fintype]
  calc
    _ ≤ ∑ i, ENNReal.ofReal (cfg.N k ^ ζ) * cfg.ρ k (H.A i ×ˢ Icc (0 : ℝ) 1) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = ENNReal.ofReal (cfg.N k ^ ζ) * ∑ i, cfg.ρ k (H.A i ×ˢ Icc (0 : ℝ) 1) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
      apply mul_le_mul' le_rfl
      rw [hsum]
      exact measure_mono (subset_univ _)

end Data
end
end Submission.Obl.k4_subcritical_endpoint_native_pairing
