import Submission.Obl.k4_finite_positive_prepared_models.Stages
import Submission.Obl.k4_finite_positive_prepared_models.Synthetic.Params

/-!
# The synthetic stage model

`Par.stage` is a model index with resolution `2^Λ` and loss `2^(Λ/(n+1))`: the synthetic lines,
incidences and palette, the native test `X₃`, and at a scale `s` the labels of the level
`lev s`. This file proves its pointwise hypotheses `EH1`. Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_positive_prepared_models.Synthetic

open MeasureTheory Set MvPolynomial
open scoped Grid Synth

noncomputable section

namespace Par

variable (p : Par)

/-- The level of a scale. -/
def lev (s : ℝ) : ℕ := min p.D (⌊s * p.n * p.m₀⌋₊ - p.m₀)

/-- The enumeration of the labels at a scale. -/
def eqv (s : ℝ) : Fin (Fintype.card (p.synth.Label (p.lev s))) ≃ p.synth.Label (p.lev s) :=
  (Fintype.equivFin _).symm

/-- The resolution. -/
def sN : ℝ := (2 : ℝ) ^ (p.Λ : ℝ)

/-- The loss. -/
def sK : ℝ := p.sN ^ (1 / ((p.n : ℝ) + 1))

/-- The synthetic model index. -/
def stage : EStage (ℕ × (Fin 6 → ℝ)) where
  N := p.sN
  K := p.sK
  ν := p.synth.nu
  μ := p.synth.mu
  ρ := p.synth.mu
  π := p.synth.pal
  b := p.synth.sbS
  P := X 3
  T := fun s => p.synth.T (p.lev s)
  nl := fun s => Fintype.card (p.synth.Label (p.lev s))
  j := fun s i => (p.eqv s i).1
  A := fun s i => p.synth.sA (p.lev s) (p.eqv s i)
  B := fun s i => p.synth.sA (p.lev s) (p.eqv s i)
  c := fun s i => ![p.synth.cpos (p.lev s) (p.eqv s i).2.1.1, 0,
    (((p.eqv s i).2.2.1 : ℕ) : ℝ) / 2 ^ p.synth.Ux (p.lev s), 0, 0]
  F := fun s i => X 3 - C ((spread p.synth.e p.synth.e₁ (p.synth.Gh (p.lev s))
    ((p.eqv s i).2.2.2 : ℕ) : ℝ) / 2 ^ (p.synth.e * p.synth.Gh (p.lev s)))

theorem sN_rpow (x : ℝ) : p.sN ^ x = (2 : ℝ) ^ ((p.Λ : ℝ) * x) := by
  unfold sN
  rw [← Real.rpow_mul (by norm_num)]

theorem sK_eq : p.sK = (2 : ℝ) ^ p.σ := by
  unfold sK σ
  rw [sN_rpow]
  congr 1
  ring

theorem two_rpow_le {x y : ℝ} (h : x ≤ y) : (2 : ℝ) ^ x ≤ (2 : ℝ) ^ y :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h

theorem σ_pos : 0 < p.σ := by
  have := p.σ_ge
  have : (0 : ℝ) ≤ p.B := by positivity
  have := p.n_pos
  linarith

theorem sK_ge (c : ℝ) (hc : c ≤ p.σ) : (2 : ℝ) ^ c ≤ p.sK := by
  rw [sK_eq]; exact two_rpow_le hc

theorem one_le_sK : 1 ≤ p.sK := by
  have := p.sK_ge 0 p.σ_pos.le
  simpa using this

theorem two_le_sK : 2 ≤ p.sK := by
  have h := p.sK_ge 1 (by linarith [p.σ_ge, (show (0:ℝ) ≤ p.B by positivity), p.n_pos])
  simpa using h

theorem sK_pos : 0 < p.sK := lt_of_lt_of_le one_pos p.one_le_sK

theorem four_le_sK : 4 ≤ p.sK := by
  have h := p.sK_ge 2 (by linarith [p.σ_ge, (show (0:ℝ) ≤ p.B by positivity), p.n_pos])
  norm_num at h
  exact h

/-- The samples have coordinates in `[0,1]` almost surely. -/
theorem ae_P_support :
    ∀ᵐ ω ∂P p.synth.M, ω.2.1.1 ∈ Icc (0 : ℝ) 1 ∧ ω.2.1.2 ∈ Icc (0 : ℝ) 1 ∧
      ω.2.2 ∈ Icc (0 : ℝ) 1 := by
  have h1 : P p.synth.M {ω | ω.2.1.1 ∉ Icc (0 : ℝ) 1} = 0 := by
    refine le_antisymm ?_ bot_le
    calc P p.synth.M {ω | ω.2.1.1 ∉ Icc (0 : ℝ) 1}
        ≤ ((idx p.synth.M).prod U) univ * ((U.prod U) ((Icc 0 1)ᶜ ×ˢ univ) * U univ) :=
          P_mono_prod _ (fun ω hω => ⟨trivial, ⟨hω, trivial⟩, trivial⟩)
      _ = 0 := by rw [Measure.prod_prod]; simp [U]
  have h2 : P p.synth.M {ω | ω.2.1.2 ∉ Icc (0 : ℝ) 1} = 0 := by
    refine le_antisymm ?_ bot_le
    calc P p.synth.M {ω | ω.2.1.2 ∉ Icc (0 : ℝ) 1}
        ≤ ((idx p.synth.M).prod U) univ * ((U.prod U) (univ ×ˢ (Icc 0 1)ᶜ) * U univ) :=
          P_mono_prod _ (fun ω hω => ⟨trivial, ⟨trivial, hω⟩, trivial⟩)
      _ = 0 := by rw [Measure.prod_prod]; simp [U]
  have h3 : P p.synth.M {ω | ω.2.2 ∉ Icc (0 : ℝ) 1} = 0 := by
    refine le_antisymm ?_ bot_le
    calc P p.synth.M {ω | ω.2.2 ∉ Icc (0 : ℝ) 1}
        ≤ ((idx p.synth.M).prod U) univ * ((U.prod U) univ * U (Icc 0 1)ᶜ) :=
          P_mono_prod _ (fun ω hω => ⟨trivial, trivial, hω⟩)
      _ = 0 := by simp [U]
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_union_null (measure_union_null h1 h2) h3)
  intro ω hω
  simp only [mem_ofPred_eq, not_and_or] at hω
  rcases hω with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

theorem hid_mem (i : ℕ) (hi : i < p.synth.M) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    hid p.synth.e p.synth.e₁ p.synth.G i u ∈ Icc (0 : ℝ) 1 := by
  unfold hid
  have hlt := spread_lt p.synth.he p.synth.G i
  have hp : (0 : ℝ) < 2 ^ (p.synth.e * p.synth.G) := by positivity
  have hlt' : (spread p.synth.e p.synth.e₁ p.synth.G i : ℝ) + 1 ≤ 2 ^ (p.synth.e * p.synth.G) := by
    exact_mod_cast hlt
  constructor
  · exact div_nonneg (by have := hu.1; positivity) hp.le
  · rw [div_le_one hp]; linarith [hu.2]

theorem eval_exS_X3 (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    eval (exS p.synth.sbS l t) (X 3) = hid p.synth.e p.synth.e₁ p.synth.G l.1 (l.2 2) := by
  simp [exS, Synth.sbS]

theorem eh1_point (l : ℕ × (Fin 6 → ℝ)) (t₀ : ℝ)
    (hx : hid p.synth.e p.synth.e₁ p.synth.G l.1 (l.2 2) ∈ Icc (0 : ℝ) 1) :
    (∀ t ∈ Icc (0 : ℝ) 1, |eval (exS p.synth.sbS l t) (X 3)| ≤ p.sK ∧
      |eval (exS p.synth.sbS l t) (pderiv (3 : Fin 4) (X 3))| ≤ p.sK ∧
      |eval (exS p.synth.sbS l t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (X 3)))| ≤ p.sK) ∧
      p.sK⁻¹ ≤ |eval (exS p.synth.sbS l t₀) (pderiv (3 : Fin 4) (X 3))| := by
  have hK1 := p.one_le_sK
  have h1 : pderiv (3 : Fin 4) (X (3 : Fin 4) : MvPolynomial (Fin 4) ℝ) = 1 := pderiv_X_self 3
  rw [h1]
  have h2 : pderiv (3 : Fin 4) (1 : MvPolynomial (Fin 4) ℝ) = 0 := by simp
  rw [h2]
  simp only [map_one, map_zero, abs_one, abs_zero]
  refine ⟨fun t _ => ⟨?_, hK1, by linarith⟩, inv_le_one_of_one_le₀ hK1⟩
  rw [p.eval_exS_X3, abs_of_nonneg hx.1]
  linarith [hx.2]

theorem eh1_last : ∀ᵐ x ∂p.stage.μ, (∀ t ∈ Set.Icc (0 : ℝ) 1,
    |MvPolynomial.eval (exS p.stage.b x.1 t) (p.stage.P)| ≤ p.stage.K ∧
    |MvPolynomial.eval (exS p.stage.b x.1 t) (MvPolynomial.pderiv (3 : Fin 4) (p.stage.P))| ≤
      p.stage.K ∧
    |MvPolynomial.eval (exS p.stage.b x.1 t) (MvPolynomial.pderiv (3 : Fin 4)
      (MvPolynomial.pderiv (3 : Fin 4) (p.stage.P)))| ≤ p.stage.K) ∧
    (p.stage.K)⁻¹ ≤ |MvPolynomial.eval (exS p.stage.b x.1 x.2)
      (MvPolynomial.pderiv (3 : Fin 4) (p.stage.P))| := by
  have hQ : MeasurableSet {x : (ℕ × (Fin 6 → ℝ)) × ℝ |
      hid p.synth.e p.synth.e₁ p.synth.G x.1.1 (x.1.2 2) ∈ Icc (0 : ℝ) 1} :=
    ((measurable_hid _ _ _).comp (measurable_fst.comp measurable_fst |>.prodMk
      ((measurable_pi_apply 2).comp (measurable_snd.comp measurable_fst)))) measurableSet_Icc
  have hae := p.synth.ae_mu_of_good
    (Q := fun x : (ℕ × (Fin 6 → ℝ)) × ℝ =>
      hid p.synth.e p.synth.e₁ p.synth.G x.1.1 (x.1.2 2) ∈ Icc (0 : ℝ) 1) hQ
    (fun q hq => p.hid_mem _ hq.2.1 hq.2.2.1)
  exact hae.mono fun x hx => p.eh1_point x.1 x.2 hx

/-- **`EH1`.** -/
theorem eh1 : EH1 p.stage := by
  have hK1 := p.one_le_sK
  have hK2 := p.two_le_sK
  have hBD := p.synth_hBD
  refine ⟨p.synth.measurable_sbS, (by show IsProbabilityMeasure p.synth.nu; infer_instance),
    (by show IsProbabilityMeasure p.synth.pal; infer_instance), ?_, le_rfl, ?_, ?_, ?_, ?_, ?_⟩
  · -- μ ≤ K • (ν × dt)
    calc p.synth.mu ≤ p.synth.nu.prod volume := p.synth.mu_le
      _ = (1 : ENNReal) • p.synth.nu.prod volume := (one_smul _ _).symm
      _ ≤ ENNReal.ofReal p.sK • p.synth.nu.prod volume := by
          refine Measure.le_iff'.2 fun s => ?_
          simp only [Measure.smul_apply, smul_eq_mul]
          gcongr
          simpa using ENNReal.ofReal_le_ofReal hK1
  · -- time support
    show p.synth.mu (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0
    rw [p.synth.mu_apply (MeasurableSet.univ.prod measurableSet_Icc).compl]
    refine measure_mono_null ?_ (measure_empty (μ := (P p.synth.M).prod volume))
    rintro ⟨ω, t⟩ ⟨hg, hc⟩
    exact hc ⟨trivial, Ico_subset_Icc_self hg.1⟩
  · -- residual mass
    show ENNReal.ofReal p.sK⁻¹ ≤ p.synth.mu univ
    refine le_trans ?_ (p.synth.mu_univ hBD)
    calc ENNReal.ofReal p.sK⁻¹ ≤ ENNReal.ofReal (1 / 2) := by
          apply ENNReal.ofReal_le_ofReal
          rw [inv_eq_one_div, div_le_div_iff₀ p.sK_pos (by norm_num)]
          linarith
      _ = 1 / 2 := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  · show (X (3 : Fin 4) : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 2
    rw [totalDegree_X]; norm_num
  · show ∀ᵐ l ∂p.synth.nu, |p.synth.sbS l 0| + |p.synth.sbS l 1| + |p.synth.sbS l 3| +
      |p.synth.sbS l 4| ≤ p.sK
    have hm : MeasurableSet {l : ℕ × (Fin 6 → ℝ) | |p.synth.sbS l 0| + |p.synth.sbS l 1| +
        |p.synth.sbS l 3| + |p.synth.sbS l 4| ≤ p.sK} := by
      have := p.synth.measurable_sbS
      exact measurableSet_le (by fun_prop) measurable_const
    rw [Synth.nu, ae_map_iff measurable_emb.aemeasurable hm]
    filter_upwards [p.ae_P_support] with ω hω
    obtain ⟨h0, h3, h1⟩ := hω
    simp only [Synth.sbS, emb]
    simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      abs_zero, add_zero]
    have hβ := p.synth.β_pos
    have hβ2 := p.synth.β_le_half
    rw [abs_of_nonneg h0.1, abs_of_nonneg h1.1, abs_of_nonneg (mul_nonneg hβ.le h3.1)]
    have : p.synth.β * ω.2.1.2 ≤ 1 := by nlinarith [h3.2]
    have := p.four_le_sK
    linarith [h0.2, h1.2]
  · exact p.eh1_last

end Par

end

end Submission.Obl.k4_finite_positive_prepared_models.Synthetic
