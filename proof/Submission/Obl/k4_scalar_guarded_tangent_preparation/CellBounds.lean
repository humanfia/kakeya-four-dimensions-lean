import Submission.Obl.k4_scalar_guarded_tangent_preparation.CeilingPacket
import Submission.Obl.k4_scalar_guarded_tangent_preparation.ReferenceLaws

/-!
# Full-prior bounds for the pieces of a true layer

For one piece `(A, C)` of a true layer at depth `r` with slack `N₀ ^ ε = H` and width
`J ≥ 1 / (H 2^T)`:
* the true floor and `C ⊆ A × I` give the full-prior lower bound
  `ν(A) ≥ N₀^{-f(r)} / (H² 2^T)`;
* a pure observation ceiling `θ` for the law `σ` bounds the `σ`-mass of the whole
  rectangle `A × I` by `θ (2H + 3) 2^{-T} (2 H J)`, so a current mass floor
  `ν(A) / (K₁ 2^T) ≤ ρ(A × I)` with `ρ ≤ σ` gives the full-prior upper bound.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open Submission.Obl.k4_scalar_linear_critical_extremizers
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction
open MeasureTheory Set
open scoped ENNReal

noncomputable section

theorem rpow_log_div_log {N H : ℝ} (hN : 1 < N) (hH : 0 < H) :
    N ^ (Real.log H / Real.log N) = H := by
  have hlogN : 0 < Real.log N := Real.log_pos hN
  rw [Real.rpow_def_of_pos (by linarith), mul_div_cancel₀ _ hlogN.ne', Real.exp_log hH]

theorem I_eq_Icc (T : ℕ) (j : Fin (2 ^ T)) :
    Split.I T j = Icc ((j : ℕ) / (2 : ℝ) ^ T) ((j : ℕ) / (2 : ℝ) ^ T + 1 / (2 : ℝ) ^ T) := by
  unfold Split.I
  congr 1
  ring

theorem volume_I (T : ℕ) (j : Fin (2 ^ T)) :
    volume (Split.I T j) = ENNReal.ofReal (1 / (2 : ℝ) ^ T) := by
  rw [I_eq_Icc, Real.volume_Icc]
  congr 1
  ring

theorem pureObservation_eq_obsL (N s : ℝ) :
    pureObservation N s = obsL (N ^ (-s)) := by
  funext z
  rfl

/-- The incidence mass of a rectangle is at most its full prior times the block length. -/
theorem mu_rect_le (p : Code) (m : ℕ) (γ : Fin (p.1 m)) (A : Set Coeff) (T : ℕ)
    (j : Fin (2 ^ T)) :
    Split.mu p m γ (A ×ˢ Split.I T j) ≤
      p.prior m γ A * ENNReal.ofReal (1 / (2 : ℝ) ^ T) := by
  calc Split.mu p m γ (A ×ˢ Split.I T j)
      ≤ ((p.prior m γ).prod volume) (A ×ˢ Split.I T j) := Measure.restrict_le_self _
    _ = p.prior m γ A * ENNReal.ofReal (1 / (2 : ℝ) ^ T) := by
        rw [Measure.prod_prod, volume_I]

/-- The full-prior lower bound of a true piece. -/
theorem prior_lower_of_floor (p : Code) (m : ℕ) (γ : Fin (p.1 m)) {A : Set Coeff}
    {C : Set Incidence} {T : ℕ} {j : Fin (2 ^ T)} {J H F : ℝ}
    (hH : 0 < H) (hF : 0 ≤ F)
    (hC : C ⊆ Split.E p m γ ∩ (A ×ˢ Split.I T j))
    (hfloor : ENNReal.ofReal (F * J / (H * (2 : ℝ) ^ T)) ≤ Split.mu p m γ C)
    (hJ : (H * (2 : ℝ) ^ T)⁻¹ ≤ J) :
    ENNReal.ofReal (F / (H ^ 2 * (2 : ℝ) ^ T)) ≤ p.prior m γ A := by
  have h2T : (0 : ℝ) < 2 ^ T := by positivity
  have hmono : Split.mu p m γ C ≤ Split.mu p m γ (A ×ˢ Split.I T j) :=
    measure_mono (fun z hz => (hC hz).2)
  have hchain := hfloor.trans (hmono.trans (mu_rect_le p m γ A T j))
  -- lower bound the floor by the target times the block length
  have hfl : ENNReal.ofReal (F / (H ^ 2 * (2 : ℝ) ^ T)) * ENNReal.ofReal (1 / (2 : ℝ) ^ T) ≤
      ENNReal.ofReal (F * J / (H * (2 : ℝ) ^ T)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hJ' : 1 / (H * 2 ^ T) ≤ J := by simpa [one_div] using hJ
    calc F / (H ^ 2 * 2 ^ T) * (1 / 2 ^ T) = F * (1 / (H * 2 ^ T)) / (H * 2 ^ T) := by
          field_simp
      _ ≤ F * J / (H * 2 ^ T) := by
          gcongr
  have hpos : ENNReal.ofReal (1 / (2 : ℝ) ^ T) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; positivity
  have htop : ENNReal.ofReal (1 / (2 : ℝ) ^ T) ≠ ⊤ := ENNReal.ofReal_ne_top
  exact (ENNReal.mul_le_mul_iff_left hpos htop).mp (hfl.trans hchain)

/-- The `σ`-mass of a fitted rectangle under a pure observation ceiling. -/
theorem rect_mass_le_of_ceiling {σ : Measure Incidence} {a θ : ℝ} (ha : 0 < a)
    (hceil : σ.map (obsL a) ≤ ENNReal.ofReal θ • (volume.prod Measure.count))
    {P : MvPolynomial (Fin 2) ℝ} (hP : P.totalDegree ≤ 2)
    {A : Set Coeff} {t₀ q u v w Λ : ℝ} (hΛ : 0 ≤ Λ) (hw : 0 ≤ w)
    (hconf : ∀ l ∈ A, ∀ t ∈ Icc t₀ (t₀ + q),
      |Split.y l t - u - t * v| ≤ w ∧
      |Split.x l t - MvPolynomial.eval ![t, Split.y l t] P| ≤ Λ * a) :
    σ (A ×ˢ Icc t₀ (t₀ + q)) ≤
      ENNReal.ofReal θ * (ENNReal.ofReal (2 * Λ + 3) * ENNReal.ofReal (q * (2 * w))) := by
  have hconf' : ∀ l ∈ A, ∀ t ∈ Icc t₀ (t₀ + q),
      |spatial l t - (u + v * t)| ≤ w ∧
      |hidden l t - MvPolynomial.eval ![t, spatial l t] P| ≤ Λ * a := by
    intro l hl t ht
    obtain ⟨hy, hx⟩ := hconf l hl t ht
    refine ⟨?_, hx⟩
    have : spatial l t - (u + v * t) = Split.y l t - u - t * v := by
      simp only [spatial, Split.y]; ring
    rw [this]; exact hy
  have hm : MeasurableSet (chartPar t₀ q u v w) := measurableSet_chartPar t₀ q u v w
  set ZF : Set (Fin 2 → ℝ) := {v' | (v' 0, v' 1) ∈ chartPar t₀ q u v w} with hZF
  have hZFm : MeasurableSet ZF := hm.preimage (by fun_prop)
  have hfm : Measurable (fun v' : Fin 2 → ℝ => MvPolynomial.eval ![v' 0, v' 1] P / a) := by
    have h' : Continuous (fun v' : Fin 2 → ℝ => MvPolynomial.eval ![v' 0, v' 1] P) := by
      have hq := (isQuad2_eval P hP).continuous
      exact hq.comp (f := fun v' : Fin 2 → ℝ => (v' 0, v' 1)) (by fun_prop)
    exact h'.measurable.div_const a
  set S : Set ((Fin 2 → ℝ) × ℤ) :=
    {x | x.1 ∈ ZF ∧ |(x.2 : ℝ) - MvPolynomial.eval ![x.1 0, x.1 1] P / a| ≤ Λ + 1} with hS
  have hSm : MeasurableSet S := by
    show MeasurableSet ((Prod.fst ⁻¹' ZF) ∩
      {x : (Fin 2 → ℝ) × ℤ | |(x.2 : ℝ) - MvPolynomial.eval ![x.1 0, x.1 1] P / a| ≤ Λ + 1})
    refine (hZFm.preimage measurable_fst).inter (measurableSet_le ?_ measurable_const)
    have h2 : Measurable (fun p : (Fin 2 → ℝ) × ℤ => ((p.2 : ℤ) : ℝ)) :=
      (measurable_from_top (f := fun k : ℤ => (k : ℝ))).comp measurable_snd
    exact (h2.sub (hfm.comp measurable_fst)).abs
  have hsub : A ×ˢ Icc t₀ (t₀ + q) ⊆ obsL a ⁻¹' S := by
    rintro ⟨l, t⟩ ⟨hl, ht⟩
    obtain ⟨hc, hx⟩ := hconf' l hl t ht
    refine ⟨?_, ?_⟩
    · show (t, spatial l t) ∈ chartPar t₀ q u v w
      exact ⟨ht, hc⟩
    · show |((⌊hidden l t / a⌋ : ℤ) : ℝ) -
          MvPolynomial.eval ![t, spatial l t] P / a| ≤ Λ + 1
      exact floor_near_of_fit ha hx
  calc σ (A ×ˢ Icc t₀ (t₀ + q)) ≤ σ (obsL a ⁻¹' S) := measure_mono hsub
    _ = (σ.map (obsL a)) S := (Measure.map_apply (measurable_obsL a) hSm).symm
    _ ≤ (ENNReal.ofReal θ • (volume.prod Measure.count)) S := hceil S
    _ = ENNReal.ofReal θ * (volume.prod Measure.count) S := rfl
    _ ≤ ENNReal.ofReal θ * (ENNReal.ofReal (2 * (Λ + 1) + 1) * volume ZF) := by
        gcongr
        exact prod_count_box_le hZFm hfm (by linarith)
    _ = ENNReal.ofReal θ * (ENNReal.ofReal (2 * Λ + 3) * volume (chartPar t₀ q u v w)) := by
        rw [hZF, volume_fin2_eq hm]
        congr 3
        ring
    _ ≤ ENNReal.ofReal θ * (ENNReal.ofReal (2 * Λ + 3) * ENNReal.ofReal (q * (2 * w))) := by
        gcongr
        exact volume_chartPar_le t₀ q u v w hw

end

end Submission.Obl.k4_scalar_guarded_tangent_preparation
