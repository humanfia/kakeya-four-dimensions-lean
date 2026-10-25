/- Adapted from this LOT tree, obligation o064, session x0214, commit a612574618456ee4cdb4d54c4cee48847fe99758,
   Submission/Lib/K4ChartLifting/SampleNormalize.lean. Original provenance is retained below. -/
import Submission.Obl.k4_raw_native_atlas_normalization.Kernel.Sizes

/-!
# The normalized problem satisfies the per-sample problem conditions

`SampleProblem`: the per-sample conditions of the frozen problem predicate. The data of the
normalized problem of an atlas (`normPrior`, `normEventOf`, `normNative`, `normScale`,
`normWeight`) and its properties: probability priors, weights, the assignment budget
`normZ ≤ 1`, native bounds almost everywhere, the lower native bound on events, and the
total selected mass.
-/
namespace Submission.Obl.k4_raw_native_atlas_normalization.Kernel
open MeasureTheory MvPolynomial

/-- The per-sample conditions of the frozen problem predicate (everything inside
`∃ M D, ∀ k, …` and the total selected mass), at one sample. -/
structure SampleProblem (N K : ℝ) (M D : ℕ) (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure Trajectory) (E : Fin W → Set Incidence)
    (P : Fin W → MvPolynomial (Fin 4) ℝ) (B : Fin W → ℝ) : Prop where
  card : (W : ℝ) ≤ N ^ M
  weight_nonneg : ∀ γ, 0 ≤ ω γ
  weight_sum : ∑ γ, ω γ = 1
  prob : ∀ γ, IsProbabilityMeasure (ν γ)
  scale_pos : ∀ γ, 0 < B γ
  scale_le : ∀ γ, B γ ≤ N ^ M
  scale_inv_le : ∀ γ, (B γ)⁻¹ ≤ N ^ M
  deg : ∀ γ, (P γ).totalDegree ≤ 2
  coeff : ∀ γ b, |(P γ).coeff b| ≤ N ^ M
  prior : ∀ γ, ∃ m : ℕ, (m : ℝ) ≤ N ^ M ∧ ∃ (c : Fin m → ℝ) (i : Fin m → ℕ)
    (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧ c j ≤ N ^ M ∧ (i j : ℝ) ≤ N ^ M ∧
      PolynomialFormat N M D (A j) ∧ (∀ x ∈ A j, ∀ b, |x b| ≤ N ^ M)) ∧
      ν γ = ∑ j, ENNReal.ofReal (c j) • Measure.map (fun x => (i j, x)) (volume.restrict (A j))
  event_meas : ∀ γ, MeasurableSet (E γ)
  event_time : ∀ γ, E γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1
  event_bdd : ∀ γ, ∀ p ∈ E γ, (p.1.1 : ℝ) ≤ N ^ M ∧ ∀ e, |p.1.2 e| ≤ N ^ M
  event_fmt : ∀ γ i, PolynomialFormat N M D
    {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ E γ}
  native : ∀ γ, ∀ᵐ l ∂ν γ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖planarPoint l t‖ + ‖velocity l‖ ≤ K ∧ |eval (graphPoint l t) (P γ)| ≤ K ∧
    |eval (graphPoint l t) (pderiv (3 : Fin 4) (P γ))| ≤ K * B γ ∧
    |eval (graphPoint l t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (P γ)))| ≤ K * B γ ^ 2
  lower : ∀ γ, ∀ᵐ p ∂(((ν γ).prod volume).restrict (E γ)),
    B γ / K ≤ |eval (graphPoint p.1 p.2) (pderiv (3 : Fin 4) (P γ))|
  mass : ENNReal.ofReal K⁻¹ ≤ ∑ γ, ENNReal.ofReal (ω γ) * ((ν γ).prod volume) (E γ)


namespace ChartSystem

variable {W T₀ : ℕ} (s : ChartSystem W T₀)

/-- The normalizing constant of the world weights of the normalized problem. -/
noncomputable def normZ (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory) : ℝ :=
  ∑ c, ω (s.world c) * ((ν (s.world c) (s.assignment c)).toReal / (2 : ℝ) ^ T₀)

/-- World weights of the normalized problem: `∝ ω q ν(A_c)`. -/
noncomputable def normWeight (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
    (c : Fin s.count) : ℝ :=
  ω (s.world c) * ((ν (s.world c) (s.assignment c)).toReal / (2 : ℝ) ^ T₀) / s.normZ ω ν

/-- Priors of the normalized problem. -/
noncomputable def normPrior (ν : Fin W → Measure Trajectory) (c : Fin s.count) :
    Measure Trajectory :=
  (ν (s.world c) (s.assignment c))⁻¹ •
    Measure.map (s.frameOf c).normTraj ((ν (s.world c)).restrict (s.assignment c))

/-- Events of the normalized problem: the normalized selected incidences of each chart. -/
def normEventOf (c : Fin s.count) : Set Incidence :=
  (s.frameOf c).normEvent (s.assignment c) (s.event c)

/-- Native tests of the normalized problem: `P_c / δ`. -/
noncomputable def normNative (δ : ℝ) (c : Fin s.count) : MvPolynomial (Fin 4) ℝ :=
  (s.frameOf c).normTest δ (s.test c)

/-- Derivative scales of the normalized problem: `B / δ`. -/
noncomputable def normScale (B : Fin W → ℝ) (δ : ℝ) (c : Fin s.count) : ℝ :=
  B (s.world c) / δ

theorem normWeight_nonneg (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
    (hω : ∀ γ, 0 ≤ ω γ) (c : Fin s.count) : 0 ≤ s.normWeight ω ν c := by
  unfold normWeight
  have hZ : 0 ≤ s.normZ ω ν := Finset.sum_nonneg fun c _ => mul_nonneg (hω _) (by positivity)
  exact div_nonneg (mul_nonneg (hω _) (by positivity)) hZ

theorem normWeight_sum (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
    (hZ : 0 < s.normZ ω ν) : ∑ c, s.normWeight ω ν c = 1 := by
  unfold normWeight
  rw [← Finset.sum_div]
  exact div_self hZ.ne'

theorem normPrior_isProbability (ν : Fin W → Measure Trajectory) [∀ γ, IsFiniteMeasure (ν γ)]
    (c : Fin s.count) (hpos : ν (s.world c) (s.assignment c) ≠ 0) :
    IsProbabilityMeasure (s.normPrior ν c) := by
  constructor
  rw [normPrior, Measure.smul_apply, Measure.map_apply (measurable_normTraj _)
    MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos (measure_ne_top _ _)


theorem denormTraj_normTraj' (c : Fin s.count) (hD : IsUnit (s.frame c).det) (l : Trajectory) :
    (s.frameOf c).denormTraj ((s.frameOf c).normTraj l) = l :=
  (s.frameOf c).denormTraj_normTraj (s.frameOf_q_pos c).ne' hD l

theorem normTraj_denormTraj (c : Fin s.count) (hD : IsUnit (s.frame c).det) (l : Trajectory) :
    (s.frameOf c).normTraj ((s.frameOf c).denormTraj l) = l := by
  simp [Frame.normTraj, Frame.denormTraj,
    (s.frameOf c).normCoeff_denormCoeff (s.frameOf_q_pos c).ne' hD]

/-- Almost every normalized trajectory comes from the chart's assignment. -/
theorem ae_normPrior_mem (ν : Fin W → Measure Trajectory) (c : Fin s.count)
    (hD : IsUnit (s.frame c).det) (hA : MeasurableSet (s.assignment c)) :
    ∀ᵐ l ∂(s.normPrior ν c), (s.frameOf c).denormTraj l ∈ s.assignment c := by
  unfold normPrior
  refine Measure.ae_smul_measure ?_ _
  have hm : MeasurableSet {l : Trajectory | (s.frameOf c).denormTraj l ∈ s.assignment c} :=
    (s.frameOf c).measurable_denormTraj hA
  rw [ae_map_iff (measurable_normTraj _).aemeasurable hm]
  refine (ae_restrict_mem hA).mono fun l hl => ?_
  show (s.frameOf c).denormTraj ((s.frameOf c).normTraj l) ∈ s.assignment c
  rw [s.denormTraj_normTraj' c hD]; exact hl


/-- Native bounds of the normalized problem, almost everywhere for its prior. -/
theorem normPrior_native (ν : Fin W → Measure Trajectory) (c : Fin s.count)
    (hD : IsUnit (s.frame c).det) (hA : MeasurableSet (s.assignment c)) {κ δ B : ℝ}
    (hκ : 0 ≤ κ) (hδ : 0 < δ) (hB : 0 ≤ B)
    (hchart : ∀ l ∈ s.assignment c, ∀ t ∈ timeBlock T₀ (s.block c),
      ‖Matrix.toEuclideanLin ((s.frame c)⁻¹) (planarPoint l t - s.center c - t • s.speed c)‖ ≤ κ ∧
      |MvPolynomial.eval (graphPoint l t) (s.test c)| ≤ κ * δ ∧
      |MvPolynomial.eval (graphPoint l t) (MvPolynomial.pderiv (3 : Fin 4) (s.test c))| ≤ κ * B ∧
      |MvPolynomial.eval (graphPoint l t)
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (s.test c)))| ≤
        κ * B ^ 2 / δ) :
    ∀ᵐ l ∂(s.normPrior ν c), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖planarPoint l τ‖ + ‖velocity l‖ ≤ 3 * κ ∧
      |eval (graphPoint l τ) (s.normNative δ c)| ≤ 3 * κ ∧
      |eval (graphPoint l τ) (pderiv (3 : Fin 4) (s.normNative δ c))| ≤ 3 * κ * (B / δ) ∧
      |eval (graphPoint l τ) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (s.normNative δ c)))| ≤
        3 * κ * (B / δ) ^ 2 := by
  refine (s.ae_normPrior_mem ν c hD hA).mono fun l hl τ hτ => ?_
  have hl' : (s.frameOf c).normTraj ((s.frameOf c).denormTraj l) = l := s.normTraj_denormTraj c hD l
  obtain ⟨h1, h2, h3, h4⟩ := s.norm_native_bounds c hδ hD hchart _ hl τ hτ
  rw [hl'] at h1 h2 h3 h4
  have hB2 : 0 ≤ (B / δ) ^ 2 := sq_nonneg _
  refine ⟨h1, h2.trans (by linarith), h3.trans ?_, h4.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hB hδ.le)
  · exact mul_le_mul_of_nonneg_right (by linarith) hB2


/-- The lower native bound of the normalized problem on its events. -/
theorem normEvent_lower (ν : Fin W → Measure Trajectory) [∀ γ, IsFiniteMeasure (ν γ)]
    (c : Fin s.count) (hA : MeasurableSet (s.assignment c)) (hF : MeasurableSet (s.event c))
    {κ δ B : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) (hB : 0 ≤ B)
    (hev : ∀ p ∈ s.event c, B / κ ≤
      |MvPolynomial.eval (graphPoint p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (s.test c))|) :
    ∀ᵐ p ∂(((s.normPrior ν c).prod volume).restrict (s.normEventOf c)),
      B / δ / (3 * κ) ≤ |eval (graphPoint p.1 p.2) (pderiv (3 : Fin 4) (s.normNative δ c))| := by
  refine ae_restrict_of_forall_mem ((s.frameOf c).measurableSet_normEvent hA hF) ?_
  intro p hp
  have h3 : ((s.frameOf c).denormTraj p.1, (s.frameOf c).t₀ + (s.frameOf c).q * p.2) ∈
      s.event c := hp.2.2
  have hb := hev _ h3
  dsimp only at hb
  have h := (s.frameOf c).normTest_lower (s.frameOf_q_pos c).ne' hδ (s.test c) p.1 p.2 hb
  have hle : B / δ / (3 * κ) ≤ B / δ / κ :=
    div_le_div_of_nonneg_left (div_nonneg hB hδ.le) hκ (by linarith)
  exact hle.trans h

/-- The assignment budget of an atlas: `Σ_c ω q ν(A_c) ≤ 1`. -/
theorem normZ_le_one (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
    [∀ γ, IsProbabilityMeasure (ν γ)] (hω : ∀ γ, 0 ≤ ω γ) (hωs : ∑ γ, ω γ = 1)
    (hA : ∀ c, MeasurableSet (s.assignment c))
    (hdisj : ∀ b b', b ≠ b' → s.world b = s.world b' → s.block b = s.block b' →
      Disjoint (s.assignment b) (s.assignment b')) :
    s.normZ ω ν ≤ 1 := by
  classical
  have hgroup : ∀ (γ : Fin W) (j : Fin (2 ^ T₀)),
      ∑ c ∈ Finset.univ.filter (fun c => s.world c = γ ∧ s.block c = j),
        (ν γ (s.assignment c)).toReal ≤ 1 := by
    intro γ j
    set I := Finset.univ.filter (fun c => s.world c = γ ∧ s.block c = j)
    have hpair : (↑I : Set (Fin s.count)).PairwiseDisjoint s.assignment := by
      intro b hb b' hb' hbb'
      have hb0 := (Finset.mem_filter.mp hb).2
      have hb1 := (Finset.mem_filter.mp hb').2
      exact hdisj b b' hbb' (hb0.1.trans hb1.1.symm) (hb0.2.trans hb1.2.symm)
    rw [← ENNReal.toReal_sum (fun c _ => measure_ne_top _ _),
      ← measure_biUnion_finset hpair (fun c _ => hA c)]
    calc (ν γ (⋃ c ∈ I, s.assignment c)).toReal ≤ (ν γ Set.univ).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))
      _ = 1 := by rw [measure_univ]; rfl
  have hq : (0 : ℝ) < (2 : ℝ) ^ T₀ := by positivity
  unfold normZ
  calc ∑ c, ω (s.world c) * ((ν (s.world c) (s.assignment c)).toReal / (2 : ℝ) ^ T₀)
      = ∑ γ, ∑ j : Fin (2 ^ T₀), ∑ c ∈ Finset.univ.filter
          (fun c => s.world c = γ ∧ s.block c = j),
          ω (s.world c) * ((ν (s.world c) (s.assignment c)).toReal / (2 : ℝ) ^ T₀) := by
        simpa only [Fintype.sum_prod_type, Prod.mk.injEq] using
          (Finset.sum_fiberwise Finset.univ (fun c => (s.world c, s.block c))
            (fun c => ω (s.world c) *
              ((ν (s.world c) (s.assignment c)).toReal / (2 : ℝ) ^ T₀))).symm
    _ ≤ ∑ γ, ∑ _j : Fin (2 ^ T₀), ω γ / (2 : ℝ) ^ T₀ := by
        apply Finset.sum_le_sum; intro γ _
        apply Finset.sum_le_sum; intro j _
        calc ∑ c ∈ Finset.univ.filter (fun c => s.world c = γ ∧ s.block c = j),
              ω (s.world c) * ((ν (s.world c) (s.assignment c)).toReal / (2 : ℝ) ^ T₀)
            = ω γ / (2 : ℝ) ^ T₀ * ∑ c ∈ Finset.univ.filter
                (fun c => s.world c = γ ∧ s.block c = j), (ν γ (s.assignment c)).toReal := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro c hc
              rw [(Finset.mem_filter.mp hc).2.1]; ring
          _ ≤ ω γ / (2 : ℝ) ^ T₀ * 1 :=
              mul_le_mul_of_nonneg_left (hgroup γ j) (div_nonneg (hω γ) hq.le)
          _ = ω γ / (2 : ℝ) ^ T₀ := mul_one _
    _ = 1 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have : ∀ γ, ((2 ^ T₀ : ℕ) : ℝ) * (ω γ / (2 : ℝ) ^ T₀) = ω γ := by
          intro γ; push_cast; field_simp
        simp only [this, hωs]


/-- Per chart: normalized weight times normalized event mass is the original weighted
selected mass divided by `Z`. -/
theorem normWeight_mul_mass (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
    [∀ γ, IsFiniteMeasure (ν γ)] (hω : ∀ γ, 0 ≤ ω γ) (hZ : 0 < s.normZ ω ν) (c : Fin s.count)
    (hD : IsUnit (s.frame c).det) (hA : MeasurableSet (s.assignment c))
    (hF : MeasurableSet (s.event c))
    (hsub : ∀ p ∈ s.event c, p.1 ∈ s.assignment c ∧ p.2 ∈ timeBlock T₀ (s.block c)) :
    ENNReal.ofReal (s.normWeight ω ν c) * ((s.normPrior ν c).prod volume) (s.normEventOf c) =
      ENNReal.ofReal (s.normZ ω ν)⁻¹ *
        (ENNReal.ofReal (ω (s.world c)) * ((ν (s.world c)).prod volume) (s.event c)) := by
  have hq := s.frameOf_q_pos c
  have hsub' : ∀ p ∈ s.event c, p.1 ∈ s.assignment c ∧
      p.2 ∈ Set.Icc (s.frameOf c).t₀ ((s.frameOf c).t₀ + (s.frameOf c).q) := by
    intro p hp
    obtain ⟨h1, h2⟩ := hsub p hp
    exact ⟨h1, (s.timeBlock_frameOf c) ▸ h2⟩
  rw [(s.frameOf c).prod_normEvent hq hD (ν (s.world c)) hA hF hsub']
  set X := ((Measure.map (s.frameOf c).normTraj ((ν (s.world c)).restrict (s.assignment c))).prod
    volume) (s.normEventOf c)
  have hX : ((s.normPrior ν c).prod volume) (s.normEventOf c) =
      (ν (s.world c) (s.assignment c))⁻¹ * X := by
    rw [normPrior, Measure.prod_smul_left, Measure.smul_apply, smul_eq_mul]
  rw [hX]
  set νA := ν (s.world c) (s.assignment c)
  have hq' : (s.frameOf c).q = 1 / (2 : ℝ) ^ T₀ := rfl
  by_cases h0 : νA = 0
  · have hres : (ν (s.world c)).restrict (s.assignment c) = 0 := Measure.restrict_eq_zero.mpr h0
    have hX0 : X = 0 := by
      show ((Measure.map (s.frameOf c).normTraj ((ν (s.world c)).restrict (s.assignment c))).prod
        volume) (s.normEventOf c) = 0
      rw [hres]; simp
    rw [hX0, mul_zero, mul_zero]
    symm
    simp only [mul_eq_zero]
    right; right; right
    exact hX0
  · have hνA : ENNReal.ofReal νA.toReal = νA := ENNReal.ofReal_toReal (measure_ne_top _ _)
    have hZi : 0 ≤ (s.normZ ω ν)⁻¹ := inv_nonneg.mpr hZ.le
    have hw : s.normWeight ω ν c = ω (s.world c) * (s.frameOf c).q * (s.normZ ω ν)⁻¹ * νA.toReal := by
      unfold normWeight; rw [hq']; field_simp; rfl
    have e1 : ENNReal.ofReal (s.normWeight ω ν c) = ENNReal.ofReal (ω (s.world c)) *
        ENNReal.ofReal (s.frameOf c).q * ENNReal.ofReal (s.normZ ω ν)⁻¹ * νA := by
      rw [hw, ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (hω _) hq.le) hZi),
        ENNReal.ofReal_mul (mul_nonneg (hω _) hq.le), ENNReal.ofReal_mul (hω _), hνA]
    rw [e1]
    have e2 : νA * νA⁻¹ = 1 := ENNReal.mul_inv_cancel h0 (measure_ne_top _ _)
    calc ENNReal.ofReal (ω (s.world c)) * ENNReal.ofReal (s.frameOf c).q *
          ENNReal.ofReal (s.normZ ω ν)⁻¹ * νA * (νA⁻¹ * X)
        = ENNReal.ofReal (s.normZ ω ν)⁻¹ * (ENNReal.ofReal (ω (s.world c)) *
            (ENNReal.ofReal (s.frameOf c).q * X)) * (νA * νA⁻¹) := by ring
      _ = _ := by rw [e2, mul_one]; rfl

/-- Total selected mass of the normalized problem. -/
theorem normMass (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
    [∀ γ, IsProbabilityMeasure (ν γ)] (hω : ∀ γ, 0 ≤ ω γ) (hωs : ∑ γ, ω γ = 1)
    (hZ : 0 < s.normZ ω ν) (hD : ∀ c, IsUnit (s.frame c).det)
    (hA : ∀ c, MeasurableSet (s.assignment c)) (hF : ∀ c, MeasurableSet (s.event c))
    (hdisj : ∀ b b', b ≠ b' → s.world b = s.world b' → s.block b = s.block b' →
      Disjoint (s.assignment b) (s.assignment b'))
    (hsub : ∀ c, ∀ p ∈ s.event c, p.1 ∈ s.assignment c ∧ p.2 ∈ timeBlock T₀ (s.block c))
    {κ : ℝ}
    (htotal : ENNReal.ofReal κ⁻¹ ≤
      ∑ c, ENNReal.ofReal (ω (s.world c)) * ((ν (s.world c)).prod volume) (s.event c)) :
    ENNReal.ofReal κ⁻¹ ≤
      ∑ c, ENNReal.ofReal (s.normWeight ω ν c) * ((s.normPrior ν c).prod volume)
        (s.normEventOf c) := by
  rw [Finset.sum_congr rfl (fun c _ => s.normWeight_mul_mass ω ν hω hZ c (hD c) (hA c) (hF c)
    (hsub c)), ← Finset.mul_sum]
  have hZ1 := s.normZ_le_one ω ν hω hωs hA hdisj
  have hinv : 1 ≤ ENNReal.ofReal (s.normZ ω ν)⁻¹ := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    rw [one_le_inv₀ hZ]; exact hZ1
  calc ENNReal.ofReal κ⁻¹ = 1 * ENNReal.ofReal κ⁻¹ := (one_mul _).symm
    _ ≤ _ := mul_le_mul' hinv htotal

end ChartSystem
end Submission.Obl.k4_raw_native_atlas_normalization.Kernel
