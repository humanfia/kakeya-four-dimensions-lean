import Submission.Obl.k4_scalar_candidate_original_return.Core.ListedBasic
import Submission.Obl.k4_scalar_candidate_original_return.Core.LayerMass
import Submission.Obl.k4_scalar_candidate_original_return.Extraction
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Basic

/-!
# The listed original success at one stage

Planks of one world are almost disjoint, old terminal lists hold almost everywhere on each
plank, each plank's listed success misses its covered mass by at most its separated-pair mass,
and the weighted separated-pair masses are negligible against the layer coverage.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Filter Set MvPolynomial

namespace PreparedData

variable {a : PreparedData} (ha : a.Valid) (π : CmpParams) (k : ℕ)
include ha

/-- Planks of one world of a layer meet in a ρ-null set. -/
theorem lm_plank_inter_null (ℓ : Fin (a.ct k)) (i i' : Fin (a.ls k ℓ).n) (hne : i ≠ i')
    (hw : (a.ls k ℓ).world i = (a.ls k ℓ).world i') :
    a.ρ k ((a.ls k ℓ).world i) (a.plank k ℓ i ∩ a.plank k ℓ i') = 0 := by
  have hCD := (ha.layer k ℓ).2.2.1
  let F : Fin (a.ls k ℓ).n → Set Inc := fun i =>
    (a.ls k ℓ).prior i ×ˢ I (a.ls k ℓ).T ((a.ls k ℓ).time i)
  have hpair := k4_scalar_true_atlas_terminal_lists.assigned_incidence_inter_null (ha.exact k)
    (a.ls k ℓ).world (a.ls k ℓ).time (a.ls k ℓ).prior F hCD.2.2.2.1 (fun _ => subset_rfl)
  apply le_antisymm _ bot_le
  calc a.ρ k ((a.ls k ℓ).world i) (a.plank k ℓ i ∩ a.plank k ℓ i')
      ≤ mu (a.p k) (a.sm k) ((a.ls k ℓ).world i) (F i ∩ F i') := ha.rho_le k _ _
    _ = 0 := hpair i i' hne hw


/-- Old terminal lists hold almost everywhere on each plank. -/
theorem lm_plank_list_ae (ℓ : Fin (a.ct k)) (i : Fin (a.ls k ℓ).n) :
    a.ρ k ((a.ls k ℓ).world i)
      (a.plank k ℓ i \ {z | i ∈ (a.ls k ℓ).lists ((a.ls k ℓ).world i) (a.obs k z)}) = 0 := by
  classical
  set g := (a.ls k ℓ).world i with hg
  have hTK : a.ρ k g {z : Inc | ¬∃ i', (a.ls k ℓ).world i' = g ∧ z.1 ∈ (a.ls k ℓ).prior i' ∧
      z.2 ∈ I (a.ls k ℓ).T ((a.ls k ℓ).time i') ∧ i' ∈ (a.ls k ℓ).lists g (a.obs k z)} = 0 :=
    (ha.tangentData_terminalKnown).2.2.2.2 k ℓ g
  have hpairs : a.ρ k g (⋃ i' : Fin (a.ls k ℓ).n,
      {z | i' ≠ i ∧ (a.ls k ℓ).world i' = g ∧ z ∈ a.plank k ℓ i ∩ a.plank k ℓ i'}) = 0 := by
    apply measure_iUnion_null
    intro i'
    by_cases hc : i' ≠ i ∧ (a.ls k ℓ).world i' = g
    · apply measure_mono_null (fun z hz => hz.2.2)
      have := lm_plank_inter_null ha k ℓ i i' (Ne.symm hc.1) (hc.2.symm)
      simpa only [hg] using this
    · have hempty : {z : Inc | i' ≠ i ∧ (a.ls k ℓ).world i' = g ∧
          z ∈ a.plank k ℓ i ∩ a.plank k ℓ i'} = ∅ := by
        ext z
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        intro hz
        exact hc ⟨hz.1, hz.2.1⟩
      rw [hempty, measure_empty]
  apply measure_mono_null _ (measure_union_null hTK hpairs)
  rintro z ⟨hzP, hzL⟩
  by_cases hbad : ∃ i', (a.ls k ℓ).world i' = g ∧ z.1 ∈ (a.ls k ℓ).prior i' ∧
      z.2 ∈ I (a.ls k ℓ).T ((a.ls k ℓ).time i') ∧ i' ∈ (a.ls k ℓ).lists g (a.obs k z)
  · right
    obtain ⟨i', hw, h1, h2, hl⟩ := hbad
    have hne : i' ≠ i := by
      rintro rfl
      exact hzL hl
    exact mem_iUnion.mpr ⟨i', hne, hw, hzP, ⟨h1, h2⟩⟩
  · left
    exact hbad

/-- Each plank's separated-pair mass is a small multiple of its prior mass. -/
theorem lm_farMass_le_prior (ℓ : Fin (a.ct k)) (s : ℝ) (i : Fin (a.ls k ℓ).n)
    (hP : a.PlankHyp π k ℓ i s) (hM : MatchAt (a.tangent k ^ π.σ.c₀) π.εm a.rd) :
    MatchApply.farMass (a.Gz π k ℓ i) (a.pairW π k ℓ i) (a.jetStep π k) ≤
      ENNReal.ofReal (1000 * a.rK k ^ 4 *
        a.tangent k ^ (2 * π.θ * π.σ.c₀ - π.εm * π.σ.c₀ + π.θ * π.σ.c₀ / 4) /
          (2 : ℝ) ^ (a.ls k ℓ).T) *
        ν (a.p k) (a.sm k) ((a.ls k ℓ).world i) ((a.ls k ℓ).prior i) := by
  have hfm := plank_farMass_le ha π k ℓ i s hP hM
  have hN : 2 ≤ a.tangent k := hP.N_ge
  have hNpos : 0 < a.tangent k := by linarith
  have hN1 : 1 ≤ a.tangent k := by linarith
  have hK : 1 ≤ a.rK k := hP.K_ge
  have hKpos : 0 < a.rK k := by linarith
  have hT : (0 : ℝ) < (2 : ℝ) ^ (a.ls k ℓ).T := by positivity
  obtain ⟨hd0, hd1⟩ := hP.d_range
  obtain ⟨hsθ, _⟩ := hP.s_win
  obtain ⟨hs₀, hc₀, hθ, hθε, hε, hε1⟩ := hP.par_pos
  refine hfm.trans ?_
  refine le_trans ?_ (mul_le_mul' le_rfl hP.nu_lower)
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  -- real inequality
  have hexp : -a.rd * π.σ.s₀ + 2 * π.θ * π.σ.c₀ - π.εm * π.σ.c₀ ≤
      (2 * π.θ * π.σ.c₀ - π.εm * π.σ.c₀ + π.θ * π.σ.c₀ / 4) + (-a.rd * s) := by
    have h1 : a.rd * (s - π.σ.s₀) ≤ π.θ * π.σ.c₀ / 4 := by
      calc a.rd * (s - π.σ.s₀) ≤ a.rd * |s - π.σ.s₀| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hd0
        _ ≤ 1 * |s - π.σ.s₀| := mul_le_mul_of_nonneg_right hd1.le (abs_nonneg _)
        _ ≤ π.θ * π.σ.c₀ / 4 := by linarith
    nlinarith
  have hpow : a.tangent k ^ (-a.rd * π.σ.s₀ + 2 * π.θ * π.σ.c₀ - π.εm * π.σ.c₀) ≤
      a.tangent k ^ (2 * π.θ * π.σ.c₀ - π.εm * π.σ.c₀ + π.θ * π.σ.c₀ / 4) *
        a.tangent k ^ (-a.rd * s) := by
    rw [← Real.rpow_add hNpos]
    exact Real.rpow_le_rpow_of_exponent_le hN1 hexp
  have h2T : (2 : ℝ) ^ (2 * (a.ls k ℓ).T) = (2 : ℝ) ^ (a.ls k ℓ).T * (2 : ℝ) ^ (a.ls k ℓ).T := by
    rw [two_mul, pow_add]
  rw [h2T]
  have hA := Real.rpow_pos_of_pos hNpos (2 * π.θ * π.σ.c₀ - π.εm * π.σ.c₀ + π.θ * π.σ.c₀ / 4)
  have hB := Real.rpow_pos_of_pos hNpos (-a.rd * s)
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  have hK3 : 0 ≤ a.rK k ^ 3 := by positivity
  calc 1000 * a.rK k ^ 3 * a.tangent k ^ (-a.rd * π.σ.s₀ + 2 * π.θ * π.σ.c₀ - π.εm * π.σ.c₀) *
        ((2 : ℝ) ^ (a.ls k ℓ).T * (a.rK k * (2 : ℝ) ^ (a.ls k ℓ).T))
      ≤ 1000 * a.rK k ^ 3 * (a.tangent k ^ (2 * π.θ * π.σ.c₀ - π.εm * π.σ.c₀ +
          π.θ * π.σ.c₀ / 4) * a.tangent k ^ (-a.rd * s)) *
        ((2 : ℝ) ^ (a.ls k ℓ).T * (a.rK k * (2 : ℝ) ^ (a.ls k ℓ).T)) := by
        gcongr
    _ = 1000 * a.rK k ^ 4 * a.tangent k ^ (2 * π.θ * π.σ.c₀ - π.εm * π.σ.c₀ +
          π.θ * π.σ.c₀ / 4) * a.tangent k ^ (-a.rd * s) *
        ((2 : ℝ) ^ (a.ls k ℓ).T * (2 : ℝ) ^ (a.ls k ℓ).T) := by ring

/-- The numerical smallness of the separated-pair budget. -/
theorem lm_budget_le (ℓ : Fin (a.ct k)) (s : ℝ) (i : Fin (a.ls k ℓ).n)
    (hP : a.PlankHyp π k ℓ i s) {C : ℝ} (hC : 1 ≤ C)
    (hCN : 4000 * C ≤ a.tangent k ^ (π.θ * π.σ.c₀)) :
    1000 * a.rK k ^ 4 * a.tangent k ^ (2 * π.θ * π.σ.c₀ - π.εm * π.σ.c₀ + π.θ * π.σ.c₀ / 4) ≤
      (2 * C * a.H k ^ 2)⁻¹ := by
  have hN : 2 ≤ a.tangent k := hP.N_ge
  have hNpos : 0 < a.tangent k := by linarith
  have hN1 : 1 ≤ a.tangent k := by linarith
  have hK : 1 ≤ a.rK k := hP.K_ge
  have hH : 2 ≤ a.H k := hP.H_ge
  have hKs := hP.K_small
  have hHs := hP.H_small
  obtain ⟨hs₀, hc₀, hθ, hθε, hε, hε1⟩ := hP.par_pos
  set κ0 := kap0 π with hκ0
  have hκ0v : κ0 = π.θ * π.σ.c₀ / 1000 := rfl
  set e₂ := 2 * π.θ * π.σ.c₀ - π.εm * π.σ.c₀ + π.θ * π.σ.c₀ / 4 with he₂
  have hpos : 0 < 2 * C * a.H k ^ 2 := by positivity
  rw [show (2 * C * a.H k ^ 2)⁻¹ = 1 / (2 * C * a.H k ^ 2) by rw [one_div],
    le_div_iff₀ hpos]
  have hK4 : a.rK k ^ 4 ≤ a.tangent k ^ (κ0 * 4) := by
    calc a.rK k ^ 4 ≤ (a.tangent k ^ κ0) ^ 4 := pow_le_pow_left₀ (by linarith) hKs 4
      _ = a.tangent k ^ (κ0 * 4) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
        norm_num
  have hH2 : a.H k ^ 2 ≤ a.tangent k ^ (κ0 * 2) := by
    calc a.H k ^ 2 ≤ (a.tangent k ^ κ0) ^ 2 := pow_le_pow_left₀ (by linarith) hHs 2
      _ = a.tangent k ^ (κ0 * 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
        norm_num
  have hC2 : 2000 * C ≤ a.tangent k ^ (π.θ * π.σ.c₀) := by linarith
  have hexp : π.θ * π.σ.c₀ + κ0 * 4 + κ0 * 2 + e₂ ≤ 0 := by
    rw [hκ0v, he₂]
    have : π.εm * π.σ.c₀ ≥ 16 * π.θ * π.σ.c₀ := by nlinarith
    nlinarith
  have hE := Real.rpow_pos_of_pos hNpos e₂
  calc 1000 * a.rK k ^ 4 * a.tangent k ^ e₂ * (2 * C * a.H k ^ 2)
      = (2000 * C) * a.rK k ^ 4 * a.H k ^ 2 * a.tangent k ^ e₂ := by ring
    _ ≤ a.tangent k ^ (π.θ * π.σ.c₀) * a.tangent k ^ (κ0 * 4) * a.tangent k ^ (κ0 * 2) *
          a.tangent k ^ e₂ := by
        gcongr
    _ = a.tangent k ^ (π.θ * π.σ.c₀ + κ0 * 4 + κ0 * 2 + e₂) := by
        rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 hexp

/-- The weighted separated-pair masses of a layer are below half the coverage floor. -/
theorem lm_weighted_farMass_le (ℓ : Fin (a.ct k)) (s : ℝ) (hP : ∀ i, a.PlankHyp π k ℓ i s)
    (hM : MatchAt (a.tangent k ^ π.σ.c₀) π.εm a.rd) {C : ℝ} (hC : 1 ≤ C)
    (hCN : 4000 * C ≤ a.tangent k ^ (π.θ * π.σ.c₀)) :
    ∑ i : Fin (a.ls k ℓ).n, ENNReal.ofReal (ω (a.p k) (a.sm k) ((a.ls k ℓ).world i)) *
        MatchApply.farMass (a.Gz π k ℓ i) (a.pairW π k ℓ i) (a.jetStep π k) ≤
      ENNReal.ofReal ((2 * C * a.H k ^ 2)⁻¹) := by
  by_cases hn : (a.ls k ℓ).n = 0
  · have hempty : (Finset.univ : Finset (Fin (a.ls k ℓ).n)) = ∅ := by
      rw [Finset.univ_eq_empty_iff]
      rw [hn]
      infer_instance
    rw [hempty, Finset.sum_empty]
    exact bot_le
  let i₀ : Fin (a.ls k ℓ).n := ⟨0, Nat.pos_of_ne_zero hn⟩
  set y : ℝ := 1000 * a.rK k ^ 4 *
    a.tangent k ^ (2 * π.θ * π.σ.c₀ - π.εm * π.σ.c₀ + π.θ * π.σ.c₀ / 4) with hy
  have hy0 : 0 ≤ y := by
    have : 0 ≤ a.rK k := by linarith [(hP i₀).K_ge]
    have : 0 < a.tangent k := by linarith [(hP i₀).N_ge]
    positivity
  have hT : (0 : ℝ) < (2 : ℝ) ^ (a.ls k ℓ).T := by positivity
  calc ∑ i : Fin (a.ls k ℓ).n, ENNReal.ofReal (ω (a.p k) (a.sm k) ((a.ls k ℓ).world i)) *
        MatchApply.farMass (a.Gz π k ℓ i) (a.pairW π k ℓ i) (a.jetStep π k)
      ≤ ∑ i : Fin (a.ls k ℓ).n, ENNReal.ofReal (ω (a.p k) (a.sm k) ((a.ls k ℓ).world i)) *
        (ENNReal.ofReal (y / (2 : ℝ) ^ (a.ls k ℓ).T) *
          ν (a.p k) (a.sm k) ((a.ls k ℓ).world i) ((a.ls k ℓ).prior i)) := by
        gcongr with i
        exact lm_farMass_le_prior ha π k ℓ s i (hP i) hM
    _ = ENNReal.ofReal (y / (2 : ℝ) ^ (a.ls k ℓ).T) *
        ∑ i : Fin (a.ls k ℓ).n, ENNReal.ofReal (ω (a.p k) (a.sm k) ((a.ls k ℓ).world i)) *
          ν (a.p k) (a.sm k) ((a.ls k ℓ).world i) ((a.ls k ℓ).prior i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ ≤ ENNReal.ofReal (y / (2 : ℝ) ^ (a.ls k ℓ).T) * (2 : ENNReal) ^ (a.ls k ℓ).T := by
        gcongr
        exact layer_weighted_prior_le ha k ℓ
    _ = ENNReal.ofReal y := by
        have h2 : (2 : ENNReal) ^ (a.ls k ℓ).T = ENNReal.ofReal ((2 : ℝ) ^ (a.ls k ℓ).T) := by
          rw [ENNReal.ofReal_pow (by norm_num)]
          norm_num
        rw [h2, ← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ hT.ne']
    _ ≤ ENNReal.ofReal ((2 * C * a.H k ^ 2)⁻¹) :=
        ENNReal.ofReal_le_ofReal (lm_budget_le ha π k ℓ s i₀ (hP i₀) hC hCN)

/-- In one world, the layer coverage is listed except for the separated-pair masses. -/
theorem lm_world_bound (ℓ : Fin (a.ct k)) (s : ℝ) (hP : ∀ i, a.PlankHyp π k ℓ i s)
    (g : Fin (a.Wk k)) :
    a.ρ k g (a.layerCoverage π.θ π.σ k ℓ g) ≤
      a.ρ k g {z | ∃ j, (a.ls k ℓ).world (a.parentOf π k ℓ j) = g ∧
          z.1 ∈ {l | ∃ i h, a.binOf π k ℓ i h = j ∧ l ∈ a.asg π k ℓ i h} ∧
          z.2 ∈ I (a.ls k ℓ).T ((a.ls k ℓ).time (a.parentOf π k ℓ j)) ∧
          j ∈ a.listsOf π k ℓ g (a.obs k z)} +
      ∑ i ∈ Finset.univ.filter (fun i : Fin (a.ls k ℓ).n => (a.ls k ℓ).world i = g),
        MatchApply.farMass (a.Gz π k ℓ i) (a.pairW π k ℓ i) (a.jetStep π k) := by
  classical
  set F := Finset.univ.filter (fun i : Fin (a.ls k ℓ).n => (a.ls k ℓ).world i = g) with hF
  set Tg := {z : Inc | ∃ j, (a.ls k ℓ).world (a.parentOf π k ℓ j) = g ∧
          z.1 ∈ {l | ∃ i h, a.binOf π k ℓ i h = j ∧ l ∈ a.asg π k ℓ i h} ∧
          z.2 ∈ I (a.ls k ℓ).T ((a.ls k ℓ).time (a.parentOf π k ℓ j)) ∧
          j ∈ a.listsOf π k ℓ g (a.obs k z)} with hTg
  let S : Fin (a.ls k ℓ).n → Set Inc := fun i => a.succSet π k ℓ i (a.bstarOf π k ℓ i)
  let L : Fin (a.ls k ℓ).n → Set Inc := fun i => {z | i ∈ (a.ls k ℓ).lists g (a.obs k z)}
  have hwF : ∀ i ∈ F, (a.ls k ℓ).world i = g := fun i hi => (Finset.mem_filter.mp hi).2
  -- the record choice satisfies the posterior success inequality
  have hSP : ∀ i, a.SuccProp π k ℓ i (a.bstarOf π k ℓ i) := by
    intro i
    have hex : ∃ b, a.SuccProp π k ℓ i b := plank_success ha π k ℓ i s (hP i)
    have key : a.bstarOf π k ℓ i = Classical.choose hex := by
      unfold bstarOf
      simp only [hex, ↓reduceDIte]
    rw [key]
    exact Classical.choose_spec hex
  -- measurability
  have hrec : ∀ T : Set ((Fin 2 → ℤ) × ℤ), MeasurableSet (a.recordOf π k ⁻¹' T) := by
    intro T
    rw [← Set.biUnion_preimage_singleton]
    exact MeasurableSet.biUnion (Set.to_countable T)
      (fun O _ => recordOf_fiber_measurable ha π k O)
  have hSm : ∀ i, MeasurableSet (S i) := by
    intro i
    exact MeasurableSet.iUnion fun m => (cvd_measurable ha π k ℓ i m).inter (hrec _)
  have hLm : ∀ i, MeasurableSet (L i) := by
    intro i
    have hΛ : MeasurableSet {w : Base × ℤ | i ∈ (a.ls k ℓ).lists g w} :=
      ((ha.layer k ℓ).2.2.1).2.2.2.2.2.2.2.1 g i
    exact (obs_measurable ha k) hΛ
  have hSsub : ∀ i, S i ⊆ a.plank k ℓ i := by
    intro i z hz
    obtain ⟨m, hm⟩ := mem_iUnion.mp hz
    exact cvd_subset_plank ha π k ℓ i m hm.1
  -- listed success lies in the target set
  have hmem : ∀ i ∈ F, S i ∩ L i ⊆ Tg := by
    intro i hi z hz
    have hw := hwF i hi
    obtain ⟨hzS, hzL⟩ := hz
    obtain ⟨m, hzc, hzr⟩ := mem_iUnion.mp hzS
    have hpar := parentOf_binOf ha π k ℓ i m
    have hbin := binLabel_binOf ha π k ℓ i m
    refine ⟨a.binOf π k ℓ i m, ?_, ⟨i, m, rfl, hzc.1⟩, ?_, ?_⟩
    · rw [hpar]
      exact hw
    · rw [hpar]
      exact hzc.2
    · simp only [listsOf, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hpar, hbin]
      exact ⟨hw, hzL, hzr⟩
  -- old lists hold almost everywhere on the success sets
  have hlist : ∀ i ∈ F, a.ρ k g (S i) ≤ a.ρ k g (S i ∩ L i) := by
    intro i hi
    have hw := hwF i hi
    have hnull : a.ρ k g (S i \ L i) = 0 := by
      have hsub : S i \ L i ⊆ a.plank k ℓ i \ L i := fun z hz => ⟨hSsub i hz.1, hz.2⟩
      apply measure_mono_null hsub
      have := lm_plank_list_ae ha k ℓ i
      rw [hw] at this
      exact this
    calc a.ρ k g (S i) ≤ a.ρ k g (S i ∩ L i) + a.ρ k g (S i \ L i) :=
          measure_le_inter_add_sdiff _ _ _
      _ = a.ρ k g (S i ∩ L i) := by rw [hnull, add_zero]
  -- planks of the world are almost disjoint
  have hdisj : (↑F : Set (Fin (a.ls k ℓ).n)).Pairwise
      (Function.onFun (AEDisjoint (a.ρ k g)) fun i => S i ∩ L i) := by
    intro i hi i' hi' hne
    have hw := hwF i hi
    have hw' := hwF i' hi'
    change a.ρ k g ((S i ∩ L i) ∩ (S i' ∩ L i')) = 0
    have hsub : (S i ∩ L i) ∩ (S i' ∩ L i') ⊆ a.plank k ℓ i ∩ a.plank k ℓ i' :=
      fun z hz => ⟨hSsub i hz.1.1, hSsub i' hz.2.1⟩
    apply measure_mono_null hsub
    have := lm_plank_inter_null ha k ℓ i i' hne (hw.trans hw'.symm)
    rw [hw] at this
    exact this
  -- assemble
  have hcov_le : a.ρ k g (a.layerCoverage π.θ π.σ k ℓ g) ≤ ∑ i ∈ F, a.ρ k g (a.cov π.θ π.σ k ℓ i) := by
    refine le_trans (measure_mono ?_) (measure_biUnion_finset_le F _)
    intro z hz
    simp only [layerCoverage, mem_iUnion] at hz
    obtain ⟨i, hi, hz⟩ := hz
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, hz⟩
  have hsucc : ∀ i ∈ F, a.ρ k g (a.cov π.θ π.σ k ℓ i) ≤ a.ρ k g (S i) +
      MatchApply.farMass (a.Gz π k ℓ i) (a.pairW π k ℓ i) (a.jetStep π k) := by
    intro i hi
    have hw := hwF i hi
    have := hSP i
    unfold SuccProp at this
    rw [hw] at this
    exact this
  calc a.ρ k g (a.layerCoverage π.θ π.σ k ℓ g)
      ≤ ∑ i ∈ F, a.ρ k g (a.cov π.θ π.σ k ℓ i) := hcov_le
    _ ≤ ∑ i ∈ F, (a.ρ k g (S i) +
          MatchApply.farMass (a.Gz π k ℓ i) (a.pairW π k ℓ i) (a.jetStep π k)) :=
        Finset.sum_le_sum hsucc
    _ = ∑ i ∈ F, a.ρ k g (S i) + ∑ i ∈ F,
          MatchApply.farMass (a.Gz π k ℓ i) (a.pairW π k ℓ i) (a.jetStep π k) :=
        Finset.sum_add_distrib
    _ ≤ ∑ i ∈ F, a.ρ k g (S i ∩ L i) + ∑ i ∈ F,
          MatchApply.farMass (a.Gz π k ℓ i) (a.pairW π k ℓ i) (a.jetStep π k) :=
        add_le_add (Finset.sum_le_sum hlist) le_rfl
    _ = a.ρ k g (⋃ i ∈ F, S i ∩ L i) + ∑ i ∈ F,
          MatchApply.farMass (a.Gz π k ℓ i) (a.pairW π k ℓ i) (a.jetStep π k) := by
        rw [measure_biUnion_finset₀ hdisj
          (fun i _ => ((hSm i).inter (hLm i)).nullMeasurableSet)]
    _ ≤ a.ρ k g Tg + ∑ i ∈ F,
          MatchApply.farMass (a.Gz π k ℓ i) (a.pairW π k ℓ i) (a.jetStep π k) := by
        gcongr
        exact iUnion₂_subset hmem

/-- The listed original success of a layer. -/
theorem lm_listed_mass_layer (ℓ : Fin (a.ct k)) (s : ℝ) (hP : ∀ i, a.PlankHyp π k ℓ i s)
    (hM : MatchAt (a.tangent k ^ π.σ.c₀) π.εm a.rd)
    {C : ℝ} (hC : 1 ≤ C)
    (hcov : ENNReal.ofReal ((C * a.H k ^ 2)⁻¹) ≤ a.layerCoverageMass π.θ π.σ k ℓ)
    (hCN : 4000 * C ≤ a.tangent k ^ (π.θ * π.σ.c₀)) :
    ENNReal.ofReal ((2 * C * a.H k ^ 2)⁻¹) ≤
      ∑ g, ENNReal.ofReal (ω (a.p k) (a.sm k) g) * a.ρ k g
        {z | ∃ j, (a.ls k ℓ).world (a.parentOf π k ℓ j) = g ∧
          z.1 ∈ {l | ∃ i h, a.binOf π k ℓ i h = j ∧ l ∈ a.asg π k ℓ i h} ∧
          z.2 ∈ I (a.ls k ℓ).T ((a.ls k ℓ).time (a.parentOf π k ℓ j)) ∧
          j ∈ a.listsOf π k ℓ g (a.obs k z)} := by
  classical
  set Tsum := ∑ g, ENNReal.ofReal (ω (a.p k) (a.sm k) g) * a.ρ k g
        {z | ∃ j, (a.ls k ℓ).world (a.parentOf π k ℓ j) = g ∧
          z.1 ∈ {l | ∃ i h, a.binOf π k ℓ i h = j ∧ l ∈ a.asg π k ℓ i h} ∧
          z.2 ∈ I (a.ls k ℓ).T ((a.ls k ℓ).time (a.parentOf π k ℓ j)) ∧
          j ∈ a.listsOf π k ℓ g (a.obs k z)} with hTsum
  set fm : Fin (a.ls k ℓ).n → ENNReal := fun i =>
    MatchApply.farMass (a.Gz π k ℓ i) (a.pairW π k ℓ i) (a.jetStep π k) with hfm
  have hregroup : ∑ g : Fin (a.Wk k), ENNReal.ofReal (ω (a.p k) (a.sm k) g) *
      ∑ i ∈ Finset.univ.filter (fun i : Fin (a.ls k ℓ).n => (a.ls k ℓ).world i = g), fm i =
      ∑ i : Fin (a.ls k ℓ).n, ENNReal.ofReal (ω (a.p k) (a.sm k) ((a.ls k ℓ).world i)) *
        fm i := by
    rw [← Finset.sum_fiberwise Finset.univ (fun i : Fin (a.ls k ℓ).n => (a.ls k ℓ).world i)
      (fun i => ENNReal.ofReal (ω (a.p k) (a.sm k) ((a.ls k ℓ).world i)) * fm i)]
    apply Finset.sum_congr rfl
    intro g _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  have hcovle : a.layerCoverageMass π.θ π.σ k ℓ ≤
      Tsum + ENNReal.ofReal ((2 * C * a.H k ^ 2)⁻¹) := by
    calc a.layerCoverageMass π.θ π.σ k ℓ
        = ∑ g, ENNReal.ofReal (ω (a.p k) (a.sm k) g) *
            a.ρ k g (a.layerCoverage π.θ π.σ k ℓ g) := rfl
      _ ≤ ∑ g, ENNReal.ofReal (ω (a.p k) (a.sm k) g) *
            (a.ρ k g {z | ∃ j, (a.ls k ℓ).world (a.parentOf π k ℓ j) = g ∧
              z.1 ∈ {l | ∃ i h, a.binOf π k ℓ i h = j ∧ l ∈ a.asg π k ℓ i h} ∧
              z.2 ∈ I (a.ls k ℓ).T ((a.ls k ℓ).time (a.parentOf π k ℓ j)) ∧
              j ∈ a.listsOf π k ℓ g (a.obs k z)} +
            ∑ i ∈ Finset.univ.filter (fun i : Fin (a.ls k ℓ).n => (a.ls k ℓ).world i = g),
              fm i) := by
          gcongr with g
          exact lm_world_bound ha π k ℓ s hP g
      _ = Tsum + ∑ g : Fin (a.Wk k), ENNReal.ofReal (ω (a.p k) (a.sm k) g) *
            ∑ i ∈ Finset.univ.filter (fun i : Fin (a.ls k ℓ).n => (a.ls k ℓ).world i = g),
              fm i := by
          rw [hTsum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro g _
          rw [mul_add]
      _ = Tsum + ∑ i : Fin (a.ls k ℓ).n,
            ENNReal.ofReal (ω (a.p k) (a.sm k) ((a.ls k ℓ).world i)) * fm i := by
          rw [hregroup]
      _ ≤ Tsum + ENNReal.ofReal ((2 * C * a.H k ^ 2)⁻¹) := by
          gcongr
          exact lm_weighted_farMass_le ha π k ℓ s hP hM hC hCN
  have hpos : 0 < 2 * C * a.H k ^ 2 := by
    have hH : 0 < a.H k := by linarith [(ha.bounds k).2.2.1]
    positivity
  have hhalf : ENNReal.ofReal ((C * a.H k ^ 2)⁻¹) =
      ENNReal.ofReal ((2 * C * a.H k ^ 2)⁻¹) + ENNReal.ofReal ((2 * C * a.H k ^ 2)⁻¹) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    have hCH : 0 < C * a.H k ^ 2 := by nlinarith
    field_simp
    ring
  have hfinal : ENNReal.ofReal ((2 * C * a.H k ^ 2)⁻¹) +
      ENNReal.ofReal ((2 * C * a.H k ^ 2)⁻¹) ≤
      Tsum + ENNReal.ofReal ((2 * C * a.H k ^ 2)⁻¹) := by
    rw [← hhalf]
    exact hcov.trans hcovle
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp hfinal

theorem listed_mass (s : ℝ) (hP : ∀ i, a.PlankHyp π k (a.nd k s) i s)
    (hM : MatchAt (a.tangent k ^ π.σ.c₀) π.εm a.rd)
    {C : ℝ} (hC : 1 ≤ C)
    (hcov : ENNReal.ofReal ((C * a.H k ^ 2)⁻¹) ≤
      a.layerCoverageMass π.θ π.σ k (a.nd k s))
    (hCN : 4000 * C ≤ a.tangent k ^ (π.θ * π.σ.c₀)) :
    ENNReal.ofReal ((2 * C * a.H k ^ 2)⁻¹) ≤
      ∑ g, ENNReal.ofReal (ω (a.p k) (a.sm k) g) * a.ρ k g
        {z | ∃ j, (a.ls k (a.nd k s)).world (a.parentOf π k (a.nd k s) j) = g ∧
          z.1 ∈ {l | ∃ i h, a.binOf π k (a.nd k s) i h = j ∧ l ∈ a.asg π k (a.nd k s) i h} ∧
          z.2 ∈ I (a.ls k (a.nd k s)).T
            ((a.ls k (a.nd k s)).time (a.parentOf π k (a.nd k s) j)) ∧
          j ∈ a.listsOf π k (a.nd k s) g (a.obs k z)} := by
  exact lm_listed_mass_layer ha π k (a.nd k s) s hP hM hC hcov hCN

end PreparedData

end Submission.Obl.k4_scalar_candidate_original_return
