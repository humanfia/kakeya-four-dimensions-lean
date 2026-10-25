-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.MK4Numerics, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The numerical parameters of the ancestor's MK4 rows (session x1088, for x1082's root stage).

`mk4_parameters` chooses every free parameter of x1082's `Forward.AncestorRows`
`ancestor_velocity_rows` at a given precision `θ` and front strip radius `N^(-ub L)`:
the velocity bound `Vmax`, the renewal radius `radius = N^(-ub L)/(6 κ)` (so `6 κ radius` is the
front radius), the strip width `w`, `baseRho = w/(4 (Vmax + 1))`, the census steps (`2^steps ≥ Kc^100`), the
cell and duration rates (each costing `c · ref_a`), `Kg = mk4Kg …`, `gfraction = 1/4`, the MK4 retention error `ε = cE` (its additive charge is
`(1 - 1/4)⁻¹ cE` of the full reference, x1095 12:31Z)
and the mesh index `n`, and proves all of the theorem's numerical side conditions together with
`80 Kg^7 mesh(n)^((1-d)/24) ≤ θ`.  What remains for the caller is `28 Kg^6 ≤ K`, a statement
about the explicit `mk4Kg`. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Forward.AncestorRows

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

noncomputable section

/-- The census steps: `2^steps ≥ Kc^100`. -/
def stepsOf (Kc : ℝ) : ℕ := ⌈100 * Real.logb 2 Kc⌉₊

theorem two_pow_stepsOf {Kc : ℝ} (hKc : 1 ≤ Kc) :
    Kc ^ (100 : ℕ) ≤ (2 : ℝ) ^ stepsOf Kc ∧ (2 : ℝ) ^ stepsOf Kc ≤ 2 * Kc ^ (100 : ℕ) := by
  have hKc0 : 0 < Kc := by linarith
  have hlog : 0 ≤ Real.logb 2 Kc := Real.logb_nonneg (by norm_num) hKc
  have hx : (0 : ℝ) ≤ 100 * Real.logb 2 Kc := by positivity
  have hpow : (2 : ℝ) ^ (100 * Real.logb 2 Kc) = Kc ^ (100 : ℕ) := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hKc0]
    norm_cast
  have hcast : (2 : ℝ) ^ stepsOf Kc = (2 : ℝ) ^ ((stepsOf Kc : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
  constructor
  · rw [hcast, ← hpow]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  · rw [hcast, ← hpow]
    have h1 : ((stepsOf Kc : ℕ) : ℝ) ≤ 100 * Real.logb 2 Kc + 1 :=
      (Nat.ceil_lt_add_one hx).le
    calc (2 : ℝ) ^ ((stepsOf Kc : ℕ) : ℝ) ≤ (2 : ℝ) ^ (100 * Real.logb 2 Kc + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      _ = 2 * (2 : ℝ) ^ (100 * Real.logb 2 Kc) := by
          rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring

/-- The MK4 row constant at the chosen rates and widths. -/
def mk4Kg (κ Vmax Kc Cband c frontRadius δL N : ℝ) : ℝ :=
  max (6 * (1 + 24 * κ + κ ^ 2 + Vmax))
    (max ((3 * (1 + 24 * κ + κ ^ 2 + Vmax) + 3) * 7 ^ 4 / c)
      (max (8 * Cband * (Kc * ((2 : ℝ) ^ stepsOf Kc) ^ 3) / c)
        ((4 * (Vmax + 1) * κ * N ^ (2 * δL) / frontRadius) ^ 3)))

/-- The mesh index: `mesh(n)^((1-d)/24) ≤ T`. -/
def meshIndexOf (T d : ℝ) : ℕ := ⌈8 * Real.logb 2 (1 / T) / (1 - d)⌉₊

theorem mesh_pow_le {T d : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (hd : d < 1) :
    Submission.Lib.K4DyadicRowScales.mesh (meshIndexOf T d) ^ ((1 - d) / 24) ≤ T := by
  set n := meshIndexOf T d with hn
  have hd1 : 0 < 1 - d := by linarith
  have hlog : 0 ≤ Real.logb 2 (1 / T) :=
    Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hT]; linarith)
  have hnge : 8 * Real.logb 2 (1 / T) / (1 - d) ≤ (n : ℝ) := Nat.le_ceil _
  -- `mesh n = 2^(-3n)`
  have hmesh : Submission.Lib.K4DyadicRowScales.mesh n = (2 : ℝ) ^ (-(3 * (n : ℝ))) := by
    rw [Submission.Lib.K4DyadicRowScales.mesh_eq_zpow, ← Real.rpow_intCast]
    push_cast
    ring_nf
  rw [hmesh, ← Real.rpow_mul (by norm_num)]
  have hTlog : T = (2 : ℝ) ^ (-Real.logb 2 (1 / T)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
    field_simp
  conv_rhs => rw [hTlog]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have : 8 * Real.logb 2 (1 / T) ≤ (n : ℝ) * (1 - d) := by
    rw [div_le_iff₀ hd1] at hnge; linarith
  nlinarith

/-- **The MK4 parameters.** For `κ ≥ 1`, `Vmax ≥ 0`, `Kc ≥ 1`, `Cband ≥ 0`, `0 < c ≤ 1`,
`0 ≤ ratio ≤ 1/2`, `0 < θ ≤ 1`, `0 ≤ d < 1`, `N ≥ 1`, `δL ≥ 0` and a front radius
`0 < frontRadius ≤ 1`, the choices below satisfy every numerical premise of
`ancestor_velocity_rows` and give rows with error at most `θ`. -/
theorem mk4_parameters {κ Vmax Kc Cband c cE ratio θ d N δL frontRadius meshCap : ℝ}
    (hκ : 1 ≤ κ) (hV : 0 ≤ Vmax) (hKc : 1 ≤ Kc) (hCband : 0 ≤ Cband) (hc : 0 < c) (hc1 : c ≤ 1)
    (hcE : 0 < cE) (hcE1 : cE ≤ 1)
    (hratio0 : 0 ≤ ratio) (hratio : ratio ≤ 1 / 2) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hd0 : 0 ≤ d)
    (hd : d < 1) (hN : 1 ≤ N) (hδL : 0 ≤ δL) (hfr : 0 < frontRadius) (hfr1 : frontRadius ≤ 1)
    (hcap : 0 < meshCap) (hcap1 : meshCap ≤ 1) :
    let Kg := mk4Kg κ Vmax Kc Cband c frontRadius δL N
    let steps := stepsOf Kc
    let radius := frontRadius / (6 * κ)
    let w := frontRadius / (κ * N ^ (2 * δL))
    let baseRho := w / (4 * (Vmax + 1))
    let cellRate := c / (Kc * ((2 : ℝ) ^ steps) ^ 3)
    let durationRate := c / ((3 * (1 + 24 * κ + κ ^ 2 + Vmax) + 3) * 7 ^ 4)
    let T := min (min (θ / (80 * Kg ^ 7)) meshCap) (min (1 / (64 * Kg)) (min (1 / (36 * Kg ^ 4))
      (((1 / 4 : ℝ) / 4) ^ 4 * cE ^ 4 /
        (256 * Parent.ParentSource.Broad.Velocity.curvatureRowConstant ^ 3 * Kg ^ 9 + 1))))
    let n := meshIndexOf T d
    let fineMesh := Submission.Lib.K4DyadicRowScales.mesh n / (2 : ℝ) ^ steps
    0 < fineMesh ∧ fineMesh ≤ 1 ∧ 1 ≤ Kc ∧ Kc ^ (100 : ℕ) ≤ (2 : ℝ) ^ steps ∧
      fineMesh * (2 : ℝ) ^ steps ≤ 1 ∧ 0 < cellRate ∧ 0 < durationRate ∧
      fineMesh * (2 : ℝ) ^ steps = Submission.Lib.K4DyadicRowScales.mesh n ∧
      6 * (1 + 24 * κ + κ ^ 2 + Vmax) ≤ Kg ∧ durationRate⁻¹ ≤ Kg ∧ 8 * Cband / cellRate ≤ Kg ∧
      0 ≤ baseRho ∧ 1 ≤ Kg * baseRho ^ 3 ∧ baseRho ≤ 1 / 4 ∧ 2 * (Vmax + 1) * baseRho ≤ w ∧
      w * N ^ (2 * δL) ≤ 6 * radius ∧ 6 * κ * radius ≤ frontRadius ∧
      (0 : ℝ) < 1 / 4 ∧ (1 / 4 : ℝ) < 1 - ratio ∧ 0 < cE ∧
      Submission.Lib.K4DyadicRowScales.mesh n ^ ((1 - d) / 24) ≤
        min (1 / (64 * Kg)) (min (1 / (36 * Kg ^ 4))
          (((1 / 4 : ℝ) / 4) ^ 4 * cE ^ 4 /
            (256 * Parent.ParentSource.Broad.Velocity.curvatureRowConstant ^ 3 * Kg ^ 9 + 1))) ∧
      80 * Kg ^ 7 * Submission.Lib.K4DyadicRowScales.mesh n ^ ((1 - d) / 24) ≤ θ ∧
      (Kc * ((2 : ℝ) ^ steps) ^ 3) * cellRate +
        durationRate * (3 * (1 + 24 * κ + κ ^ 2 + Vmax) + 3) * 7 ^ 4 ≤ 2 * c ∧
      Submission.Lib.K4DyadicRowScales.mesh n ≤ meshCap ∧ fineMesh ≤ meshCap := by
  intro Kg steps radius w baseRho cellRate durationRate T n fineMesh
  have hκ0 : 0 < κ := by linarith
  have hNp : 0 < N := by linarith
  have hNpow : 1 ≤ N ^ (2 * δL) := Real.one_le_rpow hN (by positivity)
  have hsteps := two_pow_stepsOf hKc
  have h2s : (0 : ℝ) < (2 : ℝ) ^ steps := by positivity
  have hA : 0 < 1 + 24 * κ + κ ^ 2 + Vmax := by positivity
  have hKg1 : 6 * (1 + 24 * κ + κ ^ 2 + Vmax) ≤ Kg := le_max_left _ _
  have hKgpos : 0 < Kg := lt_of_lt_of_le (by positivity) hKg1
  have hKg2 : (3 * (1 + 24 * κ + κ ^ 2 + Vmax) + 3) * 7 ^ 4 / c ≤ Kg :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hKg3 : 8 * Cband * (Kc * ((2 : ℝ) ^ stepsOf Kc) ^ 3) / c ≤ Kg :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hKg4 : (4 * (Vmax + 1) * κ * N ^ (2 * δL) / frontRadius) ^ 3 ≤ Kg :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hKg_ge1 : 1 ≤ Kg := le_trans (by nlinarith) hKg1
  -- `T`
  have hT0 : 0 < T := by
    have : 0 < 256 * Parent.ParentSource.Broad.Velocity.curvatureRowConstant ^ 3 * Kg ^ 9 + 1 := by
      have := Parent.ParentSource.Broad.Velocity.curvatureRowConstant_pos
      positivity
    exact lt_min (lt_min (by positivity) hcap) (lt_min (by positivity) (lt_min (by positivity)
      (by positivity)))
  have hT1 : T ≤ 1 := by
    refine (min_le_right _ _).trans ((min_le_left _ _).trans ?_)
    rw [div_le_one (by positivity)]; linarith
  have hmeshT := mesh_pow_le hT0 hT1 hd
  have hmesh0 := Submission.Lib.K4DyadicRowScales.mesh_pos n
  have hmesh1 : Submission.Lib.K4DyadicRowScales.mesh n ≤ 1 := by
    unfold Submission.Lib.K4DyadicRowScales.mesh
    exact pow_le_one₀ (Submission.Lib.K4DyadicRowScales.unit_pos n).le
      (Submission.Lib.K4DyadicRowScales.unit_le_one n)
  have hfine0 : 0 < fineMesh := div_pos hmesh0 h2s
  have hfine_eq : fineMesh * (2 : ℝ) ^ steps = Submission.Lib.K4DyadicRowScales.mesh n := by
    simp only [fineMesh]; field_simp
  have h2s1 : (1 : ℝ) ≤ (2 : ℝ) ^ steps := one_le_pow₀ (by norm_num)
  have hw0 : 0 < w := by positivity
  have hbase0 : 0 < baseRho := by positivity
  -- `baseRho^-3 ≤ Kg`
  have hbaseRho_inv : (4 * (Vmax + 1) * κ * N ^ (2 * δL) / frontRadius) = baseRho⁻¹ := by
    simp only [baseRho, w]; field_simp
  have hcond : 1 ≤ Kg * baseRho ^ 3 := by
    have h := hKg4
    rw [hbaseRho_inv, inv_pow] at h
    have hb3 : 0 < baseRho ^ 3 := by positivity
    rw [inv_le_iff_one_le_mul₀ hb3] at h
    linarith
  have hw1 : w ≤ 1 := by
    simp only [w]
    rw [div_le_one (by positivity)]
    nlinarith
  have hle : Submission.Lib.K4DyadicRowScales.mesh n ≤
      Submission.Lib.K4DyadicRowScales.mesh n ^ ((1 - d) / 24) := by
    apply Real.self_le_rpow_of_le_one hmesh0.le hmesh1
    rw [div_le_one (by norm_num)]; linarith
  have hTcap : T ≤ meshCap := (min_le_left _ _).trans (min_le_right _ _)
  have hmeshcap : Submission.Lib.K4DyadicRowScales.mesh n ≤ meshCap :=
    hle.trans (hmeshT.trans hTcap)
  have hfinecap : fineMesh ≤ meshCap := by
    have hfm : fineMesh ≤ Submission.Lib.K4DyadicRowScales.mesh n :=
      div_le_self hmesh0.le h2s1
    exact hfm.trans hmeshcap
  refine ⟨hfine0, ?_, hKc, hsteps.1, by rw [hfine_eq]; exact hmesh1, by positivity, by positivity,
    hfine_eq, hKg1, ?_, ?_, hbase0.le, hcond, ?_, ?_, ?_, ?_, by norm_num, by linarith,
    hcE, ?_, ?_, ?_, ?_, ?_⟩
  · -- fineMesh ≤ 1
    simp only [fineMesh]
    rw [div_le_one h2s]; linarith
  · -- durationRate⁻¹ ≤ Kg
    simp only [durationRate]; rw [inv_div]; exact hKg2
  · -- 8 Cband / cellRate ≤ Kg
    simp only [cellRate]
    rw [div_div_eq_mul_div]
    calc 8 * Cband * (Kc * ((2 : ℝ) ^ steps) ^ 3) / c ≤ Kg := hKg3
      _ = Kg := rfl
  · -- baseRho ≤ 1/4
    simp only [baseRho]
    rw [div_le_iff₀ (by positivity)]; nlinarith
  · -- 2 (Vmax + 1) baseRho ≤ w
    simp only [baseRho]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  · -- w N^(2 δL) ≤ 6 radius
    simp only [w, radius]
    rw [div_mul_eq_mul_div, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hκ0 (lt_of_lt_of_le zero_lt_one hNpow)]
  · -- 6 κ radius ≤ frontRadius
    simp only [radius]; rw [mul_div_cancel₀ _ (by positivity)]
  · -- hsmall
    exact hmeshT.trans (min_le_right _ _)
  · -- the error
    have h1 : Submission.Lib.K4DyadicRowScales.mesh n ^ ((1 - d) / 24) ≤ θ / (80 * Kg ^ 7) :=
      hmeshT.trans ((min_le_left _ _).trans (min_le_left _ _))
    have h80 : 0 < 80 * Kg ^ 7 := by positivity
    rw [le_div_iff₀ h80] at h1
    linarith
  · -- the loss
    simp only [cellRate, durationRate]
    have e1 : Kc * ((2 : ℝ) ^ steps) ^ 3 * (c / (Kc * ((2 : ℝ) ^ steps) ^ 3)) = c := by
      field_simp
    have e2 : c / ((3 * (1 + 24 * κ + κ ^ 2 + Vmax) + 3) * 7 ^ 4) *
        (3 * (1 + 24 * κ + κ ^ 2 + Vmax) + 3) * 7 ^ 4 = c := by
      field_simp
    linarith
  · exact hmeshcap
  · exact hfinecap

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
