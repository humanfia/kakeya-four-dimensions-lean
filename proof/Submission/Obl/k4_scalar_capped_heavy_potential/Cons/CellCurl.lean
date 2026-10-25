import Submission.Obl.k4_scalar_capped_heavy_potential.Core.BaseSublevel
import Submission.Obl.k4_scalar_capped_heavy_potential.Core.SwitchGlobalMass
import Submission.Obl.k4_scalar_capped_heavy_potential.Core.PolynomialVariation
import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.CellSublevel
import Submission.Lib.K4ScalarActualSwitching.FiniteReference

/-!
# Quantitative curl from switched paths, with floor-cell start ceilings

This is x0511/x0212's `exists_homogeneous_coefficient_curl_constant`
(o062, adapted in `Core/HomogeneousCurl.lean`) with its start-density
hypothesis `ν.map x ≤ M • volume` replaced by a ceiling on floor cells of
side `w`: the start law of an incidence measure need not have a density, but
its base-cell masses are controlled. The price is an additive term linear in
`w`, which is negligible at fine cells.
-/

namespace Submission.Obl.k4_scalar_capped_heavy_potential.Cons

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4ScalarSwitching.Switching
open Submission.Obl.k4_scalar_capped_heavy_potential.Core.Switching

/-- The half box of the plane. -/
def halfBox : Set (Fin 2 → ℝ) := Icc (fun _ : Fin 2 => -(1 / 2 : ℝ)) (fun _ => 1 / 2)

theorem halfBox_subset : halfBox ⊆ Icc (-1 : Fin 2 → ℝ) 1 := by
  intro z hz
  constructor <;> intro i
  · have := hz.1 i
    simp only at this
    simp only [Pi.neg_apply, Pi.one_apply]
    linarith
  · have := hz.2 i
    simp only at this
    simp only [Pi.one_apply]
    linarith

theorem measurableSet_halfBox : MeasurableSet halfBox := measurableSet_Icc

/-- **Cell curl estimate.** All coefficients of the curl of a degree-`D`
field `(A,B)` are bounded by the original switched-path data, when the
start law only has floor-cell ceilings `M w² ν(univ)`. -/
theorem exists_cell_curl_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : MvPolynomial (Fin 2) ℝ),
      A.totalDegree ≤ D → B.totalDegree ≤ D →
      ∀ K L M p area ε w KP : ℝ, 1 ≤ K → 0 < L → 1 ≤ M →
        0 < p → p ≤ L → 0 ≤ area → 0 ≤ ε → 0 < w → w ≤ 1 / 2 → 0 ≤ KP →
        (∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z (pderiv 0 B - pderiv 1 A)| ≤ KP) →
        ∀ (Θ : Type*) [MeasurableSpace Θ] (ν : Measure Θ) [IsFiniteMeasure ν] [NeZero ν]
          (μ : Measure (Θ × (Fin 4 → ℝ))) (S : Set (Θ × (Fin 4 → ℝ)))
          (x : Θ → Fin 2 → ℝ) (v : Θ → Fin 4 → ℝ) (X₀ : Θ → ℝ)
          (ι : Type*) (F : Finset ι) (E : Θ → ι → Set (Fin 2 → ℝ)) (c : Θ → ι → ℝ),
          Measurable x → MeasurableSet S →
          (∀ q : Fin 2 → ℤ, ν {θ | (fun e => ⌊x θ e / w⌋) = q} ≤
            ENNReal.ofReal (M * w ^ 2 * (ν univ).toReal)) →
          μ ≤ ENNReal.ofReal L • (ν.prod volume) →
          ENNReal.ofReal (p * (ν univ).toReal) ≤ μ S →
          (∀ z ∈ S, z.2 ∈ Icc (-1 : Fin 4 → ℝ) 1) →
          (∀ z ∈ S, x z.1 ∈ halfBox ∧
            (∀ i, |v z.1 i| ≤ K) ∧ 1 / K ≤ |v z.1 1 - v z.1 0| ∧
              1 / K ≤ |v z.1 3 - v z.1 2|) →
          (∀ θ, ∀ i ∈ F, MeasurableSet (E θ i)) →
          (∀ θ, (∑ i ∈ F, volume (E θ i)) ≤ ENNReal.ofReal area) →
          (∀ z ∈ S, ∃ i ∈ F, switchedBaseEndpoint (x z.1) (v z.1) z.2 ∈ E z.1 i ∧
            |X₀ z.1 + eval z.2 (brokenHeight A B (x z.1) (v z.1)) - c z.1 i| ≤ ε) →
          ∀ e : Fin 2 →₀ ℕ, |(pderiv 0 B - pderiv 1 A).coeff e| ≤
            C * K ^ 4 * L ^ (6 * D + 1) * M ^ (2 * D) * area * ε / p ^ (6 * D + 1) +
              C * KP * w * L ^ (2 * D) * M ^ (2 * D) / p ^ (2 * D) := by
  classical
  obtain ⟨Cbase, hCbase, hsub⟩ := exists_base_polynomial_sublevel_constant D
  obtain ⟨Cpath, hCpath, hmassBound⟩ := exists_global_switching_mass_constant D
  obtain ⟨Cvar, hCvar, hvar⟩ := exists_symmetric_square_variation_constant D
  let nb := 2 * D
  let ni := 4 * D
  let Fb : ℝ := (64 * ((D : ℝ) + 1)) ^ nb
  let Fi : ℝ := (512 * ((D : ℝ) + 1)) ^ ni
  have hFb : 0 < Fb := by dsimp [Fb]; positivity
  have hFi : 0 < Fi := by dsimp [Fi]; positivity
  let C₁ : ℝ := 1024 * Cbase * Cpath * Fb * Fi * ((D : ℝ) + 2) * 64 ^ nb * 4 ^ ni
  let C₂ : ℝ := 8 * Cbase * Fb * Cvar * 64 ^ nb
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 < C₂ := by dsimp [C₂]; positivity
  refine ⟨C₁ + C₂, by positivity, ?_⟩
  intro A B hA hB K L M p area ε w KP hK hL hM hp hpL harea hε hw hw1 hKP hcurlKP
    Θ _ ν _ _ μ S x v X₀ ι F E c hx hS hcell hdom hmass hbox hdata hE hareaSum hcover e
  have hKp : 0 < K := by linarith
  have hMp : 0 < M := by linarith
  set P := pderiv 0 B - pderiv 1 A with hPdef
  have hP : P.totalDegree ≤ D := by
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · exact (Submission.Lib.K4PolynomialPotential.totalDegree_pderiv_le B 0).trans
        ((Nat.sub_le _ _).trans hB)
    · exact (Submission.Lib.K4PolynomialPotential.totalDegree_pderiv_le A 1).trans
        ((Nat.sub_le _ _).trans hA)
  set m := (ν univ).toReal with hmdef
  have hm : 0 < m := ENNReal.toReal_pos (NeZero.ne (ν univ)) (measure_ne_top _ _)
  have hmass_eq : ENNReal.ofReal m = ν univ := ENNReal.ofReal_toReal (measure_ne_top _ _)
  -- the two terms of the bound are nonnegative
  have hT₁ : 0 ≤ (C₁ + C₂) * K ^ 4 * L ^ (6 * D + 1) * M ^ (2 * D) * area * ε /
      p ^ (6 * D + 1) := by positivity
  have hT₂ : 0 ≤ (C₁ + C₂) * KP * w * L ^ (2 * D) * M ^ (2 * D) / p ^ (2 * D) := by
    positivity
  set k := |P.coeff e| with hkdef
  by_cases hz : k = 0
  · rw [hz]
    exact add_nonneg hT₁ hT₂
  have hk : 0 < k := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hz)
  let ηb := p / (64 * L * M)
  let ηi := p / (4 * L)
  have hηb : 0 < ηb := div_pos hp (by positivity)
  have hηi : 0 < ηi := div_pos hp (by positivity)
  have hηb1 : ηb ≤ 1 := by
    dsimp [ηb]
    apply (div_le_one (by positivity)).mpr
    nlinarith
  have hηi1 : ηi ≤ 1 := by
    dsimp [ηi]
    apply (div_le_one (by positivity)).mpr
    linarith
  let σ' := k * ηb ^ nb / (2 * Cbase * Fb)
  have hσ' : 0 < σ' := by dsimp [σ']; positivity
  have hsmall : volume {z : Fin 2 → ℝ | z ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧ |eval z P| ≤ σ'} <
      ENNReal.ofReal ηb := hsub P hP e k ηb hk hηb hηb1 le_rfl
  let Lip := Cvar * KP
  have hLip0 : 0 ≤ Lip := by dsimp [Lip]; positivity
  have hLip : ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, ∀ z' ∈ Icc (-1 : Fin 2 → ℝ) 1,
      |eval z P - eval z' P| ≤ Lip * (|z 0 - z' 0| + |z 1 - z' 1|) := by
    intro z hz z' hz'
    exact hvar P hP KP hKP hcurlKP z' hz' z hz
  by_cases hcase : 2 * Lip * w ≤ σ' / 2
  swap
  · -- the cell is too coarse: then `k` is controlled by the cell term
    push Not at hcase
    have hk' : k * ηb ^ nb < 8 * Cbase * Fb * Lip * w := by
      have h1 : k * ηb ^ nb / (2 * Cbase * Fb) < 4 * Lip * w := by
        have h := hcase
        dsimp only [σ'] at h
        linarith
      have h2 := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Cbase * Fb)).mp h1
      have h3 : 4 * Lip * w * (2 * Cbase * Fb) = 8 * Cbase * Fb * Lip * w := by ring
      linarith
    have hηbpow : ηb ^ nb = p ^ nb / (64 * L * M) ^ nb := by dsimp [ηb]; rw [div_pow]
    have hk'' : k * p ^ nb < 8 * Cbase * Fb * Lip * w * (64 * L * M) ^ nb := by
      rw [hηbpow] at hk'
      have hpos : 0 < (64 * L * M) ^ nb := by positivity
      have := mul_lt_mul_of_pos_right hk' hpos
      rwa [mul_assoc, div_mul_cancel₀ _ hpos.ne'] at this
    have hkle : k ≤ C₂ * KP * w * L ^ (2 * D) * M ^ (2 * D) / p ^ (2 * D) := by
      rw [le_div_iff₀ (by positivity)]
      have hexp : (64 * L * M) ^ nb = 64 ^ nb * L ^ (2 * D) * M ^ (2 * D) := by
        dsimp [nb]; rw [mul_pow, mul_pow]
      rw [hexp] at hk''
      have : C₂ * KP * w * L ^ (2 * D) * M ^ (2 * D) =
          8 * Cbase * Fb * Lip * w * (64 ^ nb * L ^ (2 * D) * M ^ (2 * D)) := by
        dsimp [C₂, Lip]; ring
      rw [this]
      exact hk''.le
    calc
      k ≤ C₂ * KP * w * L ^ (2 * D) * M ^ (2 * D) / p ^ (2 * D) := hkle
      _ ≤ (C₁ + C₂) * KP * w * L ^ (2 * D) * M ^ (2 * D) / p ^ (2 * D) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        gcongr
        linarith
      _ ≤ _ := le_add_of_nonneg_left hT₁
  -- main case: the starting-point discard costs only the sublevel volume
  let σ := σ' / 2
  let κ := σ / (8 * K ^ 4)
  have hκ : 0 < κ := div_pos (by positivity) (by positivity)
  have hskew : 8 * K ^ 4 * κ = σ := by dsimp [κ]; field_simp
  -- move the starting points outside the unit box when they leave the half box
  let x' : Θ → Fin 2 → ℝ := fun θ => if x θ ∈ halfBox then x θ else fun _ => 2
  have hx' : Measurable x' :=
    Measurable.ite (measurableSet_halfBox.preimage hx) hx measurable_const
  have hx'S : ∀ z ∈ S, x' z.1 = x z.1 := fun z hz => by
    show (if x z.1 ∈ halfBox then x z.1 else fun _ => 2) = x z.1
    rw [if_pos (hdata z hz).1]
  have hBad : {θ | x' θ ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧ |eval (x' θ) P| ≤ 8 * K ^ 4 * κ} ⊆
      {θ | x θ ∈ halfBox ∧ |eval (x θ) P| ≤ σ} := by
    intro θ hθ
    by_cases hθx : x θ ∈ halfBox
    · have hxx : x' θ = x θ := by
        show (if x θ ∈ halfBox then x θ else fun _ => 2) = x θ
        rw [if_pos hθx]
      have h2 := hθ.2
      rw [hxx, hskew] at h2
      exact ⟨hθx, h2⟩
    · exfalso
      have hxx : x' θ = fun _ => 2 := by
        show (if x θ ∈ halfBox then x θ else fun _ => 2) = fun _ => 2
        rw [if_neg hθx]
      have h := (hθ.1.2 0)
      rw [hxx] at h
      simp only [Pi.one_apply] at h
      norm_num at h
  have hcellbound := cell_sublevel_mass_le ν x P hw hw1
    (by positivity : 0 ≤ M * w ^ 2 * m) hLip0 (s := σ) hcell hLip
  have hw2 : M * w ^ 2 * m / w ^ 2 = M * m := by field_simp
  rw [hw2] at hcellbound
  have hmono : {z : Fin 2 → ℝ | z ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧ |eval z P| ≤ σ + 2 * Lip * w} ⊆
      {z : Fin 2 → ℝ | z ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧ |eval z P| ≤ σ'} := by
    intro z hz
    refine ⟨hz.1, hz.2.trans ?_⟩
    dsimp [σ]
    linarith
  have hνbad : ν {θ | x' θ ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧ |eval (x' θ) P| ≤ 8 * K ^ 4 * κ} ≤
      ENNReal.ofReal (M * m) * ENNReal.ofReal ηb := by
    calc
      _ ≤ ν {θ | x θ ∈ halfBox ∧ |eval (x θ) P| ≤ σ} := measure_mono hBad
      _ ≤ ENNReal.ofReal (M * m) * volume {z : Fin 2 → ℝ | z ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧
            |eval z P| ≤ σ + 2 * Lip * w} := hcellbound
      _ ≤ ENNReal.ofReal (M * m) * volume {z : Fin 2 → ℝ | z ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧
            |eval z P| ≤ σ'} := by gcongr
      _ ≤ ENNReal.ofReal (M * m) * ENNReal.ofReal ηb := by gcongr
  -- normalize the reference
  let ν₀ : Measure Θ := (ν univ)⁻¹ • ν
  haveI : IsProbabilityMeasure ν₀ := by
    constructor
    simp only [ν₀, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (NeZero.ne (ν univ)) (measure_ne_top _ _)
  have hdom₀ : μ ≤ ENNReal.ofReal (L * m) • (ν₀.prod volume) := by
    have h := Submission.Lib.K4ScalarActualSwitching.path_ceiling_with_probability_reference
      ν volume μ (ENNReal.ofReal L) hdom
    have hsc : ENNReal.ofReal L * ν univ = ENNReal.ofReal (L * m) := by
      rw [ENNReal.ofReal_mul hL.le, hmass_eq]
    rw [hsc] at h
    exact h
  have hνbad₀ : ν₀ {θ | x' θ ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧ |eval (x' θ) P| ≤ 8 * K ^ 4 * κ} ≤
      ENNReal.ofReal (M * ηb) := by
    simp only [ν₀, Measure.smul_apply, smul_eq_mul]
    calc
      _ ≤ (ν univ)⁻¹ * (ENNReal.ofReal (M * m) * ENNReal.ofReal ηb) := by gcongr
      _ = ENNReal.ofReal (M * ηb) := by
        rw [← hmass_eq, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_inv_of_pos hm, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
  have hdata' : ∀ z ∈ S, x' z.1 ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧
      (∀ i, |v z.1 i| ≤ K) ∧ 1 / K ≤ |v z.1 1 - v z.1 0| ∧ 1 / K ≤ |v z.1 3 - v z.1 2| := by
    intro z hz
    rw [hx'S z hz]
    obtain ⟨h1, h2, h3, h4⟩ := hdata z hz
    exact ⟨halfBox_subset h1, h2, h3, h4⟩
  have hcover' : ∀ z ∈ S, ∃ i ∈ F, switchedBaseEndpoint (x' z.1) (v z.1) z.2 ∈ E z.1 i ∧
      |X₀ z.1 + eval z.2 (brokenHeight A B (x' z.1) (v z.1)) - c z.1 i| ≤ ε := by
    intro z hz
    rw [hx'S z hz]
    exact hcover z hz
  let threshold := κ * ηi ^ ni / (2 * Cpath * Fi)
  have hthreshold : 0 < threshold := by dsimp [threshold]; positivity
  have hmass' := hmassBound A B hA hB K (L * m) κ ηi ε area (M * ηb) hK (by positivity)
    hκ hηi hηi1 hε harea (by positivity)
    Θ ν₀ μ S x' v X₀ ι F E c hx' hS hdom₀ hbox hdata' hνbad₀ hE hareaSum hcover'
  have hreal : p * m ≤ L * m * (16 * (M * ηb) + ηi +
      8 * ((D : ℝ) + 2) * area * ε / threshold) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hmass.trans hmass')
  have hreal' : p ≤ L * (16 * (M * ηb) + ηi + 8 * ((D : ℝ) + 2) * area * ε / threshold) := by
    have h : p * m ≤ (L * (16 * (M * ηb) + ηi +
        8 * ((D : ℝ) + 2) * area * ε / threshold)) * m := by linarith
    exact le_of_mul_le_mul_right h hm
  have hbudget : L * (16 * (M * ηb) + ηi) = p / 2 := by
    dsimp [ηb, ηi]
    field_simp
    ring
  have hhalf : p / 2 ≤ (8 * L * ((D : ℝ) + 2) * area * ε) / threshold := by
    have hid : L * (16 * (M * ηb) + ηi + 8 * ((D : ℝ) + 2) * area * ε / threshold) =
        L * (16 * (M * ηb) + ηi) + (8 * L * ((D : ℝ) + 2) * area * ε) / threshold := by ring
    rw [hid, hbudget] at hreal'
    linarith
  have hmul := (le_div_iff₀ hthreshold).mp hhalf
  -- unfold the threshold
  have hthr : threshold = k * ηb ^ nb * ηi ^ ni / (64 * K ^ 4 * Cbase * Fb * Cpath * Fi) := by
    dsimp [threshold, κ, σ, σ']
    field_simp
    ring
  rw [hthr] at hmul
  have hpower : k * p * ηb ^ nb * ηi ^ ni ≤
      1024 * Cbase * Cpath * Fb * Fi * K ^ 4 * L * ((D : ℝ) + 2) * area * ε := by
    have hden : 0 < 64 * K ^ 4 * Cbase * Fb * Cpath * Fi := by positivity
    have h2 := mul_le_mul_of_nonneg_right hmul hden.le
    have hid : p / 2 * (k * ηb ^ nb * ηi ^ ni / (64 * K ^ 4 * Cbase * Fb * Cpath * Fi)) *
        (64 * K ^ 4 * Cbase * Fb * Cpath * Fi) = k * p * ηb ^ nb * ηi ^ ni / 2 := by
      field_simp
    rw [hid] at h2
    have h4 : 8 * L * ((D : ℝ) + 2) * area * ε * (64 * K ^ 4 * Cbase * Fb * Cpath * Fi) * 2 =
        1024 * Cbase * Cpath * Fb * Fi * K ^ 4 * L * ((D : ℝ) + 2) * area * ε := by ring
    linarith
  have hsc := mul_le_mul_of_nonneg_right hpower
    (mul_nonneg (pow_nonneg (by positivity : 0 ≤ 64 * L * M) nb)
      (pow_nonneg (by positivity : 0 ≤ 4 * L) ni))
  have hsum : nb + ni = 6 * D := by dsimp [nb, ni]; omega
  have hleft : k * p * ηb ^ nb * ηi ^ ni * ((64 * L * M) ^ nb * (4 * L) ^ ni) =
      k * p ^ (6 * D + 1) := by
    dsimp [ηb, ηi]
    rw [← hsum, pow_succ, pow_add, div_pow, div_pow]
    field_simp
  rw [hleft] at hsc
  have hkmain : k ≤ C₁ * K ^ 4 * L ^ (6 * D + 1) * M ^ (2 * D) * area * ε /
      p ^ (6 * D + 1) := by
    apply (le_div_iff₀ (pow_pos hp _)).mpr
    convert hsc using 1
    dsimp only [C₁]
    rw [← hsum, pow_succ, pow_add, mul_pow, mul_pow, mul_pow]
    ring
  calc
    k ≤ C₁ * K ^ 4 * L ^ (6 * D + 1) * M ^ (2 * D) * area * ε / p ^ (6 * D + 1) := hkmain
    _ ≤ (C₁ + C₂) * K ^ 4 * L ^ (6 * D + 1) * M ^ (2 * D) * area * ε / p ^ (6 * D + 1) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      gcongr
      linarith
    _ ≤ _ := le_add_of_nonneg_right hT₂

end Submission.Obl.k4_scalar_capped_heavy_potential.Cons
