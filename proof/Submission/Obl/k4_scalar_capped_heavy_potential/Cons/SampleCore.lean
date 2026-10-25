import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.BlockCurl
import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.BlockPotential
import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.SampleAlgebra

/-!
# The potential on one block, with the sample parameters

The parameter choices of the conservativity step at one sample are fed to the
block curl estimate and the block potential; the numerical conditions are
taken as hypotheses (they follow from one comparison between the subpower and
a fixed power of `N`, see `Cons/Sample.lean`).
-/

namespace Submission.Obl.k4_scalar_capped_heavy_potential.Cons

open Set MeasureTheory MvPolynomial

set_option maxHeartbeats 1600000 in
theorem exists_sample_core (D : ℕ) :
    ∃ Ccurl Cpot : ℝ, 0 < Ccurl ∧ 0 < Cpot ∧
    ∀ (νg : Measure (ℕ × (Fin 5 → ℝ))) [IsProbabilityMeasure νg]
      (πg : Measure ℝ) [IsProbabilityMeasure πg]
      (μ : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (Ag : Set (ℕ × (Fin 5 → ℝ))) (t₀ h : ℝ)
      (z₀ : Fin 2 → ℝ) (𝒯 : Fin 2 → MvPolynomial (Fin 2) ℝ) (X Y d κ S Z B : ℝ),
      MeasurableSet Ag → (∀ᵐ l ∂νg, ∀ i, |l.2 i| ≤ Y) →
      0 < h → h ≤ 1 → X ^ (-κ) / Y ≤ h → h ≤ Y * X ^ (-κ) →
      (∀ t ∈ Icc t₀ (t₀ + h), |t| ≤ 1) →
      μ ≤ ENNReal.ofReal Y • (νg.prod volume) →
      μ {p | p.1 ∈ Ag ∧ p.2 ∈ Icc t₀ (t₀ + h)}ᶜ = 0 →
      ENNReal.ofReal (h / Y) * νg Ag ≤ μ univ → μ univ ≠ 0 →
      (∀ᵐ p ∂μ, ∀ t ∈ Icc t₀ (t₀ + h), ∀ i, |ubase z₀ h p.1 t i| ≤ Y) →
      (∀ q : Fin 2 → ℤ, μ {p | (fun i => ⌊ubase z₀ h p.1 p.2 i / X ^ (-Z)⌋) = q} ≤
        ENNReal.ofReal (Y * h * X ^ (-2 * Z)) * νg Ag) →
      (∀ (q : Fin 3 → ℤ) (c : ℤ),
        μ {p | physState (X ^ (-B)) p = q ∧ p.1.2 1 ∈ {v : ℝ | ⌊v / X ^ (-(Z + 1))⌋ = c}} ≤
          ENNReal.ofReal Y * μ {p | physState (X ^ (-B)) p = q} *
            πg {v : ℝ | ⌊v / X ^ (-(Z + 1))⌋ = c}) →
      (∀ c : ℤ, πg {v : ℝ | ⌊v / X ^ (-(κ * (1 - d) / 64))⌋ = c} ≤
        ENNReal.ofReal (Y * X ^ (-S * (κ * (1 - d) / 64)))) →
      (∀ i, (𝒯 i).totalDegree ≤ D) → (∀ i b, |(𝒯 i).coeff b| ≤ Y) →
      (∀ᵐ p ∂μ, ∀ t ∈ Icc t₀ (t₀ + h), |p.1.2 3 + 2 * t * p.1.2 4 -
        ∑ i : Fin 2, eval (ubase z₀ h p.1 t) (𝒯 i) * (![1, p.1.2 1] : Fin 2 → ℝ) i| ≤
          Y * X ^ (-1 : ℝ) * h ^ (-(3 : ℝ) / 4)) →
      (jointSupport μ z₀ h (X ^ (-Z)) (X ^ (-1 : ℝ) * h ^ ((1 : ℝ) / 8))).Finite →
      ((jointSupport μ z₀ h (X ^ (-Z)) (X ^ (-1 : ℝ) * h ^ ((1 : ℝ) / 8))).ncard : ℝ) ≤
        Y * X ^ (2 * Z) * (X ^ (-1 : ℝ) / (X ^ (-1 : ℝ) * h ^ ((1 : ℝ) / 8))) ^ d →
      2 ≤ X → 1 ≤ Y → 0 ≤ d → d < 1 → 0 < κ → κ ≤ 1 → 10 ≤ Z → Z + 10 ≤ B →
      5 * Y ^ 2 ≤ X ^ (B - κ - Z - 1) → 24 * Y ^ 1 ≤ X ^ (1 : ℝ) →
      48 * Y ^ 2 ≤ X ^ (S * (κ * (1 - d) / 64)) → 64 * Y ^ 3 ≤ X ^ (κ / 8) →
      (768 * Ccurl * (2 ^ (D + 1) * (((D + 1) ^ 2 : ℕ) : ℝ) + 5) ^ 2) * Y ^ (2 * D + 4) ≤
        X ^ (Z - 2 * (κ * (1 - d) / 64)) →
      (16 * (2 ^ (D + 1) * (((D + 1) ^ 2 : ℕ) : ℝ) + 5)) * Y ^ (D + 2) ≤
        X ^ (Z - κ * (1 - d) / 64) →
      32 * Y ^ 0 ≤ X ^ Z →
      3 * Y ^ 2 ≤ X ^ (κ / 4 - 2 * (κ * (1 - d) / 1000)) →
      (3 * ((D : ℝ) + 1) ^ 2 * (Ccurl * (2 ^ (D + 1) * (((D + 1) ^ 2 : ℕ) : ℝ) + 5) ^ 4 *
          ((2 : ℝ) ^ 28) ^ (6 * D + 1) * (4 : ℝ) ^ (2 * D) * (2 : ℝ) ^ (6 * D + 1))) *
          Y ^ (4 * (D + 2) + 16 * (6 * D + 1) + 4 * (2 * D) + 1) ≤
        X ^ (κ * (1 - d) / 8 - 4 * (κ * (1 - d) / 64) - 2 * (κ * (1 - d) / 1000)) →
      (3 * ((D : ℝ) + 1) ^ 2 * (Ccurl * ((2 : ℝ) ^ (D + 2) *
          ((((D + 1) ^ 2 : ℕ) : ℝ) * (2 * ((D : ℝ) + 1)))) * ((2 : ℝ) ^ 28) ^ (2 * D) *
          (4 : ℝ) ^ (2 * D) * (2 : ℝ) ^ (2 * D))) *
          Y ^ ((D + 3) + 16 * (2 * D) + 4 * (2 * D)) ≤
        X ^ (Z - 1 - 2 * (κ * (1 - d) / 1000)) →
      ∃ (P : MvPolynomial (Fin 2) ℝ) (Kc : ℝ), P.totalDegree ≤ D + 2 ∧
        (∀ b, |P.coeff b| ≤ Cpot ^ 2 * Kc) ∧
        (∀ u : Fin 2 → ℝ, (∀ i, |u i| ≤ Y) → |eval u P| ≤ Kc) ∧
        Kc ≤ 2 ^ (D + 2) * (((D + 1) ^ 2 : ℕ) : ℝ) * Y ^ (D + 2) ∧
        ∀ l : ℕ × (Fin 5 → ℝ),
          (∀ t ∈ Icc t₀ (t₀ + h), ∀ i, |ubase z₀ h l t i| ≤ Y) →
          (∀ t ∈ Icc t₀ (t₀ + h), |l.2 3 + 2 * t * l.2 4 -
            ∑ i : Fin 2, eval (ubase z₀ h l t) (𝒯 i) * (![1, l.2 1] : Fin 2 → ℝ) i| ≤
              Y * X ^ (-1 : ℝ) * h ^ (-(3 : ℝ) / 4)) →
          ∀ t ∈ Icc t₀ (t₀ + h),
            |(xL l t - eval (ubase z₀ h l t) P) - (xL l t₀ - eval (ubase z₀ h l t₀) P)| ≤
              X ^ (-1 - 2 * (κ * (1 - d) / 1000)) := by
  obtain ⟨Ccurl, hCcurl, hcurl⟩ := exists_block_curl_constant D
  obtain ⟨Cpot, hCpot, hpot⟩ := exists_block_potential_constant D
  refine ⟨Ccurl, Cpot, hCcurl, hCpot, ?_⟩
  intro νg _ πg _ μ Ag t₀ h z₀ 𝒯 X Y d κ S Z B hA hbdd hh0 hh1 hhlo hhhi hblock hμdom hμsupp
    hμmass hμpos hu hcell hpalv hangb h𝒯deg h𝒯coeff hfield hJfin hJcard hX2 hY1 hd0 hd1 hκ0 hκ1
    hZ hB ca cb cc cd ce cf cg cF1 cF2 cF3
  -- opaque names for the exponents and the parameters
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = κ * (1 - d) / 64 := ⟨_, rfl⟩
  obtain ⟨cs, hcsdef⟩ : ∃ cs : ℝ, cs = κ * (1 - d) / 1000 := ⟨_, rfl⟩
  obtain ⟨cK, hcKdef⟩ : ∃ cK : ℝ, cK = 2 ^ (D + 1) * (((D + 1) ^ 2 : ℕ) : ℝ) + 5 := ⟨_, rfl⟩
  rw [← hbdef] at hangb cc ce cf cF2
  rw [← hcsdef] at cF1 cF2 cF3
  rw [← hcKdef] at ce cf cF2
  have hX0 : 0 < X := by linarith only [hX2]
  have hX1 : 1 ≤ X := by linarith only [hX2]
  have hY0 : 0 < Y := by linarith only [hY1]
  have h1d : 0 < 1 - d := by linarith only [hd1]
  have hb0 : 0 < b := by rw [hbdef]; positivity
  have hcK0 : 0 ≤ cK := by rw [hcKdef]; positivity
  obtain ⟨lam, hlamdef⟩ : ∃ x : ℝ, x = 2 * Y := ⟨_, rfl⟩
  obtain ⟨K₁, hK₁def⟩ : ∃ x : ℝ, x = 64 * Y := ⟨_, rfl⟩
  obtain ⟨δs, hδsdef⟩ : ∃ x : ℝ, x = X ^ (-B) := ⟨_, rfl⟩
  obtain ⟨ξ, hξdef⟩ : ∃ x : ℝ, x = X ^ (-Z) := ⟨_, rfl⟩
  obtain ⟨δv, hδvdef⟩ : ∃ x : ℝ, x = X ^ (-(Z + 1)) := ⟨_, rfl⟩
  obtain ⟨δb, hδbdef⟩ : ∃ x : ℝ, x = X ^ (-b) := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ x : ℝ, x = δb / 2 := ⟨_, rfl⟩
  obtain ⟨pang, hpangdef⟩ : ∃ x : ℝ, x = Y * X ^ (-S * b) := ⟨_, rfl⟩
  obtain ⟨εT, hεTdef⟩ : ∃ x : ℝ, x = Y * X ^ (-1 : ℝ) * h ^ (-(3 : ℝ) / 4) := ⟨_, rfl⟩
  obtain ⟨w₁, hw₁def⟩ : ∃ x : ℝ, x = X ^ (-1 : ℝ) * h ^ ((1 : ℝ) / 8) := ⟨_, rfl⟩
  obtain ⟨Jb, hJbdef⟩ : ∃ x : ℝ, x = Y * X ^ (2 * Z) * (X ^ (-1 : ℝ) / w₁) ^ d := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ x : ℝ,
      x = lam ^ (D + 1) * ((((D + 1) ^ 2 : ℕ) : ℝ) * Y) + 2 * Y + 2 * X ^ b + 1 := ⟨_, rfl⟩
  rw [← hεTdef] at hfield
  rw [← hw₁def, ← hξdef] at hJfin hJcard
  rw [← hJbdef] at hJcard
  rw [← hξdef] at hcell
  rw [← hδsdef, ← hδvdef] at hpalv
  rw [← hδbdef, ← hpangdef] at hangb
  -- elementary facts about the parameters
  have hlam1 : 1 ≤ lam := by rw [hlamdef]; linarith only [hY1]
  have hlamY : 2 * Y ≤ lam := by rw [hlamdef]
  have hδs0 : 0 < δs := by rw [hδsdef]; exact Real.rpow_pos_of_pos hX0 _
  have hδs1 : δs ≤ 1 := by
    rw [hδsdef]; exact Real.rpow_le_one_of_one_le_of_nonpos hX1 (by linarith only [hZ, hB])
  have hξ0 : 0 < ξ := by rw [hξdef]; exact Real.rpow_pos_of_pos hX0 _
  have hξ1 : ξ ≤ 1 := by
    rw [hξdef]; exact Real.rpow_le_one_of_one_le_of_nonpos hX1 (by linarith only [hZ])
  have hδv0 : 0 < δv := by rw [hδvdef]; exact Real.rpow_pos_of_pos hX0 _
  have hδb0 : 0 < δb := by rw [hδbdef]; exact Real.rpow_pos_of_pos hX0 _
  have hb1 : b ≤ Z + 1 := by
    rw [hbdef]
    have : κ * (1 - d) ≤ 1 := by nlinarith
    linarith only [this, hZ]
  have hδvb : δv ≤ δb := by
    rw [hδvdef, hδbdef]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith only [hb1])
  have hδvξ : δv ≤ ξ := by
    rw [hδvdef, hξdef]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith only)
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hrδ : r + δv / 2 ≤ δb := by rw [hrdef]; linarith only [hδvb]
  have hpang0 : 0 ≤ pang := by rw [hpangdef]; positivity
  have hεT0 : 0 ≤ εT := by rw [hεTdef]; positivity
  have hw₁0 : 0 < w₁ := by rw [hw₁def]; positivity
  have hξlam : ξ / lam ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith only [hlam1]), hlamdef]
    linarith only [hξ1, hY1]
  have hXb : 0 < X ^ b := Real.rpow_pos_of_pos hX0 _
  have hKfield : lam ^ (D + 1) * ((((D + 1) ^ 2 : ℕ) : ℝ) * Y) ≤ K := by
    rw [hKdef]; linarith only [hY1, hXb]
  have hδv1 : δv ≤ 1 := hδvξ.trans hξ1
  have hKv : Y + δv ≤ K := by
    have : 0 ≤ lam ^ (D + 1) * ((((D + 1) ^ 2 : ℕ) : ℝ) * Y) := by positivity
    rw [hKdef]; linarith only [this, hY1, hXb, hδv1]
  have hKr : 1 / r ≤ K := by
    have hinv : 1 / r = 2 * X ^ b := by
      rw [hrdef, hδbdef, Real.rpow_neg hX0.le]
      field_simp
    rw [hinv]
    have : 0 ≤ lam ^ (D + 1) * ((((D + 1) ^ 2 : ℕ) : ℝ) * Y) := by positivity
    rw [hKdef]; linarith only [this, hY1]
  have hK1 : 1 ≤ K := by
    have : 0 ≤ lam ^ (D + 1) * ((((D + 1) ^ 2 : ℕ) : ℝ) * Y) := by positivity
    rw [hKdef]; linarith only [this, hY1, hXb]
  -- switch errors are below the velocity rounding width
  have hsw' := switch_error_le hX2 hY1 hh0 hhlo hlam1 ca
  have hsw : max ((Y + 1) * δs / (h * lam)) ((4 * Y + 1) * δs / h) ≤ δv := by
    rw [hδsdef, hδvdef]; exact hsw'
  have hXZ : 32 ≤ X ^ Z := by simpa using cg
  have hδvsmall : δv ≤ 1 / 32 := by
    have h2 : ξ = (X ^ Z)⁻¹ := by rw [hξdef]; exact Real.rpow_neg hX0.le Z
    have h3 : (X ^ Z)⁻¹ ≤ 1 / 32 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hXZ
    linarith only [hδvξ, h2, h3]
  have hc1 : 4 * max ((Y + 1) * δs / (h * lam)) ((4 * Y + 1) * δs / h) + 4 * (δv / 2) ≤ 1 / 2 := by
    linarith only [hsw, hδvsmall]
  have hc2 : 4 * (Y / K₁) + 4 * (Y * (3 * pang)) ≤ 1 / 2 := by
    have h1 : Y / K₁ = 1 / 64 := by rw [hK₁def]; field_simp
    have h2 : 12 * (Y * pang) ≤ 1 / 4 := by
      have hneg : X ^ (-S * b) = (X ^ (S * b))⁻¹ := by
        rw [show -S * b = -(S * b) by ring]
        exact Real.rpow_neg hX0.le _
      have hpos : 0 < X ^ (S * b) := Real.rpow_pos_of_pos hX0 _
      rw [hpangdef, hneg]
      rw [show 12 * (Y * (Y * (X ^ (S * b))⁻¹)) = 12 * Y ^ 2 / X ^ (S * b) by ring]
      rw [div_le_iff₀ hpos]
      linarith only [cc]
    rw [h1]
    linarith only [h2]
  have hcell' : ∀ q : Fin 2 → ℤ, μ {p | (fun i => ⌊ubase z₀ h p.1 p.2 i / ξ⌋) = q} ≤
      ENNReal.ofReal (Y * h * ξ ^ 2) * νg Ag := by
    intro q
    have hξ2 : ξ ^ 2 = X ^ (-2 * Z) := by
      rw [hξdef, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
      congr 1
      push_cast
      ring
    rw [hξ2]
    exact hcell q
  have hBc := hcurl νg πg μ Ag t₀ h z₀ 𝒯 Y K₁ lam δs δv δb r pang εT ξ w₁ Jb K hA hbdd hh0
    hblock hμdom hμsupp hμmass hμpos hu hcell' hpalv hangb h𝒯deg h𝒯coeff hfield hJfin hJcard
    hY1 (by rw [hK₁def]; linarith only [hY1]) hlamY hlam1 hδs0 hδs1 hδv0 hδb0 hr0 hrδ hpang0
    hεT0 hξ0 hξlam hw₁0 hKfield hKv hKr hK1 hc1 hc2
  -- name the curl bound
  obtain ⟨bsw, hbswdef⟩ : ∃ x : ℝ, x = max ((Y + 1) * δs / (h * lam)) ((4 * Y + 1) * δs / h) :=
    ⟨_, rfl⟩
  rw [← hbswdef] at hBc hsw
  obtain ⟨ρE, hρEdef⟩ : ∃ x : ℝ, x = ξ / (2 * lam) + (4 * bsw + 4 * (δv / 2)) := ⟨_, rfl⟩
  rw [← hρEdef] at hBc
  obtain ⟨ε, hεdef⟩ : ∃ x : ℝ, x = w₁ / (2 * h) + (4 * (lam * εT + (1 + K) * (2 * Ccurl * K) *
      (4 * bsw + 4 * (δv / 2)) + K * (δv / 2)) + 3 * bsw) + bsw := ⟨_, rfl⟩
  rw [← hεdef] at hBc
  obtain ⟨KP, hKPdef⟩ : ∃ x : ℝ,
      x = lam ^ (D + 2) * ((((D + 1) ^ 2 : ℕ) : ℝ) * (2 * (((D : ℝ) + 1) * Y))) := ⟨_, rfl⟩
  rw [← hKPdef] at hBc
  obtain ⟨L, hLdef⟩ : ∃ x : ℝ, x = (Y * (Y * K₁)) ^ 4 * lam ^ 4 := ⟨_, rfl⟩
  rw [← hLdef] at hBc
  obtain ⟨M, hMdef⟩ : ∃ x : ℝ, x = Y ^ 2 * lam ^ 2 := ⟨_, rfl⟩
  rw [← hMdef] at hBc
  obtain ⟨Bc, hBcdef⟩ : ∃ x : ℝ, x = Ccurl * K ^ 4 * L ^ (6 * D + 1) * M ^ (2 * D) *
      (Jb * (2 * ρE) ^ 2) * ε / (1 / 2) ^ (6 * D + 1) +
      Ccurl * KP * (ξ / lam) * L ^ (2 * D) * M ^ (2 * D) / (1 / 2) ^ (2 * D) := ⟨_, rfl⟩
  rw [← hBcdef] at hBc
  -- simplified factors
  have hbsw0 : 0 ≤ bsw := by rw [hbswdef]; exact le_max_of_le_right (by positivity)
  have hρE0 : 0 ≤ ρE := by rw [hρEdef]; positivity
  have hρE : ρE ≤ ξ / lam := by
    rw [hρEdef]
    exact rhoE_le hX0 hY0 hδvdef hξdef hlamdef hsw (by simpa using cb)
  have hKle : K ≤ cK * Y ^ (D + 2) * X ^ b := by
    rw [hKdef, hcKdef, hlamdef]; exact K_le_bound hX1 hY1 hb0.le
  have hεle : ε ≤ w₁ / h := by
    rw [hεdef]
    exact epsilon_le hX0 hY1 hh0 hh1 hhhi hlamdef hεTdef hw₁def hbsw0 hsw hδvdef hK1 hKle
      hCcurl.le hcK0 cd ce cf cg
  -- the potential
  obtain ⟨Kpot, hKpotdef⟩ : ∃ x : ℝ, x = lam ^ (D + 1) * ((((D + 1) ^ 2 : ℕ) : ℝ) * Y) :=
    ⟨_, rfl⟩
  have hBc0 : 0 ≤ Bc := (abs_nonneg _).trans (hBc 0)
  obtain ⟨P, hPdeg, hPcoeff, hPsup, hPvar⟩ := hpot 𝒯 z₀ t₀ h lam Y εT Bc Kpot h𝒯deg h𝒯coeff
    hh0 hlam1 hY0.le hlamY hεT0 hBc0 hKpotdef.ge hBc
  -- the residual variation is a power below `N^{-1}`
  have hLeq : L = 2 ^ 28 * Y ^ 16 := by rw [hLdef, hK₁def, hlamdef]; ring
  have hMeq : M = 4 * Y ^ 4 := by rw [hMdef, hlamdef]; ring
  have hJA0 : 0 ≤ Jb * (2 * ρE) ^ 2 := by
    have : 0 ≤ Jb := by
      rw [hJbdef]
      have : 0 ≤ X ^ (-1 : ℝ) / w₁ := by positivity
      exact mul_nonneg (by positivity) (Real.rpow_nonneg this _)
    positivity
  have hε0 : 0 ≤ ε := by rw [hεdef]; positivity
  have hw₁h : w₁ / h = X ^ (-1 : ℝ) * h ^ (-(7 : ℝ) / 8) := by
    rw [hw₁def]
    have h1 := Real.rpow_add hh0 ((1 : ℝ) / 8) (-1)
    rw [Real.rpow_neg_one] at h1
    rw [show (1 : ℝ) / 8 + -1 = -(7 : ℝ) / 8 by norm_num] at h1
    rw [h1]
    field_simp
  have hεle' : ε ≤ X ^ (-1 : ℝ) * h ^ (-(7 : ℝ) / 8) := hεle.trans hw₁h.le
  have hKPeq : KP = 2 ^ (D + 2) * ((((D + 1) ^ 2 : ℕ) : ℝ) * (2 * ((D : ℝ) + 1))) *
      Y ^ (D + 3) := by
    rw [hKPdef, hlamdef, mul_pow, show D + 3 = (D + 2) + 1 by ring, pow_succ Y (D + 2)]
    ring
  have hξl0 : 0 ≤ ξ / lam := by positivity
  have hξl : ξ / lam ≤ X ^ (-Z) := by rw [← hξdef]; exact div_le_self hξ0.le hlam1
  have hJA : Jb * (2 * ρE) ^ 2 ≤ h ^ (-d / 8) := by
    rw [hJbdef]; exact Jb_area_le hX0 hY1 hh0 hξdef hlamdef hρE0 hρE hw₁def
  have hfin := final_variation_le (D := D) (b := b) (cs := cs) hX0 hY1 hh0 hh1 hhhi hd0 hd1
    hCcurl.le hcK0 (by linarith only [hK1]) hKle hLeq hMeq hJA0 hJA hε0 hεle' hKPeq hξl0 hξl
    hlam1 rfl rfl rfl rfl cF2 cF3
  have hepsT := h_mul_epsT_le hX0 hY1 hh0 hhhi (cs := cs) cF1
  have hVar : h * (εT + ((((D + 1) ^ 2 : ℕ) : ℝ) * Bc) / lam) ≤ X ^ (-1 - 2 * cs) := by
    have hsplit : h * (εT + ((((D + 1) ^ 2 : ℕ) : ℝ) * Bc) / lam) =
        h * εT + h * ((((D + 1) ^ 2 : ℕ) : ℝ) * Bc / lam) := by ring
    rw [hsplit, hεTdef]
    rw [hBcdef]
    calc
      _ ≤ X ^ (-1 - 2 * cs) / 3 + 2 * (X ^ (-1 - 2 * cs) / 3) := add_le_add hepsT hfin
      _ = X ^ (-1 - 2 * cs) := by ring
  -- output
  have h2Kpot : 2 * Kpot = 2 ^ (D + 2) * (((D + 1) ^ 2 : ℕ) : ℝ) * Y ^ (D + 2) := by
    rw [hKpotdef, hlamdef, mul_pow, show D + 2 = (D + 1) + 1 by ring, pow_succ Y (D + 1),
      pow_succ (2 : ℝ) (D + 1)]
    ring
  have hKc : h * (2 * Kpot) ≤ 2 ^ (D + 2) * (((D + 1) ^ 2 : ℕ) : ℝ) * Y ^ (D + 2) := by
    rw [← h2Kpot]
    have : 0 ≤ 2 * Kpot := by rw [h2Kpot]; positivity
    exact mul_le_of_le_one_left this hh1
  refine ⟨P, h * (2 * Kpot), hPdeg, hPcoeff, ?_, hKc, ?_⟩
  · intro v hv
    exact hPsup v (fun i => (hv i).trans (by linarith only [hlamY, hY1]))
  · intro l hul hfl t ht
    rw [← hcsdef]
    refine (hPvar l hul (fun t ht => ?_) t ht).trans hVar
    rw [hεTdef]
    exact hfl t ht

end Submission.Obl.k4_scalar_capped_heavy_potential.Cons
