import Submission.Obl.k4_scalar_grid_parameter_preparation.GlobalDeficiency
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/-! Power-small original deficiency mass, uniformly over compact depth ranges. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory Filter
open scoped Classical ENNReal

theorem original_coefficient_deficiency_power_bound {X : Type} [MeasurableSpace X]
    (N K : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : (∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (W : ℕ → ℕ) (a : X → Fin 5 → ℝ) (ha : Measurable a)
    (θ : (k : ℕ) → Fin (W k) → Measure X)
    (μ : (k : ℕ) → Fin (W k) → Measure (X × ℝ))
    (π : (k : ℕ) → Fin (W k) → Measure ℝ)
    (A : (k : ℕ) → Fin (W k) → Set (X × ℝ)) (Γ : ℕ → Finset ℝ)
    (d : ℝ) (hd : 0 ≤ d) (hd₁ : d < 1)
    (hμ : ∀ k g, IsFiniteMeasure (μ k g)) (hθ : ∀ k g, SFinite (θ k g))
    (hπ : ∀ k g, IsProbabilityMeasure (π k g))
    (hbounded : ∀ k g, ∀ᵐ l ∂θ k g, ∀ e, |a l e| ≤ K k)
    (hA : ∀ k g, MeasurableSet (A k g) ∧
      ∀ z ∈ A k g, z.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |a z.1 e| ≤ K k)
    (hdom : ∀ k g,
      (μ k g).restrict (A k g) ≤ ENNReal.ofReal (K k) • (θ k g).prod volume ∧
      ENNReal.ofReal ((K k)⁻¹) • ((θ k g).prod volume).restrict (A k g) ≤
        (μ k g).restrict (A k g))
    (hstage : ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ (g : Fin (W k)) (r : ℝ),
      R⁻¹ ≤ r → r ≤ R → r ∈ Γ k →
      (physicalScalarGridTag (N k ^ (-r)) '' (scalarPacketPosition a '' A k g)).Finite ∧
      ∀ z ∈ A k g,
        ENNReal.ofReal (N k ^ (-((2 + d) * r)) / K k) *
          π k g (scalarVelocityBin (N k ^ (-r)) ⌊a z.1 1 / N k ^ (-r)⌋) ≤
          μ k g (A k g ∩ {z' | physicalScalarGridTag (N k ^ (-r)) (scalarPacketPosition a z') =
            physicalScalarGridTag (N k ^ (-r)) (scalarPacketPosition a z) ∧
            a z'.1 1 ∈ scalarVelocityBin (N k ^ (-r)) ⌊a z.1 1 / N k ^ (-r)⌋}))
    (hmixed : ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ (g : Fin (W k)) (r s : ℝ),
      R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → ∀ z : Fin 5 → ℤ,
        θ k g {l | scalarMixedCoefficientTag (N k ^ (-r)) (N k ^ (-s)) (a l) = z} ≤
          ENNReal.ofReal (K k * N k ^ (-r - d * s)) *
            π k g (scalarVelocityBin (N k ^ (-r)) (z 1))) :
    ∀ ε R : ℝ, 0 < ε → 1 < R → ∃ κ : ℝ, 0 < κ ∧
      ∀ᶠ k in atTop, ∀ (g : Fin (W k)) (r : ℝ), R⁻¹ ≤ r → r ≤ R → r ∈ Γ k →
        μ k g {z | z ∈ A k g ∧
          z.1 ∈ scalarLightCoefficientSet (θ k g) a (π k g) (N k ^ (-r)) d (N k ^ (-ε))} ≤
            ENNReal.ofReal (N k ^ (-κ)) := by
  intro ε R hε hR
  obtain ⟨η,hη,N₀,hN₀,hcore⟩ := deficient_coefficient_mass d ε R hd hd₁ hε hR.le
  let t := min (η / 100) (1 / (2 * R))
  have hRp : 0 < R := by linarith
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  have htη : t ≤ η / 100 := min_le_left _ _
  have htR : t ≤ R⁻¹ := by
    apply (min_le_right _ _).trans
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le hRp (by linarith)
  have hgap : 0 < η - 3 * t := by linarith
  let R' := max (R + 1) (t⁻¹ + 1)
  have hRR' : R ≤ R' := (by linarith : R ≤ R + 1).trans (le_max_left _ _)
  have hR' : 1 < R' := (by linarith : 1 < R + 1).trans_le (le_max_left _ _)
  have hR'p : 0 < R' := by linarith
  have hR't : R'⁻¹ ≤ t := by
    have hh : t⁻¹ ≤ R' := (by linarith : t⁻¹ ≤ t⁻¹ + 1).trans (le_max_right _ _)
    have hi := one_div_le_one_div_of_le (inv_pos.mpr ht) hh
    simpa only [one_div,inv_inv] using hi
  have hR'R : R'⁻¹ ≤ R⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hRp hRR'
  have hN₁ (k) : 1 ≤ N k := by linarith [hN k]
  have hpoly := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN₁ hNt hK.1 hK.2 7 (a := 0) (b := η - 3 * t) hgap (A := 3888) (by norm_num)
  have hnorm := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN₁ hNt hK.1 hK.2 1 (a := 0) (b := η) hη (A := 3) (by norm_num)
  have hfinal := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN₁ hNt hK.1 hK.2 2 (a := 0) (b := η / 2) (by positivity) (A := 6) (by norm_num)
  refine ⟨η / 2,by positivity,?_⟩
  filter_upwards [hNt.eventually_ge_atTop N₀,hpoly,hnorm,hfinal,hstage R hR,hmixed R' hR']
    with k hk hp hn hf hst hmx
  intro g r hr hr' hrΓ
  letI : IsFiniteMeasure (μ k g) := hμ k g
  letI : SFinite (θ k g) := hθ k g
  letI : IsProbabilityMeasure (π k g) := hπ k g
  have hNp : 0 < N k := by linarith [hN k]
  have hNgt : 1 < N k := by linarith [hN k]
  have hKp : 0 < K k := zero_lt_one.trans_le (hK.1 k)
  have hK₀ : 0 ≤ K k := hKp.le
  have hp' : 3888 * K k ^ 7 ≤ N k ^ (η - 3 * t) := by
    simpa only [Real.rpow_zero,mul_one] using hp.le
  have hn' : 3 * K k ≤ N k ^ η := by
    simpa only [pow_one,Real.rpow_zero,mul_one] using hn.le
  have hf' : 6 * K k ^ 2 ≤ N k ^ (η / 2) := by
    simpa only [Real.rpow_zero,mul_one] using hf.le
  let ξ := N k ^ (-r)
  let σ := N k ^ (-t)
  let Q := (6 * K k / σ) ^ 3 * K k
  have hξ : 0 < ξ := Real.rpow_pos_of_pos hNp _
  have hσ : 0 < σ := Real.rpow_pos_of_pos hNp _
  have hξσ : ξ ≤ σ := Real.rpow_le_rpow_of_exponent_le (hN₁ k) (by linarith [htR])
  have hσ₁ : σ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (hN₁ k) (by linarith)
  have hσinv : σ⁻¹ = N k ^ t := by
    dsimp only [σ]
    rw [Real.rpow_neg hNp.le,inv_inv]
  have hQeq : Q = 216 * K k ^ 4 * N k ^ (3 * t) := by
    calc
      _ = 216 * K k ^ 4 * (σ⁻¹) ^ 3 := by dsimp only [Q]; ring
      _ = _ := by
        rw [hσinv,← Real.rpow_natCast (N k ^ t) 3,← Real.rpow_mul hNp.le]
        congr 2
        ring
  have hcoeff : K k ^ 2 * (4 * (K k + 3) + 2) * Q ≤ N k ^ η := by
    calc
      _ ≤ K k ^ 2 * (18 * K k) * Q := by
        gcongr
        linarith [hK.1 k]
      _ = (3888 * K k ^ 7) * N k ^ (3 * t) := by rw [hQeq]; ring
      _ ≤ N k ^ (η - 3 * t) * N k ^ (3 * t) :=
        mul_le_mul_of_nonneg_right hp' (Real.rpow_nonneg hNp.le _)
      _ = _ := by rw [← Real.rpow_add hNp]; congr 1; ring
  have hQbound : Q ≤ N k ^ η := by
    apply le_trans ?_ hcoeff
    have hfac : 1 ≤ K k ^ 2 * (4 * (K k + 3) + 2) := by
      have hpow : 1 ≤ K k ^ 2 := one_le_pow₀ (hK.1 k)
      nlinarith [hK.1 k]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hfac (by dsimp only [Q]; positivity)
  have hpower : ξ / N k ^ (-((2 + d) * r)) = ξ ^ (-1 - d) := by
    dsimp only [ξ]
    rw [div_eq_mul_inv,← Real.rpow_neg hNp.le,← Real.rpow_add hNp,← Real.rpow_mul hNp.le]
    congr 1
    ring
  have hsize :
      (K k * (4 * (K k + 3) + 2) * (Q * ξ)) / (N k ^ (-((2 + d) * r)) / K k) ≤
        N k ^ η * ξ ^ (-1 - d) := by
    have heq :
        (K k * (4 * (K k + 3) + 2) * (Q * ξ)) / (N k ^ (-((2 + d) * r)) / K k) =
          (K k ^ 2 * (4 * (K k + 3) + 2) * Q) * (ξ / N k ^ (-((2 + d) * r))) := by
      field_simp [hKp.ne',(Real.rpow_pos_of_pos hNp (-((2 + d) * r))).ne']
      <;> ring
    rw [heq,hpower]
    exact mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hξ.le _)
  have hcap (ζ : ℝ) (hζ : ξ ≤ ζ) (hζσ : ζ ≤ σ) (z : Fin 5 → ℤ) :
      θ k g {l | scalarMixedCoefficientTag ξ ζ (a l) = z} ≤
        ENNReal.ofReal (K k * ξ * ζ ^ d) * π k g (scalarVelocityBin ξ (z 1)) := by
    let b := -Real.logb (N k) ζ
    have hζp : 0 < ζ := hξ.trans_le hζ
    have hbpow : N k ^ (-b) = ζ := by
      dsimp only [b]
      rw [neg_neg]
      exact Real.rpow_logb hNp hNgt.ne' hζp
    have htb : t ≤ b := by
      have hh : N k ^ (-b) ≤ N k ^ (-t) := by rw [hbpow]; exact hζσ
      have hh' := (Real.rpow_le_rpow_left_iff hNgt).mp hh
      linarith
    have hbr : b ≤ r := by
      have hh : N k ^ (-r) ≤ N k ^ (-b) := by rw [hbpow]; exact hζ
      have hh' := (Real.rpow_le_rpow_left_iff hNgt).mp hh
      linarith
    have hh := hmx g r b (hR'R.trans hr) (hr'.trans hRR')
      (hR't.trans htb) (hbr.trans (hr'.trans hRR')) z
    have heq : N k ^ (-r - d * b) = ξ * ζ ^ d := by
      rw [← hbpow]
      dsimp only [ξ]
      rw [← Real.rpow_mul hNp.le,← Real.rpow_add hNp]
      congr 1
      ring
    simpa only [hbpow,heq,← mul_assoc] using hh
  have hsmall := hcore (N k) hk r hr hr' X (μ k g) (θ k g) (π k g) a ha (A k g)
    (hA k g).1 (K k) (K k) (K k) σ (N k ^ (-((2 + d) * r)) / K k) (K k)⁻¹
    (hK.1 k) hK₀ hK₀ hσ hξσ hσ₁ (by positivity) (inv_pos.mpr hKp)
    (hbounded k g) (hA k g).2 (hdom k g).1 (hdom k g).2
    (hst g r hr hr' hrΓ).1 (hst g r hr hr' hrΓ).2 hcap hn' hQbound hsize
  apply hsmall.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    6 * K k * K k * N k ^ (-η) = (6 * K k ^ 2) * N k ^ (-η) := by ring
    _ ≤ N k ^ (η / 2) * N k ^ (-η) := mul_le_mul_of_nonneg_right hf' (Real.rpow_nonneg hNp.le _)
    _ = _ := by rw [← Real.rpow_add hNp]; congr 1; ring

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
