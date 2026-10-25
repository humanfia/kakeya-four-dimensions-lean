import Submission.Obl.k4_scalar_coefficient_clustering.Plank

namespace Submission.Obl.k4_scalar_coefficient_clustering

noncomputable section

def normalizedBase (R : ℝ) (a : Coeff) (s : ℝ) : Plane := R⁻¹ • liftBase a s
def normalizedSlope (R : ℝ) (a : Coeff) (s : ℝ) : Plane := R⁻¹ • liftSlope a s

theorem normalized_lift_bounds {a : Coeff} {B R s : ℝ} (ha : ‖a‖ ≤ B)
    (hB : 1 ≤ B) (hR : 3 * B ≤ R) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖normalizedBase R a s‖ ≤ 1 ∧ ‖normalizedSlope R a s‖ ≤ 1 := by
  have hRpos : 0 < R := by linarith
  have hh := lift_norm_bounds ha hB hs
  have hb : ‖liftBase a s‖ / R ≤ 1 := (div_le_one hRpos).mpr (by linarith [hh.1])
  have hu : ‖liftSlope a s‖ / R ≤ 1 := (div_le_one hRpos).mpr (by linarith [hh.2])
  simpa only [normalizedBase, normalizedSlope, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hRpos, div_eq_mul_inv, mul_comm] using And.intro hb hu

theorem normalized_lift_scalar (R : ℝ) (a : Coeff) (s t : ℝ) :
    (normalizedBase R a s + t • normalizedSlope R a s) 0 +
      t * (normalizedBase R a s + t • normalizedSlope R a s) 1 = R⁻¹ * quadratic a t := by
  simp [normalizedBase, normalizedSlope, liftBase, liftSlope, quadratic,
    PiLp.add_apply, PiLp.smul_apply]
  ring

theorem raw_plank_of_normalized {D : ℕ} {R s α : ℝ} (hR : 0 < R)
    {a : Coeff} {c w e : Plane}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |inner ℝ (normalizedBase R a s + t • normalizedSlope R a s - c - t • w) e| ≤ α / (D : ℝ)) :
    InNarrowPlank (R • c) (R • w) e (R * α / (D : ℝ)) a s := by
  intro t ht
  have heq : liftTrace a s t - R • c - t • R • w =
      R • (normalizedBase R a s + t • normalizedSlope R a s - c - t • w) := by
    simp only [normalizedBase, normalizedSlope, smul_sub, smul_add, smul_smul,
      mul_inv_cancel₀ hR.ne', one_smul]
    rw [show R * (t * R⁻¹) = t by field_simp]
    simp only [liftTrace]
    module
  rw [heq, real_inner_smul_left, abs_mul, abs_of_pos hR]
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (h t ht) hR.le

/-- The two coefficient bounds, on opposite sides of the cutoff, give a uniform plank cap. -/
theorem lifted_plank_cap {D n : ℕ} (hD : 1 ≤ D) {R p K H Λ d : ℝ}
    (hR : 1 ≤ R) (hp : 0 < p) (hK : 0 ≤ K) (hH : 0 ≤ H) (hΛ : 1 ≤ Λ)
    (hd : d < 1) (hmesh : p ≤ 2 * R / (D : ℝ))
    (a : Fin n → Coeff) (ω : Fin n → ℝ) (hω : ∀ i, 0 ≤ ω i)
    (hsmall : ∀ i, ω i ≤ H) (hinj : Function.Injective (coefficientCode p ∘ a))
    (hcluster : ∀ v : ℝ, p ≤ 2 * v → ∀ T : Finset (Fin n),
      (∀ i ∈ T, ∀ j ∈ T, ‖a i - a j‖ ≤ 24 * v) → ∑ i ∈ T, ω i ≤ 32 * K * v ^ d) :
    PlankCap D
      (fun q : Fin n × Fin D => normalizedBase R (a q.1) (((q.2 : ℕ) : ℝ) / (D : ℝ)))
      (fun q : Fin n × Fin D => normalizedSlope R (a q.1) (((q.2 : ℕ) : ℝ) / (D : ℝ)))
      (fun q => ω q.1 / (D : ℝ))
      (5000000 * (R / (D : ℝ)) ^ 2 * (K * (p * Λ) ^ (d - 1) + Λ ^ 3 * H / p)) := by
  classical
  intro c w e₁ e₂ α β he₁ he₂ ho hα hαβ hβ S hS
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hRpos : 0 < R := by linarith
  let U : ℝ := R * α / (D : ℝ)
  let V : ℝ := R * β / (D : ℝ)
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 < V := by
    have hb : 0 < β := by linarith
    dsimp [V]
    positivity
  have hpV : p ≤ 2 * V := by
    have hb : 1 ≤ β := hα.trans hαβ
    have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ R / (D : ℝ))
    calc
      p ≤ 2 * (R / (D : ℝ)) := by convert hmesh using 1 <;> ring
      _ ≤ 2 * ((R / (D : ℝ)) * β) := by linarith
      _ = 2 * V := by dsimp [V]; ring
  have hraw : ∀ q ∈ S, InPlank (R • c) (R • w) e₁ e₂ U V
      (a q.1) (((q.2 : ℕ) : ℝ) / (D : ℝ)) := by
    intro q hq
    exact ⟨raw_plank_of_normalized hRpos (fun t ht => (hS q hq t ht).1),
      raw_plank_of_normalized hRpos (fun t ht => (hS q hq t ht).2)⟩
  let T := S.image Prod.fst
  have hsum := sum_plank_dummy_bound hD hR hα hαβ a ω hω he₁ he₂ ho S hraw
  have hdiam := plank_coefficient_diameter hD hRpos.le hαβ a he₁ he₂ ho S hraw
  have hsum' : (∑ q ∈ S, ω q.1 / (D : ℝ)) ≤ 18 * U * ∑ i ∈ T, ω i := by
    convert hsum using 1 <;> dsimp [U, T] <;> ring
  have hcore : (∑ i ∈ T, ω i) ≤
      250000 * V * (K * (p * Λ) ^ (d - 1) + Λ ^ 3 * H / p) := by
    by_cases hcut : V ≤ p * Λ
    · have hc := card_coefficient_codes T a hp (by positivity : 0 ≤ 24 * V) hdiam
      rw [Finset.card_image_of_injOn hinj.injOn] at hc
      have hdiv : 48 * V / p + 2 ≤ 50 * Λ := by
        have heq : V / p ≤ Λ := (div_le_iff₀ hp).mpr (by nlinarith [hcut])
        calc
          48 * V / p + 2 = 48 * (V / p) + 2 := by ring
          _ ≤ 48 * Λ + 2 := by linarith
          _ ≤ _ := by linarith
      have hc' : (T.card : ℝ) ≤ 125000 * Λ ^ 3 := by
        have hdiv' : 2 * (24 * V) / p + 2 ≤ 50 * Λ := by convert hdiv using 1 <;> ring
        have hpw := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * (24 * V) / p + 2) hdiv' 3
        nlinarith
      have hwt : (∑ i ∈ T, ω i) ≤ 125000 * Λ ^ 3 * H := by
        calc
          _ ≤ ∑ _i ∈ T, H := Finset.sum_le_sum (fun i _ => hsmall i)
          _ = (T.card : ℝ) * H := by simp
          _ ≤ _ := mul_le_mul_of_nonneg_right hc' hH
      have hratio : 1 ≤ 2 * V / p := (le_div_iff₀ hp).mpr (by linarith)
      have hnonneg : 0 ≤ K * (p * Λ) ^ (d - 1) := by positivity
      have hm := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 125000 * Λ ^ 3 * H)
      have hs0 : 0 ≤ 250000 * V * (K * (p * Λ) ^ (d - 1)) := by positivity
      have heq : 125000 * Λ ^ 3 * H * (2 * V / p) = 250000 * V * (Λ ^ 3 * H / p) := by ring
      rw [heq] at hm
      nlinarith
    · have hcl := hcluster V hpV T hdiam
      have hpow : V ^ (d - 1) ≤ (p * Λ) ^ (d - 1) := by
        exact Real.rpow_le_rpow_of_nonpos (by positivity) (le_of_not_ge hcut) (by linarith)
      have heq : V ^ d = V * V ^ (d - 1) := by
        calc
          V ^ d = V ^ (1 + (d - 1)) := by congr 1; ring
          _ = V ^ (1 : ℝ) * V ^ (d - 1) := Real.rpow_add hV _ _
          _ = _ := by rw [Real.rpow_one]
      rw [heq] at hcl
      have hm := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 32 * K * V)
      have hnonneg : 0 ≤ V * (Λ ^ 3 * H / p) := by positivity
      have hnonneg' : 0 ≤ V * (K * (p * Λ) ^ (d - 1)) := by positivity
      nlinarith
  have hnonneg : 0 ≤ K * (p * Λ) ^ (d - 1) + Λ ^ 3 * H / p := by positivity
  calc
    _ ≤ 18 * U * (250000 * V * (K * (p * Λ) ^ (d - 1) + Λ ^ 3 * H / p)) :=
      hsum'.trans (mul_le_mul_of_nonneg_left hcore (by positivity))
    _ ≤ 5000000 * U * V * (K * (p * Λ) ^ (d - 1) + Λ ^ 3 * H / p) := by
      nlinarith [mul_nonneg (mul_nonneg hU hV.le) hnonneg]
    _ = _ := by dsimp [U, V]; ring

end
end Submission.Obl.k4_scalar_coefficient_clustering
