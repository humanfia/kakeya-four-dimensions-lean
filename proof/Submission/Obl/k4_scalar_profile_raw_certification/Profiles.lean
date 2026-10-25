import Submission.Obl.k4_profile_density_bounds.Mass
import Submission.Obl.k4_profile_density_bounds.Asymptotics

open MeasureTheory Set Filter
open scoped ENNReal

namespace Submission.Obl.k4_scalar_profile_raw_certification

/-- A fixed representative has a power-small exceptional set at every tolerance. -/
def PowerWindow {X : Type*} [MeasurableSpace X] (N : ℕ → ℝ)
    (μ : ℕ → Measure X) (h : ℕ → X → ENNReal) (e : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
    μ k {p | h k p < ENNReal.ofReal (N k ^ (-e - τ)) ∨
      ENNReal.ofReal (N k ^ (-e + τ)) < h k p} ≤ ENNReal.ofReal (N k ^ (-c))

/-- A raw ceiling transfers to any chosen density of a dominated law. -/
lemma observed_density_le_of_domination {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (ρ : Measure Y) [SigmaFinite ρ]
    {μ ν : Measure X} (hdom : ν ≤ μ) {f : X → Y} (hf : Measurable f)
    {g G : Y → ENNReal} (hg : Measurable g)
    (hν : ν.map f = ρ.withDensity g) (hμ : μ.map f = ρ.withDensity G)
    {b : ENNReal} (hbound : ∀ᵐ z ∂ρ, G z ≤ b) :
    ∀ᵐ p ∂ν, g (f p) ≤ b := by
  apply Submission.Obl.k4_profile_density_bounds.ae_observed_density_le_of_measure_bound
    ν ρ hf hg hν b
  intro S hS
  calc
    (ν.map f) S ≤ (μ.map f) S := Measure.map_mono hdom hf S
    _ = (ρ.withDensity G) S := by rw [hμ]
    _ ≤ (ρ.withDensity (fun _ => b)) S := withDensity_mono hbound S
    _ = b * ρ S := by rw [withDensity_apply _ hS, setLIntegral_const]

/-- An asymptotic density ceiling forces the lower bound on its exponent. -/
lemma le_exponent_of_cap {X : Type*} [MeasurableSpace X]
    {N L : ℕ → ℝ} (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hL : ∀ k, 1 ≤ L k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, L k ≤ N k ^ ε)
    (μ : ℕ → Measure X) (h : ℕ → X → ENNReal)
    (hmass : ∀ k, ENNReal.ofReal ((L k)⁻¹) ≤ μ k univ)
    {e a : ℝ} (htyp : PowerWindow N μ h e)
    (hcap : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      ∀ᵐ p ∂μ k, h k p ≤ ENNReal.ofReal (N k ^ (-a + ε))) : a ≤ e := by
  by_contra hle
  have hgap : 0 < a - e := sub_pos.mpr (lt_of_not_ge hle)
  let τ := (a - e) / 4
  have hτ : 0 < τ := by dsimp [τ]; linarith
  obtain ⟨c, hc, htail⟩ := htyp τ hτ
  have hcmp := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (show -a + τ < -e - τ by dsimp [τ]; linarith) 1
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_sum_lt_inv
    hN hNt hL hsub 0 (by norm_num : (0 : ℝ) < 1) hc
    (by norm_num : (0 : ℝ) ≤ 0)
  obtain ⟨k, hktail, hkcap, hkcmp, hksmall⟩ :=
    (htail.and ((hcap τ hτ).and (hcmp.and hsmall))).exists
  have hcaplt : ENNReal.ofReal (N k ^ (-a + τ)) <
      ENNReal.ofReal (N k ^ (-e - τ)) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos (by linarith [hN k]) _)).mpr
    simpa only [one_mul] using hkcmp
  have hlow : μ k univ ≤ μ k {p | h k p < ENNReal.ofReal (N k ^ (-e - τ)) ∨
      ENNReal.ofReal (N k ^ (-e + τ)) < h k p} := by
    apply measure_mono_ae
    filter_upwards [hkcap] with p hp _
    exact Or.inl (hp.trans_lt hcaplt)
  have hlt : ENNReal.ofReal (N k ^ (-c)) < ENNReal.ofReal ((L k)⁻¹) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr (lt_of_lt_of_le zero_lt_one (hL k)))).mpr
    simpa only [zero_mul, zero_add] using hksmall
  exact (not_lt_of_ge (hmass k)) ((hlow.trans hktail).trans_lt hlt)

/-- An asymptotic support-volume bound forces the upper bound on its exponent. -/
lemma exponent_le_of_support {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    {N L : ℕ → ℝ} (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hL : ∀ k, 1 ≤ L k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, L k ≤ N k ^ ε)
    (μ : ℕ → Measure X) (ρ : Measure Y) (f : ℕ → X → Y)
    (g : ℕ → Y → ENNReal) (hf : ∀ k, Measurable (f k))
    (hg : ∀ k, Measurable (g k)) (hlaw : ∀ k, (μ k).map (f k) = ρ.withDensity (g k))
    (hmass : ∀ k, ENNReal.ofReal ((L k)⁻¹) ≤ μ k univ)
    {e a : ℝ} (htyp : PowerWindow N μ (fun k p => g k (f k p)) e)
    (hsupp : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      ∃ B : Set Y, MeasurableSet B ∧ (∀ᵐ p ∂μ k, f k p ∈ B) ∧
        ρ B ≤ ENNReal.ofReal (N k ^ (a + ε))) : e ≤ a := by
  by_contra hle
  have hgap : 0 < e - a := sub_pos.mpr (lt_of_not_ge hle)
  let τ := (e - a) / 4
  have hτ : 0 < τ := by dsimp [τ]; linarith
  have hdecay : 0 < e - a - 2 * τ := by dsimp [τ]; linarith
  obtain ⟨c, hc, htail⟩ := htyp τ hτ
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_sum_lt_inv
    hN hNt hL hsub 0 hdecay hc (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨k, hktail, hksupp, hksmall⟩ := (htail.and ((hsupp τ hτ).and hsmall)).exists
  obtain ⟨B, hB, hsupport, hvol⟩ := hksupp
  have hbad : μ k {p | ENNReal.ofReal (N k ^ (-e + τ)) < g k (f k p)} ≤
      ENNReal.ofReal (N k ^ (-c)) := by
    refine (measure_mono ?_).trans hktail
    intro p hp
    exact Or.inr hp
  have hm := Submission.Obl.k4_profile_density_bounds.mass_le_density_times_support
    (μ k) ρ (hf k) (hg k) (hlaw k) hB hsupport
    (ENNReal.ofReal (N k ^ (-e + τ)))
  have hkN : 0 < N k := by linarith [hN k]
  have hprod : ENNReal.ofReal (N k ^ (-e + τ)) *
      ENNReal.ofReal (N k ^ (a + τ)) = ENNReal.ofReal (N k ^ (-(e - a - 2 * τ))) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hkN.le _), ← Real.rpow_add hkN]
    congr 2
    ring
  have hu : μ k univ ≤ ENNReal.ofReal
      (N k ^ (-(e - a - 2 * τ)) + N k ^ (-c)) := by
    calc
      _ ≤ ENNReal.ofReal (N k ^ (-e + τ)) * ρ B + ENNReal.ofReal (N k ^ (-c)) :=
        hm.trans (add_le_add le_rfl hbad)
      _ ≤ ENNReal.ofReal (N k ^ (-e + τ)) * ENNReal.ofReal (N k ^ (a + τ)) +
          ENNReal.ofReal (N k ^ (-c)) := by gcongr
      _ = _ := by rw [hprod, ENNReal.ofReal_add (by positivity) (by positivity)]
  have hlt : ENNReal.ofReal (N k ^ (-(e - a - 2 * τ)) + N k ^ (-c)) <
      ENNReal.ofReal ((L k)⁻¹) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr (lt_of_lt_of_le zero_lt_one (hL k)))).mpr
    simpa only [pow_zero, mul_one, one_mul] using hksmall
  exact (not_lt_of_ge (hmass k)) (hu.trans_lt hlt)

end Submission.Obl.k4_scalar_profile_raw_certification
