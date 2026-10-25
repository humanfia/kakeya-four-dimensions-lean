import Submission.Obl.k4_profile_density_bounds.Mass
import Submission.Obl.k4_profile_density_bounds.Asymptotics

open MeasureTheory Set Filter
open scoped ENNReal

/-!
# Typical densities and exponents

A support of measure at most `A * K^p * N^s` forces the typical density exponent to be at
most `s`. A measure ceiling of size `A * Λ * N^(-s)` forces that exponent to be at least `s`.
Both arguments compare the exceptional power-small mass with the selected mass `1 / K`.
-/

namespace Submission.Obl.k4_profile_density_bounds

def Typical (N : ℕ → ℝ) (μ : ℕ → Measure State)
    (f : ℕ → State → Observation) (e : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
    ∀ G : Observation → ENNReal, Measurable G →
    (μ k).map (f k) = reference.withDensity G →
    μ k {p | G (f k p) < ENNReal.ofReal (N k ^ (-e - τ)) ∨
      ENNReal.ofReal (N k ^ (-e + τ)) < G (f k p)} ≤
        ENNReal.ofReal (N k ^ (-c))

lemma profile_le_of_support_bound {N K : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (μ : ℕ → Measure State) (f : ℕ → State → Observation)
    (hf : ∀ k, Measurable (f k))
    (hmass : ∀ k, ENNReal.ofReal ((K k)⁻¹) ≤ μ k univ)
    (hdens : ∀ k, ∃ G, Measurable G ∧ (μ k).map (f k) = reference.withDensity G)
    {e s A : ℝ} (hA : 0 ≤ A) (p : ℕ)
    (htyp : Typical N μ f e)
    (hsupp : ∀ k, ∃ S : Set Observation, MeasurableSet S ∧
      (∀ᵐ x ∂μ k, f k x ∈ S) ∧
      reference S ≤ ENNReal.ofReal (A * K k ^ p * N k ^ s)) : e ≤ s := by
  by_contra hes
  have hgap : 0 < e - s := sub_pos.mpr (lt_of_not_ge hes)
  let τ := (e - s) / 2
  have hτ : 0 < τ := by dsimp [τ]; linarith
  obtain ⟨c, hc, htail⟩ := htyp τ hτ
  have ha : 0 < e - s - τ := by dsimp [τ]; linarith
  have hsmall := eventually_sum_lt_inv hN hNt hK hsub p ha hc hA
  obtain ⟨k, hktail, hksmall⟩ := (htail.and hsmall).exists
  obtain ⟨G, hG, hlaw⟩ := hdens k
  obtain ⟨S, hS, hsupport, hbound⟩ := hsupp k
  have hbad : μ k {x | ENNReal.ofReal (N k ^ (-e + τ)) < G (f k x)} ≤
      ENNReal.ofReal (N k ^ (-c)) := by
    refine (measure_mono ?_).trans (hktail G hG hlaw)
    intro x hx
    exact Or.inr hx
  have hm := mass_le_density_times_support (μ k) reference (hf k) hG hlaw hS hsupport
    (ENNReal.ofReal (N k ^ (-e + τ)))
  have hkN : 0 < N k := by linarith [hN k]
  have hkK : 0 < K k := by linarith [hK k]
  have hprod : ENNReal.ofReal (N k ^ (-e + τ)) *
      ENNReal.ofReal (A * K k ^ p * N k ^ s) =
      ENNReal.ofReal (A * K k ^ p * N k ^ (-(e - s - τ))) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hkN.le _)]
    congr 1
    calc
      N k ^ (-e + τ) * (A * K k ^ p * N k ^ s) =
          A * K k ^ p * (N k ^ (-e + τ) * N k ^ s) := by ring
      _ = _ := by
        rw [← Real.rpow_add hkN]
        congr 2
        ring
  have hu : μ k univ ≤ ENNReal.ofReal
      (A * K k ^ p * N k ^ (-(e - s - τ)) + N k ^ (-c)) := by
    calc
      _ ≤ ENNReal.ofReal (N k ^ (-e + τ)) * reference S +
          ENNReal.ofReal (N k ^ (-c)) := hm.trans (add_le_add le_rfl hbad)
      _ ≤ ENNReal.ofReal (N k ^ (-e + τ)) *
          ENNReal.ofReal (A * K k ^ p * N k ^ s) +
          ENNReal.ofReal (N k ^ (-c)) := by gcongr
      _ = _ := by
        rw [hprod, ENNReal.ofReal_add (by positivity) (by positivity)]
  have hlt : ENNReal.ofReal
      (A * K k ^ p * N k ^ (-(e - s - τ)) + N k ^ (-c)) <
      ENNReal.ofReal ((K k)⁻¹) :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hksmall
  exact (not_lt_of_ge (hmass k)) (hu.trans_lt hlt)

lemma profile_ge_of_measure_bound {N K Λ : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (hΛ : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, Λ k ≤ N k ^ ε)
    (μ : ℕ → Measure State) (f : ℕ → State → Observation)
    (hf : ∀ k, Measurable (f k))
    (hmass : ∀ k, ENNReal.ofReal ((K k)⁻¹) ≤ μ k univ)
    (hdens : ∀ k, ∃ G, Measurable G ∧ (μ k).map (f k) = reference.withDensity G)
    {e s A : ℝ} (hA : 0 ≤ A) (htyp : Typical N μ f e)
    (hbound : ∀ k, ∀ S : Set Observation, MeasurableSet S →
      ((μ k).map (f k)) S ≤ ENNReal.ofReal (A * Λ k * N k ^ (-s)) * reference S) :
    s ≤ e := by
  by_contra hse
  have hgap : 0 < s - e := sub_pos.mpr (lt_of_not_ge hse)
  let τ := (s - e) / 4
  have hτ : 0 < τ := by dsimp [τ]; linarith
  obtain ⟨c, hc, htail⟩ := htyp τ hτ
  have hcmp := eventually_const_mul_rpow_lt hNt
    (show τ + -s < -e - τ by dsimp [τ]; linarith) A
  have hsmall := eventually_sum_lt_inv hN hNt hK hsub 0 (by norm_num : (0 : ℝ) < 1)
    hc (by norm_num : (0 : ℝ) ≤ 0)
  obtain ⟨k, hktyp, hkΛ, hkcmp, hksmall⟩ :=
    (htail.and ((hΛ τ hτ).and (hcmp.and hsmall))).exists
  obtain ⟨G, hG, hlaw⟩ := hdens k
  have hkN : 0 < N k := by linarith [hN k]
  have hkK : 0 < K k := by linarith [hK k]
  have hcaplt : ENNReal.ofReal (A * Λ k * N k ^ (-s)) <
      ENNReal.ofReal (N k ^ (-e - τ)) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hkN _)).mpr
    calc
      A * Λ k * N k ^ (-s) ≤ A * N k ^ τ * N k ^ (-s) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkΛ hA)
          (Real.rpow_nonneg hkN.le _)
      _ = A * N k ^ (τ + -s) := by rw [Real.rpow_add hkN]; ring
      _ < _ := hkcmp
  haveI : SigmaFinite reference := by unfold reference; infer_instance
  have hae := ae_observed_density_le_of_measure_bound (μ k) reference (hf k) hG hlaw
    (ENNReal.ofReal (A * Λ k * N k ^ (-s))) (hbound k)
  have hlow : μ k univ ≤ μ k {p | G (f k p) < ENNReal.ofReal (N k ^ (-e - τ))} := by
    apply measure_mono_ae
    filter_upwards [hae] with p hp _
    exact hp.trans_lt hcaplt
  have hmassupper : μ k univ ≤ ENNReal.ofReal (N k ^ (-c)) := by
    refine hlow.trans ((measure_mono ?_).trans (hktyp G hG hlaw))
    intro p hp
    exact Or.inl hp
  have hlt : ENNReal.ofReal (N k ^ (-c)) < ENNReal.ofReal ((K k)⁻¹) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    simpa only [zero_mul, zero_add] using hksmall
  exact (not_lt_of_ge (hmass k)) (hmassupper.trans_lt hlt)

end Submission.Obl.k4_profile_density_bounds
