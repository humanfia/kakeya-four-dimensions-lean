import Submission.Obl.k4_scalar_profile_raw_certification.Interface
import Submission.Obl.k4_scalar_profile_raw_certification.Numerics

open MeasureTheory Set Filter
open scoped ENNReal

namespace Submission.Obl.k4_scalar_profile_raw_certification

/-- Once the coefficient exponent and angular flag are fixed, the raw estimates
certify all the numerical clauses of the given homogeneous profile. -/
theorem numerical_of_raw {N K L c : ℕ → ℝ}
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : Subpower N K) (hL : Subpower N L)
    {d s m S U C₀ : ℝ} (hs : 0 < s) (hsm : s < m) (hU : U < m)
    {angular : ℕ → Bool} {angular₀ : Bool} (hangular : ∀ k, angular k = angular₀)
    {μ ν : ℕ → Measure State} (hdom : ∀ k, ν k ≤ μ k)
    (hmass : ∀ k, ENNReal.ofReal ((L k)⁻¹) ≤ ν k univ)
    (hraw : ∀ k, Raw (N k) (K k) d s m S U (c k) (angular k) (μ k))
    (hc : HasExponent N c C₀) {F : ℝ → ℝ → ℝ}
    (hhom : Homogeneous N s (4 * (m + s + 1)) ν F) :
    Numerical d s m S U C₀ angular₀ F := by
  have hN1 : ∀ k, 1 ≤ N k := fun k => by linarith [hN k]
  have hNpos : ∀ k, 0 < N k := fun k => by linarith [hN k]
  have hK0 : ∀ k, 0 ≤ K k := fun k => (zero_le_one.trans (hK.1 k))
  have hV : 0 ≤ 4 * (m + s + 1) := by linarith
  have hc_upper : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, c k ≤ N k ^ (C₀ + ε) :=
    fun ε hε => (hc ε hε).mono fun _ hk => hk.2
  have hc_lower : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, N k ^ (C₀ - ε) ≤ c k :=
    fun ε hε => (hc ε hε).mono fun _ hk => hk.1
  obtain ⟨g, G, hg, hG, htyp, hTyp⟩ := hhom
  have hlower (r u : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) (hu : 0 ≤ u)
      (huV : u ≤ 4 * (m + s + 1)) : d * r - C₀ + max 0 (u - m) ≤ F r u := by
    apply le_exponent_of_cap hN1 hNt hL.1 hL.2 ν
      (fun k p => G k r u (aug (N k) r u p)) hmass
      (fun τ hτ => hTyp r u τ hr hrs hu huV hτ)
    intro ε hε
    have hpow := eventually_mul_power_le hN1 hK0 hK.2 hc_upper
      (-d * r - max 0 (u - m)) ε hε
    filter_upwards [hpow] with k hk
    obtain ⟨G₀, hG₀, hlaw₀, hcap₀, _⟩ := (hraw k).2.1 r u hr hrs hu huV
    have hcap := observed_density_le_of_domination jointReference (hdom k)
      (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.measurable_obsG _ _)
      (hG k r u hr hrs hu huV).1 (hG k r u hr hrs hu huV).2 hlaw₀ hcap₀
    have hrawpow : K k * c k * N k ^ (-d * r) * min 1 (N k ^ (m - u)) =
        K k * c k * N k ^ (-d * r - max 0 (u - m)) := by
      rw [noise_factor_eq (hN1 k)]
      rw [mul_assoc (K k * c k), ← Real.rpow_add (hNpos k)]
      rfl
    filter_upwards [hcap] with p hp
    apply hp.trans
    rw [hrawpow]
    apply ENNReal.ofReal_le_ofReal
    convert hk using 1
    congr 1
    ring
  have hupper : F s 0 ≤ d * s - C₀ := by
    apply exponent_le_of_support hN1 hNt hL.1 hL.2 ν reference
      (fun k => obs (N k) s) (fun k => g k s)
      (fun k => Submission.Obl.k4_scalar_terminal_chart_packet_extraction.measurable_obsL _)
      (fun k => (hg k s hs.le le_rfl).1) (fun k => (hg k s hs.le le_rfl).2) hmass
      (fun τ hτ => htyp s τ hs.le le_rfl hτ)
    intro ε hε
    have hpow := eventually_mul_power_le hN1 hK0 hK.2
      (eventually_inv_le hN1 hc_lower) (d * s) ε hε
    filter_upwards [hpow] with k hk
    obtain ⟨B, hB, hvol, hsupport⟩ := (hraw k).2.2
    refine ⟨B, hB, (ae_mono (hdom k) hsupport), hvol.trans ?_⟩
    apply ENNReal.ofReal_le_ofReal
    convert hk using 1
    congr 1
    ring
  have heq : F s 0 = d * s - C₀ := by
    apply le_antisymm hupper
    have hh := hlower s 0 hs.le le_rfl le_rfl hV
    rwa [max_eq_left (by linarith : (0 : ℝ) - m ≤ 0), add_zero] at hh
  refine ⟨heq, hlower, ?_⟩
  intro ha u hu huU
  by_cases hu0 : u = 0
  · simp [hu0]
  have hu_pos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  have huV : u ≤ 4 * (m + s + 1) := by linarith
  rw [heq]
  apply le_exponent_of_cap hN1 hNt hL.1 hL.2 ν
    (fun k p => G k s u (aug (N k) s u p)) hmass
    (fun τ hτ => hTyp s u τ hs.le le_rfl hu huV hτ)
  intro ε hε
  have hpow := eventually_mul_power_le hN1 hK0 hK.2 hc_upper (-d * s - S * u) ε hε
  filter_upwards [hpow] with k hk
  obtain ⟨G₀, hG₀, hlaw₀, _, hangcap⟩ := (hraw k).2.1 s u hs.le le_rfl hu huV
  have hcap := observed_density_le_of_domination jointReference (hdom k)
    (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.measurable_obsG _ _)
    (hG k s u hs.le le_rfl hu huV).1 (hG k s u hs.le le_rfl hu huV).2 hlaw₀
    (hangcap rfl ((hangular k).trans ha) hu_pos huU)
  filter_upwards [hcap] with p hp
  apply hp.trans (ENNReal.ofReal_le_ofReal ?_)
  convert hk using 1
  congr 1
  ring

end Submission.Obl.k4_scalar_profile_raw_certification
