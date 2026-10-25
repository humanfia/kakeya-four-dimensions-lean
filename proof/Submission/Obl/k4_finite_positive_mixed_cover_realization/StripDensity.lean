import Submission.Obl.k4_finite_positive_mixed_cover_realization.FiniteGainMenu
import Submission.Obl.k4_finite_positive_mixed_cover_realization.Interface
import Submission.Obl.k4_fixed_menu_density_pruning.Outer
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.TypicalOperations
import Submission.Obl.k4_profile_density_bounds.Common

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Set Filter Submission.Lib.K4XInterface

noncomputable def stripGainMenu (gain ρ : ℝ) : Finset ℝ := by
  classical
  exact (geometricGainMenu gain ρ (1 / 8)).filter (fun h => gain ≤ h ∧ h ≤ 1 / 8)

lemma mem_stripGainMenu {gain ρ h : ℝ} (hgain : 0 < gain) (hρ : 0 < ρ)
    (hh : gain ≤ h) (hh1 : h ≤ 1 / 8) (hmenu : ∃ e : ℕ, h = gain * (1 + ρ) ^ e) :
    h ∈ stripGainMenu gain ρ := by
  classical
  exact Finset.mem_filter.mpr ⟨mem_geometricGainMenu hgain hρ hmenu hh1, hh, hh1⟩

lemma stripGainMenu_bounds {gain ρ h : ℝ} (hh : h ∈ stripGainMenu gain ρ) :
    gain ≤ h ∧ h ≤ 1 / 8 := (Finset.mem_filter.mp hh).2

/-- The good event uses the original terminal pure law and the original
joint law at a fixed angular depth. -/
def stripGood {W : ℕ} (Nk L fL S b h ζ : ℝ) (B : Fin W → ℝ)
    (g : Fin W → Observation → ENNReal)
    (G : Fin W → Observation × (Fin 2 → ℤ) → ENNReal) (w : Fin W) : Set Incidence :=
  {z | G w (gobs (B w) (gδ Nk L) z,
      fun e : Fin 2 => ⌊(gv z.1) e / gδ Nk (b * h * L / 4)⌋) ≤
        ENNReal.ofReal (Nk ^ (-fL - S * (b * h * L / 4) + ζ)) ∧
    ENNReal.ofReal (Nk ^ (-fL - ζ)) ≤ g w (gobs (B w) (gδ Nk L) z)}

lemma strip_good_bad_bound {W : ℕ} (Nk L fL S b h ζ : ℝ)
    (μ : Fin W → Measure Incidence) (weight : Fin W → ENNReal) (B : Fin W → ℝ)
    (g : Fin W → Observation → ENNReal)
    (G : Fin W → Observation × (Fin 2 → ℤ) → ENNReal) :
    (∑ w, weight w * μ w (stripGood Nk L fL S b h ζ B g G w)ᶜ) ≤
      (∑ w, weight w * μ w {z | g w (gobs (B w) (gδ Nk L) z) <
          ENNReal.ofReal (Nk ^ (-fL - ζ)) ∨ ENNReal.ofReal (Nk ^ (-fL + ζ)) <
          g w (gobs (B w) (gδ Nk L) z)}) +
      ∑ w, weight w * μ w {z | ENNReal.ofReal (Nk ^ (-fL - S * (b * h * L / 4) + ζ)) <
        G w (gobs (B w) (gδ Nk L) z,
          fun e : Fin 2 => ⌊(gv z.1) e / gδ Nk (b * h * L / 4)⌋)} := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w _
  rw [← mul_add]
  apply mul_le_mul' le_rfl
  apply (measure_mono ?_).trans (measure_union_le _ _)
  intro z hz
  by_cases hg : ENNReal.ofReal (Nk ^ (-fL - ζ)) ≤ g w (gobs (B w) (gδ Nk L) z)
  · exact Or.inr (lt_of_not_ge (fun hG => hz ⟨hG, hg⟩))
  · exact Or.inl (Or.inl (lt_of_not_ge hg))

/-- The finitely many original angular exceptions and the terminal pure
exception share one positive decay power before the sample is chosen. -/
theorem prob_strip_density_tails
    {N K : ℕ → ℝ} {L d S η gain ρ b ζ : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → Measure Trajectory}
    {E : (k : ℕ) → Fin (W k) → Set Incidence}
    {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → Observation → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → Observation × (Fin 2 → ℤ) → ENNReal}
    (hp : prob N K L d S η W ω ν E P B f g G)
    (hgain : 0 < gain) (hb : 0 < b) (hbη : b ≤ η) (hζ : 0 < ζ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, ∀ h ∈ stripGainMenu gain ρ,
      (∑ w, ENNReal.ofReal (ω k w) * (((ν k w).prod volume).restrict (E k w))
        (stripGood (N k) L (f L) S b h ζ (B k) (fun w => g k w L)
          (fun w => G k w (b * h * L / 4)) w)ᶜ) ≤
        ENNReal.ofReal (2 * N k ^ (-c)) := by
  classical
  rcases hp with ⟨hN, _, _, hL, _, _, _, _, _, _, _, _, hpure, _, hjoint⟩
  obtain ⟨cp, hcp, hpt⟩ := hpure L ζ hL.le le_rfl hζ
  obtain ⟨ca, hca, hat⟩ := k4_fixed_menu_density_pruning.finite_common_power_tail N
    (fun k => (by linarith [hN k] : 1 ≤ N k))
    (fun h : stripGainMenu gain ρ => fun k => ∑ w, ENNReal.ofReal (ω k w) *
      (((ν k w).prod volume).restrict (E k w))
        {z | ENNReal.ofReal (N k ^ (-f L - S * (b * h.val * L / 4) + ζ)) <
          G k w (b * h.val * L / 4) (gobs (B k w) (gδ (N k) L) z,
            fun e : Fin 2 => ⌊(gv z.1) e / gδ (N k) (b * h.val * L / 4)⌋)}) (by
      intro h
      have hh := stripGainMenu_bounds h.property
      have hh0 : 0 < h.val := hgain.trans_le hh.1
      have hu : 0 < b * h.val * L / 4 := by positivity
      have huη : b * h.val * L / 4 ≤ η * L := by
        have h1 := mul_le_mul_of_nonneg_left hh.2 (mul_nonneg hb.le hL.le)
        have h2 := mul_le_mul_of_nonneg_right hbη hL.le
        nlinarith
      exact hjoint (b * h.val * L / 4) ζ hu huη hζ)
  refine ⟨min cp ca, lt_min hcp hca, ?_⟩
  filter_upwards [hpt, hat] with k hpk hak h hh
  have hNk : 1 ≤ N k := by linarith [hN k]
  have hpbound := hpk.trans (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_le hNk (neg_le_neg (min_le_left cp ca))))
  have habound := (hak ⟨h, hh⟩).trans (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_le hNk (neg_le_neg (min_le_right cp ca))))
  apply (strip_good_bad_bound (N k) L (f L) S b h ζ
    (fun w => ((ν k w).prod volume).restrict (E k w))
    (fun w => ENNReal.ofReal (ω k w)) (B k) (fun w => g k w L)
    (fun w => G k w (b * h * L / 4))).trans
  convert add_le_add hpbound habound using 1
  · rfl
  · rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring

/-- The probability mixture has at most unit selected original mass. -/
lemma prob_original_mass_le_one
    {N K : ℕ → ℝ} {L d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → Measure Trajectory}
    {E : (k : ℕ) → Fin (W k) → Set Incidence}
    {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → Observation → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → Observation × (Fin 2 → ℤ) → ENNReal}
    (hp : prob N K L d S η W ω ν E P B f g G) (k : ℕ) :
    (∑ w, ENNReal.ofReal (ω k w) * (((ν k w).prod volume).restrict (E k w)) univ) ≤ 1 := by
  obtain ⟨M, D, hdata⟩ := hp.2.2.2.2.2.2.2.2.1
  have hk := hdata k
  rw [← k4_native_calibrated_homogeneous_remainder.worldLaw_univ]
  apply k4_native_calibrated_homogeneous_remainder.worldLaw_mass_le_one
  · rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => hk.2.1 w), hk.2.2.1]
    norm_num
  · intro w
    letI : IsProbabilityMeasure (ν k w) := (hk.2.2.2.1 w).1
    exact k4_profile_density_bounds.selected_mass_le_one _ _ (hk.2.2.2.1 w).2.2.2.2.2.2.2.2.1

end Submission.Obl.k4_finite_positive_mixed_cover_realization
