import Submission.Obl.k4_uncapped_native_capping.Availability
import Submission.Obl.k4_uncapped_native_capping.UncappedPacket

/-!
# Glue of analytical capping

The analytical input is `MaskedCaps`: for a fixed exact problem with a relative
profile close to the linear one, fixed original masks (chosen before any actual
loss) have power-small original weighted cost, and restricting every provisional
packet law to the complement of the masks gives all frozen projected caps.

From it, the uncapped geometric availability gives capped packet availability:
the masks are charged once to the original weighted incidence law (no packet-count
factor), the actual loss is chosen below the mask exponent, and the light-law
pruning of `CappedPacketAvailable.to_native` finishes `AnalyticalCappingStatement`.
-/

namespace Submission.Obl.k4_uncapped_native_capping

open MeasureTheory Filter Set
open Submission.Obl.k4_finite_width_output_exclusion
noncomputable section

/-- Fixed original masks of power-small original weighted cost whose
restriction caps every geometric packet family of small actual loss. The
profile tolerance `ξ` is chosen first, before the exact problem; the masks
and the mask exponent depend on the problem, but not on the actual loss. -/
def MaskedCaps (ds S η s m U χ : ℝ) : Prop :=
  ∃ ξ : ℝ, 0 < ξ ∧
  ∀ (N K : ℕ → ℝ) (d : ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure Traj) (E : (k : ℕ) → Fin (W k) → Set Inc)
    (P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ) (B : (k : ℕ) → Fin (W k) → ℝ)
    (f : ℝ → ℝ) (g : (k : ℕ) → Fin (W k) → ℝ → Obs → ENNReal)
    (G : (k : ℕ) → Fin (W k) → ℝ → (Obs × (Fin 2 → ℤ)) → ENNReal),
    prob N K 1 d S η W ω ν E P B f g G →
    (∀ r : ℝ, 0 ≤ r → r ≤ s → |f r - f 0 - ds * r| ≤ ξ) →
    ∃ Bad : (k : ℕ) → Fin (W k) → Set Inc,
      (∀ k w, MeasurableSet (Bad k w)) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
        (∑ w, ENNReal.ofReal (ω k w) *
          (((ν k w).prod volume).restrict (E k w)) (Bad k w)) ≤
            ENNReal.ofReal (N k ^ (-c))) ∧
      ∃ loss₀ : ℝ, 0 < loss₀ ∧ ∀ loss : ℝ, 0 < loss → loss ≤ loss₀ →
        ∀ (M D : ℕ) (h : ℝ), ∀ᶠ k in atTop, ∀ p : PacketData (W k),
          p.Geometry (N k) (K k) (ω k) (ν k) (E k) (P k) (B k) M D loss h →
          p.ProvisionalAnalysis (N k) χ ds s m (S / 2) U (ω k) (ν k) (P k) (B k) →
          p.CappingGeometry (N k) loss U (f 0) ξ (ν k) →
          (p.restrictOriginal (fun w => (Bad k w)ᶜ)).Analysis (N k) χ ds s m (S / 2) U
            (ω k) (ν k) (P k) (B k)

theorem prob_measurableSet_E {N K : ℕ → ℝ} {L d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ} {ν : (k : ℕ) → Fin (W k) → Measure Traj}
    {E : (k : ℕ) → Fin (W k) → Set Inc} {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → Obs → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → (Obs × (Fin 2 → ℤ)) → ENNReal}
    (hp : prob N K L d S η W ω ν E P B f g G) (k : ℕ) (w : Fin (W k)) :
    MeasurableSet (E k w) := by
  rcases hp with ⟨_, _, _, _, _, _, _, _, hdata, _⟩
  obtain ⟨M, D, hreg⟩ := hdata
  rcases (hreg k).2.2.2.1 w with ⟨_, _, _, _, _, _, _, hE, _⟩
  exact hE

/-- One actual sample: restrict the provisional laws to the good original
incidences. Geometry, budgets and lists are unchanged; the removed mass is
charged once to the original weighted incidence law. -/
theorem capped_sample_of_uncapped {N K : ℝ} {W : ℕ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Traj} {E : Fin W → Set Inc}
    {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ} {M D : ℕ}
    {loss loss' h χ ds s m S U f₀ ξ c : ℝ}
    (hN : 1 ≤ N) (hB : ∀ w, 0 ≤ B w) (hE : ∀ w, MeasurableSet (E w))
    (Bad : Fin W → Set Inc) (hBad : ∀ w, MeasurableSet (Bad w))
    (hcost : (∑ w, ENNReal.ofReal (ω w) *
      (((ν w).prod volume).restrict (E w)) (Bad w)) ≤ ENNReal.ofReal (N ^ (-c)))
    (hcap : ∀ p : PacketData W,
      p.Geometry N K ω ν E P B M D loss' h →
      p.ProvisionalAnalysis N χ ds s m S U ω ν P B →
      p.CappingGeometry N loss' U f₀ ξ ν →
      (p.restrictOriginal (fun w => (Bad w)ᶜ)).Analysis N χ ds s m S U ω ν P B)
    (hloss : loss' ≤ loss)
    (hgap : ENNReal.ofReal (N ^ (-loss)) + 2 * ENNReal.ofReal (N ^ (-c)) ≤
      ENNReal.ofReal (N ^ (-loss')))
    (hsample : UncappedNativeSample N K W ω ν E P B M D loss' h χ ds s m S U f₀ ξ) :
    ∃ p : PacketData W,
      p.Geometry N K ω ν E P B M D loss h ∧
      p.Analysis N χ ds s m S U ω ν P B ∧
      ENNReal.ofReal (N ^ (-loss)) ≤ p.mass ω ν := by
  obtain ⟨p, hg, ha, _, hmass, hcg⟩ := hsample.exists_packetData
  refine ⟨p.restrictOriginal (fun w => (Bad w)ᶜ),
    (hg.restrictOriginal _).mono_loss hN hB hloss, hcap p hg ha hcg, ?_⟩
  refine PacketData.mass_lower_restrictOriginal hg ha.original_domination hE
    (fun w => (Bad w)ᶜ) (fun w => (hBad w).compl) ENNReal.ofReal_ne_top ?_
    (hgap.trans hmass)
  simpa only [compl_compl] using hcost

/-- Capped availability from uncapped availability and the masked caps. The
problem and its format are those of the geometric stage; the actual loss is
chosen below both the requested loss and the mask exponent. -/
theorem cappedPacketAvailable_of_uncapped {ds kr S η s m U χ h t : ℝ}
    (hcaps : MaskedCaps ds S η s m U χ)
    (hu : UncappedAvailability ds kr S η s m U)
    (hχ : 0 < χ) (hh : 0 < h) (ht : 0 < t) :
    CappedPacketAvailable ds kr S η s m U χ h t := by
  obtain ⟨ξ, hξ, hmask⟩ := hcaps
  obtain ⟨N, K, d, W, ω, ν, E, P, B, f, g, G, hprob, hd, hH, hprofile, M, D, havail⟩ :=
    hu χ h t ξ hχ hh ht hξ
  obtain ⟨Bad, hBad, ⟨c, hc, hcost⟩, loss₀, hloss₀, hcap⟩ :=
    hmask N K d W ω ν E P B f g G hprob hprofile
  obtain ⟨hN, hNt, _, _, _, _, hB, _⟩ :=
    Submission.Obl.k4_quadratic_finite_greedy_cover.prob_basic
      N K 1 d S η W ω ν E P B f g G hprob
  refine ⟨N, K, d, W, ω, ν, E, P, B, f, g, G, hprob, hd, hH, M, D, ?_⟩
  intro loss hloss
  let ρ : ℝ := min (loss / 2) (min (c / 2) loss₀)
  have hρ : 0 < ρ := lt_min (by positivity) (lt_min (by positivity) hloss₀)
  have hρloss : ρ < loss := (min_le_left _ _).trans_lt (by linarith)
  have hρc : ρ < c := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hρ₀ : ρ ≤ loss₀ := (min_le_right _ _).trans (min_le_right _ _)
  have hgap : ∀ᶠ k in atTop,
      ENNReal.ofReal (N k ^ (-loss)) + 2 * ENNReal.ofReal (N k ^ (-c)) ≤
        ENNReal.ofReal (N k ^ (-ρ)) := by
    filter_upwards
      [Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt hNt
        (show -loss < -ρ by linarith) 2,
       Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt hNt
        (show -c < -ρ by linarith) 4] with k hk₁ hk₂
    have hN0 : 0 ≤ N k := by linarith [hN k]
    rw [show (2 : ENNReal) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (Real.rpow_nonneg hN0 _)
        (mul_nonneg (by norm_num) (Real.rpow_nonneg hN0 _))]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  apply (((havail ρ hρ).and_eventually (hcap ρ hρ hρ₀ M D h)).and_eventually
    (hcost.and hgap)).mono
  rintro k ⟨⟨hsample, hcapk⟩, hcostk, hgapk⟩
  exact capped_sample_of_uncapped (by linarith [hN k]) (fun w => (hB k w).le)
    (prob_measurableSet_E hprob k) (Bad k) (hBad k) hcostk hcapk hρloss.le hgapk hsample

/-- The analytical stage, from the masked caps at every positive scalar
tolerance. -/
theorem analyticalCapping_of_maskedCaps
    (hcaps : ∀ ds S η s m U χ : ℝ, 0 ≤ ds → ds < 1 → 0 < S → 0 < η →
      0 < s → s < 1 → s < m → 0 < U → U < m → U ≤ η → 0 < χ →
      MaskedCaps ds S η s m U χ) :
    AnalyticalCappingStatement := by
  intro ds kr S η s m U hds hds₁ hS hη hs hs₁ hsm hU hUm hUη hu χ h t hχ hh ht
  exact (cappedPacketAvailable_of_uncapped
    (hcaps ds S η s m U χ hds hds₁ hS hη hs hs₁ hsm hU hUm hUη hχ) hu hχ hh ht).to_native hχ

end
end Submission.Obl.k4_uncapped_native_capping
