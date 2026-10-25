import Submission.Obl.k4_raw_localized_native_systems.DSourceNumerics
import Submission.Obl.k4_raw_localized_native_systems.SourceDeletion
import Submission.Obl.k4_raw_localized_native_systems.Window.DensityGood
import Submission.Obl.k4_raw_localized_native_systems.Window.LongScaleBounds
import Submission.Obl.k4_raw_localized_native_systems.Window.OmissionTail
import Submission.Obl.k4_raw_localized_native_systems.Window.TailComparison

namespace Submission.Obl.k4_raw_localized_native_systems

open MeasureTheory Set Filter
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_native_grid_profile_extension.Profiles
open Window

noncomputable section
set_option maxHeartbeats 3000000

def sourceDensityTail {p : Data} {kr w ε q band : ℝ} {M D : ℕ} {sd r : ℕ → ℝ}
    (src : HomogeneousSourceSequence p kr w ε q band 2 M D sd r)
    (u τ : ℝ) (n : ℕ) : ENNReal :=
  ∑ γ, ENNReal.ofReal (p.ω (src.index n) γ) * selected p (src.index n) γ
    (densityGood p {0, r 0} {u} τ (src.index n) γ)ᶜ

def sourceMajorTail {p : Data} {kr w ε q band : ℝ} {M D : ℕ} {sd r : ℕ → ℝ}
    (src : HomogeneousSourceSequence p kr w ε q band 2 M D sd r)
    (u : ℝ) (n : ℕ) : ENNReal :=
  ∑ γ, ENNReal.ofReal (p.ω (src.index n) γ) * selected p (src.index n) γ
    (shortWitnessEvent (sourceFrame (src.forest n) (src.core n) 0)
      ((1 / (2 : ℝ) ^ (src.forest n).T 0) * p.N (src.index n) ^ (-(4 * u))) γ)

/-- Numerical and original-law data for the D-side, fixed before the
current loss or formatted current family is chosen. -/
structure SourceDData {p : Data} {kr w ε q band : ℝ} {M D : ℕ} {sd r : ℕ → ℝ}
    (src : HomogeneousSourceSequence p kr w ε q band 2 M D sd r) (χ ds s : ℝ) where
  u : ℝ
  τ : ℝ
  e : ℝ
  a₀ : ℝ
  ell : ℝ
  u_pos : 0 < u
  u_eta : u ≤ p.η * p.L
  packing_u : 8 * u + 2 * band ≤ 1
  a₀_pos : 0 < a₀
  ell_pos : 0 < ell
  ell_four : ell ≤ 4
  profile : p.f (r 0) - p.f 0 + τ + 4 * band + 2 * (8 * u + 2 * band) + χ / 2 ≤ ds * s + χ
  time : ∀ n, (2 : ℝ) ^ (src.forest n).T 0 ≤ p.N (src.index n)
  events : ∀ loss : ℝ, 0 < loss → loss ≤ ell → ∀ᶠ n in atTop,
    RawSampleBounds (p.N (src.index n)) (src.forest n).κ (p.N (src.index n) ^ e)
      χ τ (r 0) s band (8 * u + 2 * band) ∧
    p.N (src.index n) ^ loss ≤ p.N (src.index n) ^ e ∧
    16 * (src.forest n).κ * p.N (src.index n) ^ (-4 * u) ≤ δ (p.N (src.index n)) u ∧
    10 * sourceDensityTail src u τ n + 2 * sourceMajorTail src u n <
      ENNReal.ofReal (src.forest n).κ⁻¹ ∧
    6 * sourceDensityTail src u τ n + sourceMajorTail src u n +
      ENNReal.ofReal (p.N (src.index n) ^ (-p.S * u + 2 * τ)) *
        ((9 * ⌈p.N (src.index n) ^ loss⌉₊ * ⌈(src.forest n).κ⌉₊ +
          9 * ⌈(src.forest n).κ⌉₊ : ℕ) : ENNReal) ≤
      ENNReal.ofReal (p.N (src.index n) ^ (-a₀))

theorem exists_source_d_data_of_tail
    (tailLemma : ∀ {N κ : ℕ → ℝ} {X₁ X₂ : ℕ → ENNReal},
      (∀ n, 1 ≤ N n) → Tendsto N atTop atTop → (∀ n, 1 ≤ κ n) →
      (∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, κ n ≤ N n ^ e) →
      IsPowerSmall N X₁ → IsPowerSmall N X₂ →
      ∀ᶠ n in atTop, 10 * X₁ n + 2 * X₂ n < ENNReal.ofReal ((κ n)⁻¹))
 {p : Data} (hp : Valid p) (hL : p.L = 1)
    {kr w ε q band : ℝ} {M D : ℕ} {sd r : ℕ → ℝ}
    (src : HomogeneousSourceSequence p kr w ε q band 2 M D sd r)
    {χ ds s vGap : ℝ} (hχ : 0 < χ) (hds : 0 ≤ ds) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hr0 : 0 ≤ r 0) (hgap : r 0 + vGap ≤ s) (hclose : s - r 0 + 2 * vGap ≤ 2 * χ)
    (hvGap : 0 < vGap) (hband0 : 0 ≤ band) (hbandχ : band ≤ χ / 1000)
    (hband1 : band ≤ 1 / 80)
    (hprofile : |p.f (r 0) - p.f 0 - ds * r 0| ≤ χ / 1000)
    (htime : kr * sd 0 + ε ≤ 1) :
    Nonempty (SourceDData src χ ds s) := by
  have hS : 0 < p.S := hp.2.2.2.2.2.2.1
  have hη : 0 < p.η * p.L := mul_pos hp.2.2.2.2.2.2.2.1 hp.length_pos
  let u := min (χ / 1000) (min (p.η * p.L / 10) (1 / 100 : ℝ))
  have hu : 0 < u := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have huχ : u ≤ χ / 1000 := min_le_left _ _
  have huη10 : u ≤ p.η * p.L / 10 := (min_le_right _ _).trans (min_le_left _ _)
  have hu1 : u ≤ 1 / 100 := (min_le_right _ _).trans (min_le_right _ _)
  have huη : u ≤ p.η * p.L := by linarith only [huη10, hη]
  have hu4η : 4 * u ≤ p.η * p.L := by linarith only [huη10, hη]
  let τ := min (χ / 1000) (p.S * u / 100)
  have hτ : 0 < τ := lt_min (by positivity) (by positivity)
  have hτχ : τ ≤ χ / 1000 := min_le_left _ _
  have hτSu : τ ≤ p.S * u / 100 := min_le_right _ _
  have hup : 8 * u + 2 * band < 1 := by linarith only [hu1, hband1]
  have hE : 2 * band + (8 * u + 2 * band) ≤ 4 := by linarith only [hu1, hband1]
  have hrs : r 0 ≤ s := by linarith only [hgap, hvGap]
  have hrL : r 0 ≤ p.L := by rw [hL]; exact hrs.trans hs1
  let N := fun n => p.N (src.index n)
  let κ := fun n => (src.forest n).κ
  let X₁ := sourceDensityTail src u τ
  let X₂ := sourceMajorTail src u
  have hN : ∀ n, 1 ≤ N n := fun n => hp.scale_ge_one _
  have hNt : Tendsto N atTop atTop := hp.scale_tendsto.comp src.mono.tendsto_atTop
  have hκ : ∀ n, 1 ≤ κ n := fun n => (src.core n).1
  have hsub : ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, κ n ≤ N n ^ e := src.subpower
  have hR : ∀ z ∈ ({0, r 0} : Finset ℝ), 0 ≤ z ∧ z ≤ p.L := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨le_rfl, hp.length_pos.le⟩
    · exact ⟨hr0, hrL⟩
  have hA : ∀ z ∈ ({u} : Finset ℝ), 0 < z ∧ z ≤ p.η * p.L := by
    intro z hz
    rcases Finset.mem_singleton.mp hz with rfl
    exact ⟨hu, huη⟩
  have hX₁ : IsPowerSmall N X₁ := by
    exact (densityGood_powerSmall hp {0, r 0} {u} hR hA hτ).comp
      src.index src.mono.tendsto_atTop
  have hX₂ : IsPowerSmall N X₂ :=
    source_short_major_powerSmall hp src (i := 0) (by omega) hrL (by positivity) hu4η
  obtain ⟨c₁, hc₁, hX₁bound⟩ := hX₁
  obtain ⟨c₂, hc₂, hX₂bound⟩ := hX₂
  have hSu : 0 < p.S * u := mul_pos hS hu
  obtain ⟨a₀, ha₀, homit⟩ := eventually_omission_tail hp hc₁ hc₂ hSu
  have homitSrc := src.mono.tendsto_atTop.eventually homit
  have hsmall := tailLemma hN hNt hκ hsub
    (show IsPowerSmall N X₁ from ⟨c₁, hc₁, hX₁bound⟩)
    (show IsPowerSmall N X₂ from ⟨c₂, hc₂, hX₂bound⟩)
  obtain ⟨e, he, he1, hraw⟩ := exists_raw_sample_bounds hN hNt hκ hsub hχ
    (show τ < χ by linarith only [hτχ, hχ]) hup hvGap hgap hclose hE
  have hpin := eventually_long_scale hN hNt hκ hsub hu
  have hceil := eventually_source_list_ceil hN hNt hκ hsub (show 0 < p.S * u / 16 by positivity)
  have htwo : ∀ᶠ n in atTop, (2 : ℝ) ≤ N n ^ (p.S * u / 100) :=
    ((tendsto_rpow_atTop (show 0 < p.S * u / 100 by positivity)).comp hNt).eventually_ge_atTop 2
  have hprofileRaw : p.f (r 0) - p.f 0 + τ + 4 * band +
      2 * (8 * u + 2 * band) + χ / 2 ≤ ds * s + χ := by
    have hpr := (abs_le.mp hprofile).2
    have hdsr : ds * r 0 ≤ ds * s := mul_le_mul_of_nonneg_left hrs hds
    linarith only [hpr, hdsr, hτχ, hbandχ, huχ, hχ]
  refine ⟨{
    u := u
    τ := τ
    e := e
    a₀ := a₀
    ell := min e (p.S * u / 16)
    u_pos := hu
    u_eta := huη
    packing_u := hup.le
    a₀_pos := ha₀
    ell_pos := lt_min he (by positivity)
    ell_four := (min_le_left _ _).trans (he1.trans (by norm_num))
    profile := hprofileRaw
    time := ?_
    events := ?_ }⟩
  · intro n
    exact (src.time n 0 (by omega)).2.1.trans
      (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (hN n) htime)
  · intro loss hloss hlossSmall
    have hlossE : loss ≤ e := hlossSmall.trans (min_le_left _ _)
    have hlossSu : loss ≤ p.S * u / 16 := hlossSmall.trans (min_le_right _ _)
    filter_upwards [hX₁bound, hX₂bound, homitSrc, hsmall, hraw, hpin, hceil, htwo]
      with n hx₁ hx₂ ho hsm hn hpN hcN htwoN
    have hCceil : (⌈p.N (src.index n) ^ loss⌉₊ : ℝ) ≤
        p.N (src.index n) ^ (loss + p.S * u / 100) := current_list_ceil_le (hN n) hloss.le htwoN
    have homitN := ho (X₁ n) (X₂ n) ⌈p.N (src.index n) ^ loss⌉₊ ⌈κ n⌉₊
      (loss + p.S * u / 100) (p.S * u / 16) τ hx₁ hx₂ hCceil hcN
      (by positivity) (by positivity) (by linarith only [hlossSu, hτSu, hSu])
    refine ⟨hn.1, hn.2 loss hlossE, hpN, hsm, ?_⟩
    simpa only [neg_mul] using homitN

/-- All eventual D-side numerical and original-law data from the
actual homogeneous source hypotheses. -/
theorem exists_source_d_data {p : Data} (hp : Valid p) (hL : p.L = 1)
    {kr w ε q band : ℝ} {M D : ℕ} {sd r : ℕ → ℝ}
    (src : HomogeneousSourceSequence p kr w ε q band 2 M D sd r)
    {χ ds s vGap : ℝ} (hχ : 0 < χ) (hds : 0 ≤ ds) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hr0 : 0 ≤ r 0) (hgap : r 0 + vGap ≤ s) (hclose : s - r 0 + 2 * vGap ≤ 2 * χ)
    (hvGap : 0 < vGap) (hband0 : 0 ≤ band) (hbandχ : band ≤ χ / 1000)
    (hband1 : band ≤ 1 / 80)
    (hprofile : |p.f (r 0) - p.f 0 - ds * r 0| ≤ χ / 1000)
    (htime : kr * sd 0 + ε ≤ 1) :
    Nonempty (SourceDData src χ ds s) := by
  exact exists_source_d_data_of_tail eventually_source_tail_lt hp hL src hχ hds hs0 hs1
    hr0 hgap hclose hvGap hband0 hbandχ hband1 hprofile htime

end
end Submission.Obl.k4_raw_localized_native_systems
