import Submission.Obl.k4_raw_localized_native_systems.RawWitnesses
import Submission.Obl.k4_raw_localized_native_systems.SourceSequence

/-!
# The top layer of the raw localization

The frozen statement is reduced to a statement about one prepared nested
source sequence (`SequenceSamples`): the exponents `s, m, U` are fixed for the
extremal setup, and for every accuracy `χ` and thinness `w` the source
parameters (relative narrowness `w'`, depth tolerance `ε`, width error `q`,
profile tolerance `ζ`, the width band and the two target depths `sd 0 < sd 1`) are fixed before
the problem is chosen.  The problem is then taken close enough to the
extremal setup for the nested prefix extraction (`prepared_nested_prefix`) and
for the relative-profile bound, the nested sources are made homogeneous in
width (x0690's `exists_homogeneous_sources`), and the native samples are
produced from the resulting source sequence.
-/

namespace Submission.Obl.k4_raw_localized_native_systems

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_raw_critical_segment_forests

noncomputable section

/-- The native samples of one homogeneous source sequence, for a fixed
accuracy and thinness.  The source parameters are chosen before the problem:
relative narrowness `w'`, depth tolerance `ε`, width error `q`, width band
`band`, relative-profile tolerance `ζ`, and the target depths `sd 0 < sd 1 ≤ 1`
of the earlier and the later system. -/
def SequenceSamples (cert : CertificateType) (ds kr S η s m U χ w : ℝ) : Prop :=
  ∃ (w' ε q band ζ : ℝ) (sd : ℕ → ℝ), 0 ≤ w' ∧ 0 < ε ∧ ε ≤ 1 ∧ 0 < q ∧ 0 < band ∧
    0 < ζ ∧ 0 < sd 0 ∧ sd 0 < sd 1 ∧ sd 1 ≤ 1 ∧
    ∀ p : Data, Valid p → p.L = 1 → p.S = S → p.η = η →
      (∀ r : ℝ, 0 ≤ r → r ≤ 1 → |p.f r - p.f 0 - ds * r| ≤ ζ) →
      ∀ (r : ℕ → ℝ) (M D : ℕ),
        (∀ i, i < 2 → |r i - sd i| ≤ ε ∧ 0 < r i ∧ r i ≤ sd i) →
        HomogeneousSourceSequence p kr w' ε q band 2 M D sd r →
        ∃ (a₀ : ℝ) (M' D' : ℕ), 0 < a₀ ∧ ∀ loss : ℝ, 0 < loss →
          ∃ᶠ k in atTop, NativeSampleWith cert false (p.N k) (p.K k) (p.W k)
            (p.ω k) (p.ν k) (p.E k) (p.P k) (p.B k) M' D' a₀ w loss 1 χ ds s m (S / 2) U

/-- The exponents and the per-accuracy source statement. -/
def SourceSamples (cert : CertificateType) (ds kr S η : ℝ) : Prop :=
  ∃ s m U : ℝ, 0 < s ∧ s < 1 ∧ s < m ∧ 0 < U ∧ U < m ∧
    ∀ χ w : ℝ, 0 < χ → 0 < w → SequenceSamples cert ds kr S η s m U χ w

/-- **The top layer.**  Native samples from every homogeneous source sequence
give the localized systems. -/
theorem localizedSystemsWith_of_sourceSamples {cert : CertificateType}
    (hi : initialRaw) {ds kr S η : ℝ} (hes : es ds kr S η)
    (hnb : ¬ widthRaw ds kr S η) (hsrc : SourceSamples cert ds kr S η) :
    LocalizedSystemsWith cert ds kr S η := by
  obtain ⟨s, m, U, hs0, hs1, hsm, hU0, hUm, hall⟩ := hsrc
  refine ⟨s, m, U, hs0, hs1, hsm, hU0, hUm, ?_⟩
  intro χ w t hχ hw ht
  obtain ⟨w', ε, q, band, ζ, sd, hw', hε, hε1, hq, hband, hζ, hsd0, hsd01, hsd1, hsample⟩ :=
    hall χ w hχ hw
  have hsd : ∀ i, i < 2 → 0 < sd i ∧ sd i ≤ 1 := by
    intro i hi2
    interval_cases i
    · exact ⟨hsd0, hsd01.le.trans hsd1⟩
    · exact ⟨hsd0.trans hsd01, hsd1⟩
  have hstep : ∀ i, i + 1 < 2 → sd i < sd (i + 1) := by
    intro i hi2
    have hi0 : i = 0 := by omega
    subst hi0
    simpa using hsd01
  obtain ⟨p, hp, hprofile, r, M, D, hr, ⟨src⟩⟩ :=
    exists_homogeneous_sources (band := band) hi hes hnb hw' 2 sd (by norm_num) hsd hstep
      hε hε1 hq hband ht hζ
  obtain ⟨hv, hL, hS, hη, hd, hH⟩ := hp
  obtain ⟨a₀, M', D', ha₀, hfreq⟩ := hsample p hv hL hS hη hprofile r M D hr src
  refine ⟨p.N, p.K, p.d, p.W, p.ω, p.ν, p.E, p.P, p.B, p.f, p.g, p.G, ?_, hd, ?_,
    a₀, M', D', ha₀, hfreq⟩
  · have hvalid : Valid p := hv
    unfold Valid at hvalid
    rw [hL, hS, hη] at hvalid
    exact hvalid
  · have hHor : kr - t < Horizon p := hH
    unfold Horizon at hHor
    rw [hL] at hHor
    exact hHor

/-- **The raw localization from source samples.** -/
theorem rawLocalization_of_sourceSamples
    (hsrc : ∀ ds kr S η : ℝ, 0 < S → 0 < η → es ds kr S η →
      SourceSamples RawSupport ds kr S η) :
    RawLocalizationStatement := by
  intro hi ds kr S η hS hη hes hnb
  exact localizedSystemsWith_of_sourceSamples hi hes hnb (hsrc ds kr S η hS hη hes)

end
end Submission.Obl.k4_raw_localized_native_systems
