import Submission.Obl.k4_raw_localized_native_systems.C.HomogeneousSequence
import Submission.Obl.k4_raw_localized_native_systems.C.InterfaceAdapter
import Submission.Obl.k4_raw_localized_native_systems.DSequence
import Submission.Obl.k4_raw_localized_native_systems.NativeMonotonicity
import Submission.Obl.k4_raw_localized_native_systems.SequenceNumerics

namespace Submission.Obl.k4_raw_localized_native_systems

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Every homogeneous source sequence supplies the required native samples,
with formats and omission exponent fixed before the requested loss. -/
theorem sequenceSamples_raw {ds kr S η χ w : ℝ}
    (hds : 0 ≤ ds) (hkr0 : 0 ≤ kr) (hkr1 : kr ≤ 1)
    (hS : 0 < S) (hη : 0 < η) (hχ : 0 < χ) (hw : 0 < w) :
    SequenceSamples RawSupport ds kr S η (sExp kr S η) (mExp kr S η) UExp χ w := by
  refine ⟨wOf kr S η w, epsOf kr S η χ, tolOf kr S η χ, tolOf kr S η χ,
    tolOf kr S η χ, sdOf kr S η χ,
    wOf_nonneg hkr0 hS hη hw.le, epsOf_pos hkr0 hS hη hχ, epsOf_le_one,
    tolOf_pos hkr0 hS hη hχ, tolOf_pos hkr0 hS hη hχ, tolOf_pos hkr0 hS hη hχ,
    sdOf_zero_pos hkr0 hS hη, sdOf_zero_lt_one hkr0 hS hη hχ, sdOf_one_le, ?_⟩
  intro p hp hL hpS hpη hprofile r M D hr src
  obtain ⟨a₀, ell, ha₀, hell, hD⟩ :=
    d_side_of_choice hp hL hds hkr0 hkr1 hS hη hχ hr hprofile src
  obtain ⟨CB, hCB2, hB⟩ := C.exists_b0At C.pairedFullTimeBinning
  have hu : 0 < angU η := angU_pos hη
  have huη : angU η ≤ p.η := by rw [hpη]; exact angU_le hη
  have hτ : 0 < S * angU η / 100 := by positivity
  have hr1 := hr 1 (by omega)
  have hr1L : r 1 ≤ 1 := hr1.2.2.trans sdOf_one_le
  obtain ⟨-, -, htime0, hthin, hrelative, hgap⟩ :=
    choice_sequence_bounds hkr0 hkr1 hS hη hχ hw hr
  obtain ⟨MC, DC, hC⟩ := C.localized_eventually_homogeneous hCB2 hB RawSupport p hp hL src
    (d := ds) (s' := sExp kr S η) (m := mExp kr S η) (Sₛ := S / 2) (U := UExp)
    hu huη hτ ha₀ hχ hw hr1.2.1 hr1L hthin (by rw [hpS]; exact hgap)
  refine ⟨a₀, MC, DC, ha₀, ?_⟩
  intro loss hloss
  let small := min loss (min ell (χ / 2))
  have hsmall : 0 < small := lt_min hloss (lt_min hell (by positivity))
  have hsmall_loss : small ≤ loss := min_le_left _ _
  have hsmall_ell : small ≤ ell := (min_le_right _ _).trans (min_le_left _ _)
  have hsmall_chi : small < χ := by
    have hh : small ≤ χ / 2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hκ := src.subpower (1 / 16) (by norm_num)
  apply frequently_of_eventually_index src.mono
  filter_upwards [hC small hsmall hsmall_chi, hD small hsmall hsmall_ell, hκ] with n hCn hDn hκn
  apply nativeSampleWith_mono_loss (ε := small) (hp.scale_ge_one (src.index n))
    (fun γ => (hp.B_pos (src.index n) γ).le) hsmall_loss
  apply nativeSampleWith_of_cert
  apply hCn
  intro Λ hΛm hΛc hΛk g hg hg1 hgn
  apply hDn MC DC Λ g hg hg1
  apply relative_width_at hp (src.core n) (src.width_exact n) (src.width_band n)
    (A := 3 * angU η + 1) (h := kr * sdOf kr S η χ 0 + epsOf kr S η χ)
    (e := 1 / 16) (ϑ := 4) (src.time n 0 (by omega)).2.1 hκn
    (by simpa only [add_assoc] using hgn)
  have hgapwidth := (src.width_lower n 0 (by omega)).2
  norm_num only [Nat.cast_ofNat, Nat.reduceSub] at hgapwidth
  linarith only [hgapwidth, hrelative]

/-- The frozen scalar and window exponents work for every accuracy and
requested thinness in an extremal setup. -/
theorem sourceSamples_raw {ds kr S η : ℝ} (hS : 0 < S) (hη : 0 < η)
    (hes : es ds kr S η) : SourceSamples RawSupport ds kr S η := by
  have hkr0 : 0 ≤ kr := hes.2.2.1.le
  refine ⟨sExp kr S η, mExp kr S η, UExp, sExp_pos hkr0 hS hη,
    sExp_lt_one, sExp_lt_mExp, UExp_pos, UExp_lt_mExp hkr0 hS hη, ?_⟩
  intro χ w hχ hw
  exact sequenceSamples_raw hes.1 hkr0 hes.2.2.2.1 hS hη hχ hw

/-- Raw localization from the initial horizon bound and the original
extremal setup, retaining the raw earlier laws throughout. -/
theorem raw_localization : RawLocalizationStatement :=
  rawLocalization_of_sourceSamples fun _ _ _ _ hS hη hes => sourceSamples_raw hS hη hes

end
end Submission.Obl.k4_raw_localized_native_systems
