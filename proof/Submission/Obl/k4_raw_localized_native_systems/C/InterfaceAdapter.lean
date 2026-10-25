import Submission.Obl.k4_raw_localized_native_systems.C.LocalizationGeneric
import Submission.Obl.k4_raw_localized_native_systems.SplitInterfaces
import Submission.Obl.k4_paired_full_time_binning

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion

set_option maxRecDepth 4096

/-- Accepted paired full-time binning supplies the unconditional input of
the current native-sample factory. -/
theorem pairedFullTimeBinning : PairedFullTimeBinning :=
  Submission.k4_paired_full_time_binning

/-- The current factory's generic native sample has exactly the frozen
localized-sample type, with the same laws, coefficients and certificate. -/
theorem nativeSampleCert_iff_nativeSampleWith (cert : CertificateType)
    (N K : ℝ) (W : ℕ) (ω : Fin W → ℝ) (ν : Fin W → Measure Line)
    (E : Fin W → Set Point) (P : Fin W → MvPolynomial (Fin 4) ℝ) (B : Fin W → ℝ)
    (M D : ℕ) (a₀ w loss h χ d s m S U : ℝ) :
    NativeSampleCert cert N K W ω ν E P B M D a₀ w loss h χ d s m S U ↔
      NativeSampleWith cert false N K W ω ν E P B M D a₀ w loss h χ d s m S U :=
  Iff.rfl

end Submission.Obl.k4_raw_localized_native_systems.C
