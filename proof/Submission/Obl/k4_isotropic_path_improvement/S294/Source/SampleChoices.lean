-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleChoices, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The census and MK4 choices of a sample, as definitions (session x1088).

All are functions of the sample's scalars: the path factor `κ`, the source factor `Kd = d.K k`,
`N = d.N k`, `δ₀`, `L`, the prepared tolerance `τ` (the core constant is the envelope at `τ + τ`),
the front exponent `ub` (`rF = N^(-ub L)`), the grid `m`, the window `C`, `d₁` and the native fit
target `θN = N^(-graphTargetCoeff gain L)`:
* `KgeomAt`, `KcenAt` (the ONE census constant), `CbandAt`, `KgAt` (`mk4Kg` at `Vmax = 2 Kd`,
  `c = κ⁻¹/512`, front radius `rF`), `stepsAt`, `TmAt`, `nmeshAt`, `fineAt`, `cellRateAt`,
  `durationRateAt`, `θrowAt`, `δrefAt`;
* `nfamAt` (the family `i, …, i + C - g`), `thetaNAt`. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleFamily
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.MK4Numerics
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeDesign

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

noncomputable section

/-- `Kgeom` at the sample. -/
def KgeomAt (κ Kd N δ₀ L τ : ℝ) : ℝ :=
  geomOf (Native.nativePreGeometryEnvelope κ Kd N (τ + τ)) N δ₀ L

/-- The census constant at the sample. -/
def KcenAt (κ Kd N δ₀ L τ ub : ℝ) (m : ℕ) : ℝ :=
  censusKOf (KgeomAt κ Kd N δ₀ L τ) FixedSourcePowers.coreRadius FixedSourcePowers.jet
    (stripExpOf (KgeomAt κ Kd N δ₀ L τ) κ N δ₀ L (N ^ (-(ub * L))))
    (rowExpOf FixedSourcePowers.coreRadius) (gapExpOf (KgeomAt κ Kd N δ₀ L τ) N δ₀ L m)

/-- The band constant of the MK4 rows. -/
def CbandAt (κ Kd N δ₀ L τ d₁ : ℝ) : ℝ :=
  64 * (max κ Kd) ^ 2 * κ * 4 ^ d₁ * N ^ (2 * (δ₀ * L) + (τ + 2 * δ₀ * L) + τ)

/-- The MK4 row constant. -/
def KgAt (κ Kd N δ₀ L τ ub d₁ : ℝ) (m : ℕ) : ℝ :=
  mk4Kg κ (2 * Kd) (KcenAt κ Kd N δ₀ L τ ub m) (CbandAt κ Kd N δ₀ L τ d₁) (κ⁻¹ / 512)
    (N ^ (-(ub * L))) (δ₀ * L) N

/-- The census steps. -/
def stepsAt (κ Kd N δ₀ L τ ub : ℝ) (m : ℕ) : ℕ := stepsOf (KcenAt κ Kd N δ₀ L τ ub m)

/-- The MK4 mesh target at the fit target `θN` (with mesh cap `1`). -/
def TmAt (κ Kd N δ₀ L τ ub d₁ θN : ℝ) (m : ℕ) : ℝ :=
  min (min (θN / (80 * KgAt κ Kd N δ₀ L τ ub d₁ m ^ 7)) 1)
    (min (1 / (64 * KgAt κ Kd N δ₀ L τ ub d₁ m))
      (min (1 / (36 * KgAt κ Kd N δ₀ L τ ub d₁ m ^ 4))
        (((1 / 4 : ℝ) / 4) ^ 4 * (κ⁻¹ / 512) ^ 4 /
          (256 * Parent.ParentSource.Broad.Velocity.curvatureRowConstant ^ 3 *
            KgAt κ Kd N δ₀ L τ ub d₁ m ^ 9 + 1))))

/-- The MK4 mesh index (`graphMesh = mesh nmeshAt`). -/
def nmeshAt (κ Kd N δ₀ L τ ub d₁ θN : ℝ) (m : ℕ) : ℕ :=
  meshIndexOf (TmAt κ Kd N δ₀ L τ ub d₁ θN m) d₁

/-- The census fine mesh of the MK4 rows. -/
def fineAt (κ Kd N δ₀ L τ ub d₁ θN : ℝ) (m : ℕ) : ℝ :=
  Submission.Lib.K4DyadicRowScales.mesh (nmeshAt κ Kd N δ₀ L τ ub d₁ θN m) /
    (2 : ℝ) ^ stepsAt κ Kd N δ₀ L τ ub m

/-- The MK4 cell rate. -/
def cellRateAt (κ Kd N δ₀ L τ ub : ℝ) (m : ℕ) : ℝ :=
  (κ⁻¹ / 512) / (KcenAt κ Kd N δ₀ L τ ub m * ((2 : ℝ) ^ stepsAt κ Kd N δ₀ L τ ub m) ^ 3)

/-- The MK4 duration rate. -/
def durationRateAt (κ Kd : ℝ) : ℝ :=
  (κ⁻¹ / 512) / ((3 * (1 + 24 * κ + κ ^ 2 + 2 * Kd) + 3) * 7 ^ 4)

/-- The census row width. -/
def θrowAt (κ Kd N δ₀ L τ : ℝ) : ℝ :=
  (KgeomAt κ Kd N δ₀ L τ ^ rowExpOf FixedSourcePowers.coreRadius)⁻¹

/-- The census deletion reference. -/
def δrefAt (fraction : ℝ) : ENNReal := ENNReal.ofReal (16 * fraction)

/-- The number of levels of the core family. -/
def nfamAt (κ₁ δ₀ ub : ℝ) (m C : ℕ) : ℕ := C + 1 - familyMarginOf κ₁ δ₀ ub m

/-- The native fit target. -/
def thetaNAt (κ₁ d₁ : ℝ) (Ep : ℕ) (precision gain N L : ℝ) : ℝ :=
  N ^ (-(NativeDesign.graphTargetCoeff κ₁ d₁ Ep precision * gain * L))

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
