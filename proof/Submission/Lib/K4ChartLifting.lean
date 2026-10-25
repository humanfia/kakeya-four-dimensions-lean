import Submission.Lib.K4ChartLifting.Basic
import Submission.Lib.K4ChartLifting.PolyAlgebra
import Submission.Lib.K4ChartLifting.Normalize
import Submission.Lib.K4ChartLifting.Bounds
import Submission.Lib.K4ChartLifting.Format
import Submission.Lib.K4ChartLifting.Mass
import Submission.Lib.K4ChartLifting.Lift
import Submission.Lib.K4ChartLifting.Atlas
import Submission.Lib.K4ChartLifting.Normalized
import Submission.Lib.K4ChartLifting.Prior
import Submission.Lib.K4ChartLifting.NormFormat
import Submission.Lib.K4ChartLifting.Sizes
import Submission.Lib.K4ChartLifting.SampleNormalize
import Submission.Lib.K4ChartLifting.NormPriorForm
import Submission.Lib.K4ChartLifting.NormalizeProblem
import Submission.Lib.K4ChartLifting.NormDensity
import Submission.Lib.K4ChartLifting.NormDensityFormula
import Submission.Lib.K4ChartLifting.DensityLemmas
import Submission.Lib.K4ChartLifting.NormAngular
import Submission.Lib.K4ChartLifting.NormMass
import Submission.Lib.K4ChartLifting.NormCompare
import Submission.Lib.K4ChartLifting.NormTerminal

/-!
# Version-2 chart systems: normalization and lifting

Adapted from: here:o049 (the chart layout of `Basic.lean`, see its header); all other code
was written in this workspace by x0214 on o064 (`k4_terminal_charts_from_scalar_mesh_row_fit`).

Finite chart systems laid out exactly as in the frozen terminal-chart assertion
of this tree (o049/o064): trajectories `ℕ × ℝ⁶`, graph points, dyadic blocks,
the Boolean sign format (`PolynomialFormat`, with the calculus `Fmt`), and
`ChartSystem.Valid`, every chart condition of the frozen conclusion at one sample.

Main result: `ChartSystem.lift_valid` (paper Lemma 2.13, lifting part). Given a
known atlas `s₀` (only its geometry, `ChartSystem.Geometry`, is used) and a valid
system `s'` of the normalized problem whose worlds are the charts of `s₀`
(normalized priors `ν' c = ν(A_c)⁻¹ • (normTraj)_* ν|_{A_c}`, events corresponding
to the original ones, e.g. `Frame.normEvent`, derivative scales `B / δr`, weights
`∝ ω q ν(A_c)`), the lifted system `s₀.lift E δr s'` -- dyadic blocks subdivided,
centers and frames composed, tests `δr · R'(τ, z, w)` -- is valid for the original
problem at the composed thickness, with the true floor and total mass composed as
`m = q ν(A_c) m'` (paper (2.13)). Supporting results: the pderiv chain rule under
`MvPolynomial.bind₁`, degree and `ℓ¹` coefficient bounds for affine substitutions,
format preservation under affine preimages and intersections, the product-measure
change of variables for normalized incidences, size bounds of lifted data,
`ChartSystem.Valid.geometry` and `ChartSystem.Valid.mono`.

Normalization half, at one sample: the normalized native test `Frame.normTest`
(`P_c / δ_r` in the coordinates `(τ, z, w)`), native bounds of normalized worlds
(`ChartSystem.norm_native_bounds`), the lower native bound (`Frame.normTest_lower`), the
mass of normalized events (`Frame.prod_normEvent`), and the normalized prior
(`Frame.map_normTraj_prior`: piecewise Lebesgue on the pieces
`denormCoeff ⁻¹' (A j ∩ {x | (i j, x) ∈ A₀})`, densities times `|det normMatrix|⁻¹`,
`det normMatrix = q³ (det D⁻¹)²`).

`SampleProblem`: the per-sample conditions of the frozen problem predicate.
`SampleProblem.normalize`: normalizing through an atlas preserves them (all conditions
except the density hypotheses), with explicit slack and format bounds.
`Frame.normalized_obs_law`, `Frame.normalized_obs_ac`: normalized observation laws in terms
of the original ones (base change of the observation at the composed width), and their
absolute continuity; `Frame.normalized_obs_density`, the exact density transform (2.15).
`density_le_of_le`, `density_vanishes_off_lists`, `refinement_lists`: density comparison for
restricted laws and the list-refinement bound of paper Lemma 2.3.
`Frame.normalized_joint_le`: the angular cap transfers to normalized problems (a normalized
velocity bin meets `(2⌈κ⌉+1)²` original ones when `Σ |D| ≤ κ q`).
`ChartSystem.normalized_exceptional_le`, `ChartSystem.normZ_inv_le`: weighted exceptional
masses of the normalized problem are at most `2κ` times those of the original problem.
`density_depth_le`: densities at the sample decrease with depth (nested dyadic bins).
`ChartSystem.normalized_upper_comparison`: intermediate upper comparison of normalized densities
(`g'_c ≤ (J_c/ν_c) g` at any fixed coarser original depth, off `2 Z⁻¹` times exceptional mass).
`ChartSystem.normalized_terminal_lower`: terminal lower comparison from lists
(`g'_c ≥ (J_c/ν_c) ε g_L` off `Z⁻¹ (2 · exceptional + ε κ · total)` mass).
-/
