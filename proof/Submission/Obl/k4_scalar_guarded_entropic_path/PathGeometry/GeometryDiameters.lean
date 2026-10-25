/-
Adapted from this LOT tree, obligation o093, session x0535, commit b0d1e0aa,
Submission/Obl/k4_scalar_critical_path_terminal/GeometryDiameters.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TwoScaleDiameters
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootNesting

/-! Diameter certificates on a fine immutable geometry row. Its one
coarse row is read from the row projection, so ALL incidences in the fine
row use the same current coarse floor and quadratic predictor. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChartGeometry

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_true_terminal_lifting (ChartW)
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction
open ActualPacketGraphs

noncomputable section

def chartOfData {p : Code} {k B : ℕ} (g : Geometry p k) {r b h ε : ℝ} {flag : Bool}
    (Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin g.count))
    (hcd : ChartData p B r b h ε flag k g.generation g.count g.world g.block
      g.assignment g.selected g.center g.speed g.width g.polynomial Λ) :
    ChartW p B r b h ε flag k :=
  ⟨g.generation, g.count, g.world, g.block, g.assignment, g.selected,
    g.center, g.speed, g.width, g.polynomial, Λ, hcd⟩

theorem incidence_diameters {p : Code} (hp : Exact p) {k Bc Bf : ℕ}
    {rc bc hc εc rf bf hf εf : ℝ} {flag : Bool} (coarse fine : Geometry p k)
    (Λc : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin coarse.count))
    (Λf : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin fine.count))
    (hcdc : ChartData p Bc rc bc hc εc true k coarse.generation coarse.count coarse.world coarse.block
      coarse.assignment coarse.selected coarse.center coarse.speed coarse.width coarse.polynomial Λc)
    (hcdf : ChartData p Bf rf bf hf εf flag k fine.generation fine.count fine.world fine.block
      fine.assignment fine.selected fine.center fine.speed fine.width fine.polynomial Λf)
    (π : RowProjection coarse fine) (d : Fin fine.count)
    (hrc : 0 ≤ rc) (hεc : 0 ≤ εc) (ρ : Measure (Coeff × ℝ))
    (B H K : ℝ) (hB : 0 < B) (hH : 0 < H) (hK : 1 ≤ K)
    (hXc : N p k ^ εc ≤ K) (hXf : N p k ^ εf ≤ K) (hBK : B ≤ K) (hHK : H ≤ K)
    (hwidth : (K * (2 : ℝ) ^ coarse.generation)⁻¹ ≤ coarse.width (π.row d))
    (hcap : ρ.map (obsL (N p k ^ (-rc))) ≤
      ENNReal.ofReal (B * N p k ^ (-f p rc)) • (volume.prod Measure.count))
    (hfloor : (ENNReal.ofReal H)⁻¹ * ENNReal.ofReal (((2 : ℝ) ^ coarse.generation)⁻¹) *
      ν p k (coarse.world (π.row d)) (coarse.assignment (π.row d)) ≤
      ρ (coarse.assignment (π.row d) ×ˢ I coarse.generation (coarse.block (π.row d))))
    (z z' : Coeff × ℝ) (hz : z ∈ fine.selected d) (hz' : z' ∈ fine.selected d) :
    |z.2 - z'.2| ≤ ((2 : ℝ) ^ fine.generation)⁻¹ ∧
      |spatial z.1 z.2 - spatial z'.1 z'.2| ≤
        3 * K ^ 2 * ((2 : ℝ) ^ fine.generation)⁻¹ ∧
      |hidden z.1 z.2 - hidden z'.1 z'.2| ≤ 2 * K * N p k ^ (-rc) +
        47589120000000 * K ^ 26 * (((2 : ℝ) ^ fine.generation)⁻¹) /
          (((2 : ℝ) ^ coarse.generation)⁻¹) := by
  let Qc := chartOfData coarse Λc hcdc
  let Qf := chartOfData fine Λf hcdf
  have hzf := ((hcdf.2.2.2.2.1 d) hz).2
  have hzf' := ((hcdf.2.2.2.2.1 d) hz').2
  have hzc := ((hcdc.2.2.2.2.1 (π.row d)) (π.selected_subset d hz)).2
  have hzc' := ((hcdc.2.2.2.2.1 (π.row d)) (π.selected_subset d hz')).2
  have hN : 0 < N p k := by linarith [hp.1.1 k]
  have hb := actual_chart_base_diameter Qf hN K hK hXf d z.1 z'.1
    hzf.1 hzf'.1 z.2 z'.2 hzf.2 hzf'.2
  refine ⟨hb.1, hb.2, ?_⟩
  exact actual_two_scale_hidden_diameter hp Qc Qf hrc hεc (π.row d) d ρ B H K
    hB hH hK hXc hXf hBK hHK hwidth hcap hfloor z.1 z'.1 hzc.1 hzc'.1 hzf.1 hzf'.1
    z.2 z'.2 hzc.2 hzc'.2 hzf.2 hzf'.2

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChartGeometry
