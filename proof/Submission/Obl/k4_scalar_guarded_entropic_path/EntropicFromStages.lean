/-
Adapted from this LOT tree, obligation o168, session x0569, branch x0569,
Submission/Obl/k4_scalar_guarded_tangent_preparation/EntropicFromStages.lean.
The original source is work of this tree; its provenance comments are retained.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.RawStage
import Submission.Obl.k4_scalar_guarded_entropic_path.Construction

/-!
# The entropic path construction from single stages

`EntropicPathConstruction` follows once, for fixed package constants `d κ S`, every stage
index `k`, range `R > 1` and exponent `δ > 0` admit one good raw stage. The diagonal takes
`R k = k + 2` and `δ k = 1 / (k + 1)`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path

open Submission.Obl.k4_scalar_linear_critical_extremizers
open Filter
open scoped Topology

/-- A family of good raw stages for all ranges and exponents gives the output of the
entropic path construction. -/
theorem rawGeometry_of_stages {d κ S : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hS0 : 0 < S) (hS1 : S ≤ 1)
    (hstage : ∀ (k : ℕ) (R δ : ℝ), 1 < R → 0 < δ → ∃ st : RawStage, st.Good d κ S k R δ) :
    ∃ (p : ℕ → Code) (sample : ℕ → ℕ) (scale H buffer B : ℕ → ℝ)
      (M count : ℕ → ℕ) (node : (k : ℕ) → ℝ → Fin (count k))
      (depth time : (k : ℕ) → Fin (count k) → ℝ)
      (layers : (k : ℕ) → Fin (count k) → Layer ((p k).W (sample k)))
      (σ : (k : ℕ) → Fin ((p k).W (sample k)) → MeasureTheory.Measure Incidence),
      RawGeometry p sample scale H buffer B M count node depth time layers σ d κ S ∧
      ReferenceLaws (fun k => (p k).N (sample k) ^ scale k) B d S
        (fun k => (p k).W (sample k)) (fun k => (p k).weight (sample k)) σ := by
  choose st hst using fun k : ℕ => hstage k ((k : ℝ) + 2) (1 / ((k : ℝ) + 1))
    (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith) (by positivity)
  have hR : Tendsto (fun k : ℕ => (k : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hδ : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨hgeom, hlaws⟩ := RawStage.assemble hd0 hd1 hκ0 hκ1 hS0 hS1 st _ _ hR hδ hst
  exact ⟨fun k => (st k).p, fun k => (st k).sample, fun k => (st k).scale,
    fun k => (st k).H, fun k => (st k).buffer, fun k => (st k).B, fun k => (st k).M,
    fun k => (st k).count, fun k => (st k).node, fun k => (st k).depth, fun k => (st k).time,
    fun k => (st k).layers, fun k => (st k).σ, hgeom, hlaws⟩

/-- **Reduction of the entropic path construction to single stages.** -/
theorem entropicPathConstruction_of_stages
    (hstages : Split.Initial → Split.Calculus → Split.Critical →
      ∃ d κ S : ℝ, 0 ≤ d ∧ d < 1 ∧ 0 < κ ∧ κ ≤ 1 ∧ 0 < S ∧ S ≤ 1 ∧
        ∀ (k : ℕ) (R δ : ℝ), 1 < R → 0 < δ → ∃ st : RawStage, st.Good d κ S k R δ) :
    EntropicPathConstruction := by
  intro hI hC hcrit
  obtain ⟨d, κ, S, hd0, hd1, hκ0, hκ1, hS0, hS1, hst⟩ := hstages hI hC hcrit
  obtain ⟨p, sample, scale, H, buffer, B, M, count, node, depth, time, layers, σ, hg, hl⟩ :=
    rawGeometry_of_stages hd0 hd1 hκ0 hκ1 hS0 hS1 hst
  exact ⟨p, sample, scale, H, buffer, B, M, count, node, depth, time, layers, σ, d, κ, S,
    hg, hl⟩

end Submission.Obl.k4_scalar_guarded_entropic_path
