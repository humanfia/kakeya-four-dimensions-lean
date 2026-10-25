/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file WorldJetAssembly.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldSelectionInput
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldSelectedNormal
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalJetWorld

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice

namespace Zoom

/-- One coherent primitive per-world input for the frozen graph. All
floors, palettes, spatial caps and filling refer to original measures and
the global event `R`. The residual selection, lists, time row, residual
comparison and scalar-normal certificate are CONCLUSIONS of the builder. -/
structure OriginalJetWorldInput (D : ScalarData) (H : ℕ → ℝ) (B : ℝ)
    (G : (k : ℕ) → Fin (D.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ)
    (E : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence)
    (M : ℕ) (ε : ℝ) (k : ℕ) where
  g : Fin (D.W k)
  μ : Measure ScalarIncidence
  θ : Measure ScalarLine
  π : Measure ℝ
  finite_mu : IsFiniteMeasure μ
  finite_theta : IsFiniteMeasure θ
  finite_pi : IsFiniteMeasure π
  R : Set ScalarIncidence
  ρ : ℝ
  Hc : ℝ
  Krow : ℝ
  Hrow : ℝ
  A : ℝ
  ζ : ℝ
  σ : ℝ
  q : Fin 5 → ℤ
  primitive : OriginalWorldSelectionInput μ θ π R (E k g) ρ (D.N k ^ (-B))
    (H k) Hc Krow Hrow A ζ σ q (G k g)
  caps : OriginalWorldCaps θ R ρ ζ D.d q
  filling : GlobalWorldFilling R ρ (D.N k ^ (-B)) ζ D.d
  b_le_rho : D.N k ^ (-B) ≤ ρ
  Knormal : ℝ
  U : ℝ
  δ : ℝ
  P : ℝ
  δc : ℝ
  one_le_Knormal : 1 ≤ Knormal
  U_pos : 0 < U
  delta_pos : 0 < δ
  P_pos : 0 < P
  density_cap : μ ≤ ENNReal.ofReal U • θ.prod volume
  coefficient_positive : θ {l | cell ρ l.2 = q} ≠ 0
  mass_floor : ENNReal.ofReal δ * θ {l | cell ρ l.2 = q} ≤ μ (R ∩ {p | cell ρ p.1.2 = q})
  selection_cost : (∏ i ∈ Finset.range primitive.n, ((4 : ℝ≥0∞) ^ 3 * primitive.K i)) ≤
    ENNReal.ofReal P
  mass_budget : U * P / δ ≤ Knormal
  row_budget : Hrow ≤ Knormal
  row_compare_budget : 12 * worldRowConstant Hc Krow ^ 2 ≤ Knormal
  residual_budget : 6 * (A + Hrow + 5) ≤ Knormal
  absolute_cap_budget : 9 * caps.H ^ 2 * caps.A ^ 4 ≤ Knormal
  conditional_cap_budget : 9 * caps.H ^ 2 * caps.A ^ 4 / caps.η ≤ Knormal
  support_budget : filling.supportBound Hrow ≤ Knormal
  coarse_compare : ∀ p ∈ R, cell ρ p.1.2 = q →
    |filling.row (assignedCell ρ (D.N k ^ (-B)) p) 1 -
      G k g (cell (D.N k ^ (-B)) (scalarPosition p)) 1| ≤ δc
  support_precision : ∀ v,
    2 * (δc + 4 * worldRowConstant Hc Krow ^ 2 * ρ) +
      (1 + |filling.row v 0| + |filling.row v 1|) * D.N k ^ (-B) / ρ ≤ ζ
  failed : ∀ p ∈ R, ∃ i : Fin (D.n k 1),
    D.γ k 1 i = g ∧ p.1 ∈ D.A k 1 i ∧ p.2 ∈ timeBlock (D.T k 1) (D.j k 1 i) ∧
      ¬ (D.toQualificationTable B G E).rationalFit M ε k i p
  interior : ∀ p ∈ R, ∀ i : Fin (D.n k 1),
    p.2 ∈ timeBlock (D.T k 1) (D.j k 1 i) →
      p.2 ∈ Ioo (((D.j k 1 i : ℕ) : ℝ) / (2 : ℝ) ^ D.T k 1)
        ((((D.j k 1 i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ D.T k 1)
  graph_margin : σ ≤
    (((2 : ℝ) ^ D.T k 1)⁻¹) ^ M * (((2 : ℝ) ^ D.T k 1)⁻¹) ^ ((1 : ℝ) / 8)
  row_margin : 4 * worldRowConstant Hc Krow ^ 2 * ρ ≤
    (((2 : ℝ) ^ D.T k 1)⁻¹) ^ M * (((2 : ℝ) ^ D.T k 1)⁻¹) ^ ((1 : ℝ) / 8)

noncomputable section

/-- All per-world geometric seams compose from primitive original data.
The two displayed equalities let the outer numerical producer use exactly
its chosen constant and floor. Failed packet labels, interiors and original
coefficient bounds are preserved pointwise through the final restriction. -/
theorem OriginalJetWorldInput.exists_world
    {D : ScalarData} {H : ℕ → ℝ} {B : ℝ}
    {G : (k : ℕ) → Fin (D.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ}
    {E : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence}
    {M : ℕ} {ε : ℝ} {k : ℕ}
    (raw : OriginalJetWorldInput D H B G E M ε k)
    (hd : 0 ≤ D.d) (hd₁ : D.d ≤ 1) :
    ∃ w : OriginalJetWorld D H B G E M ε k, w.K = raw.Knormal ∧ w.ζ = raw.ζ := by
  letI : IsFiniteMeasure raw.μ := raw.finite_mu
  letI : IsFiniteMeasure raw.θ := raw.finite_theta
  letI : IsFiniteMeasure raw.π := raw.finite_pi
  obtain ⟨sel⟩ := raw.primitive.select
  have hnormal := scalarNormal_of_selected_original_world sel raw.caps raw.filling
    raw.primitive.rho_pos raw.primitive.b_pos raw.b_le_rho
    raw.primitive.zeta_pos raw.primitive.zeta_le_one hd hd₁
    raw.primitive.one_le_H raw.primitive.Hrow_nonneg raw.primitive.coeff_bound raw.primitive.time_mem
    raw.U_pos raw.delta_pos raw.P_pos raw.one_le_Knormal raw.density_cap raw.coefficient_positive
    raw.mass_floor raw.selection_cost raw.mass_budget raw.row_budget raw.row_compare_budget
    raw.residual_budget raw.absolute_cap_budget raw.conditional_cap_budget raw.support_budget
    raw.coarse_compare raw.support_precision
  have hphys (p : ScalarIncidence) :
      D.phys k B p = cell (D.N k ^ (-B)) (scalarPosition p) := rfl
  refine ⟨{
    g := raw.g
    θ := raw.θ
    finite_prior := raw.finite_theta
    ρ := raw.ρ
    rho_pos := raw.primitive.rho_pos
    q := raw.q
    event := sel.event
    F := sel.F
    β := raw.caps.β
    K := raw.Knormal
    ζ := raw.ζ
    normal := hnormal
    sub := fun p hp => raw.primitive.sub (sel.sub hp).1
    failed := fun p hp => raw.failed p (sel.sub hp).1
    interior := fun p hp => raw.interior p (sel.sub hp).1
    original_coeff := fun p hp => raw.primitive.coeff_bound p (sel.sub hp).1
    graph_error := ?_
    row_error := ?_
  }, rfl, rfl⟩
  · intro p hp
    simpa only [hphys] using (raw.primitive.graph_error p (sel.sub hp).1).trans raw.graph_margin
  · intro p hp
    simpa only [hphys] using (sel.row_close p hp).trans raw.row_margin

end

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
