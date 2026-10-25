-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.MultiscaleCoreBudget, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.MultiscaleCoreSource

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Native
open scoped ENNReal BigOperators

noncomputable section

-- This strengthens the existing local MultiscaleCoreSource proof, originally
-- written in this LOT tree by x0943 on o265 (83ada3e4), ported by x1082/x1095.
-- It retains the original global deletion estimate when constructing the
-- core structure, so subsequent cuts may use the full front mass reserve.
/-- Fixed branch exponents construct a common original core source with
fixed original mass at every prescribed finite family of valid depths. -/
theorem exists_broad_multiscale_core_source_with_budget :
    ∃ e rad : ℕ, 4 ≤ e ∧ 1 ≤ rad ∧
    ∀ {T : Type*} {d : ProblemData}, d.Valid →
    ∀ {k : ℕ} {p : PathData (d.W k)}
      {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ},
      p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
        κ₁ m s δ₀ Mp Dp σ →
    ∀ {H₀ : Fin (d.W k) → Set Event} {u : T → ℝ} {τ ε : ℝ},
    ∀ Q : PreparedAngularPath d k p m H₀ u τ, Q.uniformPureBounds ε → 0 ≤ τ+ε →
      (∀ w, H₀ w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b}) →
    ∀ {i stop : ℕ} {mesh envelope r fraction : ℝ} {θ : ENNReal}
      {F : PaletteFamily Q i stop mesh envelope θ},
    ∀ broad : BroadResidual F r fraction,
    ∀ (n : ℕ) (depth : Fin n → ℕ),
      (∀ j, depth j < m) → (∀ j, 0 ≤ p.r (depth j)) → (∀ j, p.r (depth j) ≤ d.L) →
      (n:ℝ) ≤ nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ+ε) →
      ∃ C : BroadMultiscaleCoreSource d k p broad.residual n depth
        (nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ+ε)) e rad,
        (∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume)
          (broad.residual w\C.current w)) ≤ ENNReal.ofReal (p.κ⁻¹/64) := by
  classical
  obtain ⟨e,rad,he,hrad,hfactory⟩ := exists_broad_multiscale_core_source 40 (by norm_num)
  refine ⟨e,rad,he,hrad,?_⟩
  intro T d hd k p κ₁ m s δ₀ Mp Dp σ hp H₀ u τ ε Q hpure htol hHterminal
    i stop mesh envelope r fraction θ F broad n depth hdepth hr hrL hn
  let K := nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ+ε)
  have hN : 1 ≤ d.N k := by linarith [hd.1 k]
  obtain ⟨hK,hκK,_,_⟩ := native_pre_geometry_envelope_bounds hp.1 hN htol
  have hκp : 0 < p.κ := zero_lt_one.trans_le hp.1
  obtain ⟨H,V,cores,current,hH,hcurrent,hcore,hloss⟩ := hfactory hd hp Q hpure htol hHterminal
    broad n depth hdepth hr hrL (3*rad+58)
  let cost := (n:ENNReal)*(ENNReal.ofReal (K^10)*ENNReal.ofReal ((K^40)⁻¹)+
    ENNReal.ofReal (K^10)*ENNReal.ofReal (2*K^(3*rad+18))*ENNReal.ofReal ((K^(3*rad+58))⁻¹))
  have hbudget : (∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (broad.residual w)) ≤
      (∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (current w))+cost := by
    calc
      _ ≤ ∑ w, ENNReal.ofReal (d.ω k w)*
          (((d.ν k w).prod volume) (current w)+
            ((d.ν k w).prod volume) (broad.residual w\current w)) := by
        apply Finset.sum_le_sum
        intro w _
        apply mul_le_mul' le_rfl
        apply (measure_mono (show broad.residual w⊆current w∪(broad.residual w\current w) from fun z hz => by
          by_cases h : z∈current w
          · exact Or.inl h
          · exact Or.inr ⟨hz,h⟩)).trans
        exact measure_union_le _ _
      _ = (∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (current w))+
          ∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (broad.residual w\current w) := by
        simp only [mul_add,Finset.sum_add_distrib]
      _ ≤ _ := add_le_add le_rfl hloss
  have hcost : cost ≤ ENNReal.ofReal (p.κ⁻¹/64) := by
    apply (mul_le_mul' le_rfl (original_value_core_loss_bound (by linarith : 2 ≤ K) rad)).trans
    exact multiscale_core_loss_small n hp.1 hK hκK hn
  have hdouble : ENNReal.ofReal (p.κ⁻¹/64)+ENNReal.ofReal (p.κ⁻¹/64) ≤
      ∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (broad.residual w) := by
    rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
    convert broad.mass using 1
    congr 1
    ring
  let C : BroadMultiscaleCoreSource d k p broad.residual n depth K e rad := {
    source := H
    measurable := fun j w => (hH j w).1
    subset := fun j w => (hH j w).2.1
    original_law := fun j w => (hH j w).2.2
    values := V
    cores := cores
    current := current
    current_measurable := fun w => (hcurrent w).1
    current_subset := fun w => (hcurrent w).2
    current_cores := hcore
    original_mass := Submission.Obl.k4_scalar_grid_cartesian_field.pruning_mass_floor
      ENNReal.ofReal_ne_top hdouble hbudget hcost }
  refine ⟨C,?_⟩
  exact hloss.trans hcost


end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
