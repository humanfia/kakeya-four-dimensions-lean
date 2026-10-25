import Submission.Obl.k4_narrow_projected_row_parents.Witness
import Submission.Obl.k4_general_parent_projected_layers.Layers
import Submission.Obl.k4_narrow_projected_row_parents.RefinementSequence

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory
open Submission.Obl.k4_general_parent_projected_layers

variable {α : Type} [MeasurableSpace α]
variable {cfg : Model α} {L a m s : ℝ} {τ : ℕ → ℕ} {H : ℕ → ℝ}
  {ρ' : ℕ → Measure (α × ℝ)} {β : ℕ → ℝ → ℝ} {n' : ℕ → ℝ → ℕ}
  {C : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Set α}
  {tag : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Fin 2 → ℤ}
  {u v : (k : ℕ) → (s : ℝ) → Fin (n' k s) → ℝ}
  {G : (k : ℕ) → (s : ℝ) → Fin (n' k s) → MvPolynomial (Fin 2) ℝ} {k : ℕ}

/-- The frozen slice is a good layer in the accepted prepared-model interface. -/
theorem Model.Slice.good_layer (h : Model.Slice cfg false L a m τ H ρ' β n' C tag u v G k s) :
    (⟨n' k s, β k s, C k s, tag k s, u k s, v k s, G k s⟩ : ProjLayer α).Good
      (cfg.N (τ k)) (H k) cfg.d cfg.ℓ (L * a) s (cfg.N (τ k) ^ (-m))
      (cfg.b (τ k)) (cfg.P (τ k)) (cfg.π (τ k)) (cfg.ρ (τ k)) := by
  obtain ⟨hβ, hlo, hup, hmeas, hdisj, hlabels, -⟩ := h
  refine ⟨hβ, ?_, hup, hmeas, hdisj, hlabels⟩
  simpa only [Bool.false_eq_true, ite_false, neg_mul] using hlo

/-- The explicit frozen reference budget is unchanged by packaging a slice as a layer. -/
theorem Model.Slice.layer_weight_sum (h : Model.Slice cfg false L a m τ H ρ' β n' C tag u v G k s) :
    (∑ i, (⟨n' k s, β k s, C k s, tag k s, u k s, v k s, G k s⟩ : ProjLayer α).weight
      (cfg.N (τ k)) cfg.d s (cfg.N (τ k) ^ (-m)) (cfg.π (τ k)) i) ≤ ENNReal.ofReal (H k) := by
  exact h.2.2.2.2.2.2.1

/-- The retained slice law is covered by projected assignments at actual unit times. -/
theorem Model.NarrowWitness.covered_in_unit (hv : Model.Valid cfg)
    (hw : Model.NarrowWitness cfg L a m s τ H ρ' β n' C tag u v G) (k : ℕ) :
    ∀ᵐ z ∂ρ' k, z.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∃ i, z.1 ∈ C k s i := by
  obtain ⟨-, -, -, -, hρμ, hsupp, -⟩ := hv.basic (τ k)
  have htime : ∀ᵐ z ∂cfg.μ (τ k), z.2 ∈ Set.Icc (0 : ℝ) 1 := by
    have ht : ∀ᵐ z ∂cfg.μ (τ k), z ∈ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 :=
      ae_iff.mpr hsupp
    exact ht.mono fun z hz => hz.2
  have htime' := ae_mono ((hw.retained k).1.trans hρμ) htime
  filter_upwards [htime', (hw.slice k).2.2.2.2.2.2.2] with z hz hc
  exact ⟨hz, hc⟩

/-- The frozen normalized witness admits a dense projected layer at any prescribed
finer major exponent, with the original width and original reference floors. -/
theorem Model.NarrowWitness.refined_layers (hv : Model.Valid cfg)
    (hw : Model.NarrowWitness cfg L a m s id H ρ' β n' C tag u v G)
    (chiExp : ℝ) (hFine : m ≤ chiExp) :
    Model.Subpow cfg.N (fun k => 4 * H k ^ 2) ∧
    ∃ (Lf : ℕ → ProjLayer α) (ζf : ℕ → Measure (α × ℝ))
      (toOld : (k : ℕ) → Fin (Lf k).n → Fin (n' k s)), ∀ k,
      ζf k ≤ ρ' k ∧ ENNReal.ofReal ((4 * H k ^ 2)⁻¹) ≤ ζf k Set.univ ∧ (Lf k).β = β k s ∧
      (Lf k).Good (cfg.N k) (4 * H k ^ 2) cfg.d cfg.ℓ (L * a) s
        (cfg.N k ^ (-m) / MajorRefinement.factor (cfg.N k ^ (-m)) (cfg.N k ^ (-chiExp)))
        (cfg.b k) (cfg.P k) (cfg.π k) (cfg.ρ k) ∧
      (∀ i, (Lf k).C i ⊆ C k s (toOld k i) ∧ (Lf k).u i = u k s (toOld k i) ∧
        (Lf k).v i = v k s (toOld k i) ∧ (Lf k).G i = G k s (toOld k i)) ∧
      (∀ᵐ z ∂ζf k, ∃ i, z.1 ∈ (Lf k).C i) ∧
      cfg.N k ^ (-chiExp) / 2 ≤ cfg.N k ^ (-m) /
        MajorRefinement.factor (cfg.N k ^ (-m)) (cfg.N k ^ (-chiExp)) ∧
      cfg.N k ^ (-m) / MajorRefinement.factor (cfg.N k ^ (-m)) (cfg.N k ^ (-chiExp)) ≤
        cfg.N k ^ (-chiExp) := by
  let layers : ℕ → ProjLayer α := fun k =>
    ⟨n' k s, β k s, C k s, tag k s, u k s, v k s, G k s⟩
  exact MajorRefinement.exists_refined_layers cfg.N H (fun k => by linarith [hv.scale k])
    hv.scale_limit (fun k => (hw.loss k).1) hw.loss_subpower cfg.d cfg.ℓ (L * a) s m chiExp hFine
    cfg.b (fun k => (hv.basic k).1) cfg.P cfg.π cfg.ρ ρ' layers
    (fun k => (hw.slice k).good_layer) (fun k => (hw.slice k).layer_weight_sum)
    (fun k => (hw.retained k).1) (fun k => (hw.retained k).2) (hw.covered_in_unit hv)

/-- The frozen normalized witness admits a dense projected layer at any prescribed
finer major width, with the original width and original reference floors. -/
theorem Model.NarrowWitness.refined_layers_at_width (hv : Model.Valid cfg)
    (hw : Model.NarrowWitness cfg L a m s id H ρ' β n' C tag u v G)
    (ξ : ℕ → ℝ) (hξ : ∀ k, 0 < ξ k)
    (hξold : ∀ k, ξ k ≤ cfg.N k ^ (-m)) :
    Model.Subpow cfg.N (fun k => 4 * H k ^ 2) ∧
    ∃ (Lf : ℕ → ProjLayer α) (ζf : ℕ → Measure (α × ℝ))
      (toOld : (k : ℕ) → Fin (Lf k).n → Fin (n' k s)), ∀ k,
      ζf k ≤ ρ' k ∧ ENNReal.ofReal ((4 * H k ^ 2)⁻¹) ≤ ζf k Set.univ ∧ (Lf k).β = β k s ∧
      (Lf k).Good (cfg.N k) (4 * H k ^ 2) cfg.d cfg.ℓ (L * a) s
        (cfg.N k ^ (-m) / MajorRefinement.factor (cfg.N k ^ (-m)) (ξ k))
        (cfg.b k) (cfg.P k) (cfg.π k) (cfg.ρ k) ∧
      (∀ i, (Lf k).C i ⊆ C k s (toOld k i) ∧ (Lf k).u i = u k s (toOld k i) ∧
        (Lf k).v i = v k s (toOld k i) ∧ (Lf k).G i = G k s (toOld k i)) ∧
      (∀ᵐ z ∂ζf k, ∃ i, z.1 ∈ (Lf k).C i) ∧
      ξ k / 2 ≤ cfg.N k ^ (-m) /
        MajorRefinement.factor (cfg.N k ^ (-m)) (ξ k) ∧
      cfg.N k ^ (-m) / MajorRefinement.factor (cfg.N k ^ (-m)) (ξ k) ≤
        ξ k := by
  let layers : ℕ → ProjLayer α := fun k =>
    ⟨n' k s, β k s, C k s, tag k s, u k s, v k s, G k s⟩
  exact MajorRefinement.exists_refined_layers_at_width cfg.N H (fun k => by linarith [hv.scale k])
    hv.scale_limit (fun k => (hw.loss k).1) hw.loss_subpower cfg.d cfg.ℓ (L * a) s m ξ hξ hξold
    cfg.b (fun k => (hv.basic k).1) cfg.P cfg.π cfg.ρ ρ' layers
    (fun k => (hw.slice k).good_layer) (fun k => (hw.slice k).layer_weight_sum)
    (fun k => (hw.retained k).1) (fun k => (hw.retained k).2) (hw.covered_in_unit hv)

end Submission.Obl.k4_narrow_projected_row_parents
