import Submission.Obl.k4_general_parent_wide_layer_candidates.Lists.Geometry
import Submission.Obl.k4_wide_velocity_lists_scalar_preparation.ScalarCaps
import Submission.Obl.k4_wide_velocity_lists_scalar_preparation.NativeCaps

/-!
# Integrating one scalar residual cell against the native fine caps

Adapted from accepted o248 (`k4_wide_velocity_lists_scalar_preparation/FrameCaps.lean`)
to the general parent: the integrated signal is the native signal `P(x)`. The generic
cap transfer lemmas of o248 are imported and reused.
-/

set_option maxHeartbeats 1000000

namespace Submission.Obl.k4_general_parent_wide_layer_candidates

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_wide_velocity_lists_scalar_preparation
  (ae_of_scaled_map_domination fine_cell_cap_of_scaled_map_domination
    normalized_residual_cell_cap quadratic_background_variation)

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] {p : Parent α}

/-- The original three-coordinate point associated to a normalized scalar time. -/
def normalizedPoint (p : Parent α) (k : ℕ) (t₀ q : ℝ) (ω : α × ℝ) : Fin 3 → ℝ :=
  ![t₀ + q * ω.2, p.x k ω.1 (t₀ + q * ω.2) 1, p.x k ω.1 (t₀ + q * ω.2) 2]

theorem normalizedPoint_eq (p : Parent α) (k : ℕ) (t₀ q : ℝ) (ω : α × ℝ) :
    p.normalizedPoint k t₀ q ω = p.base k ω.1 (t₀ + q * ω.2) := by
  ext i
  fin_cases i <;> rfl

theorem measurable_trajectory (h : p.Valid) (k : ℕ) :
    Measurable (fun ω : α × ℝ => p.x k ω.1 ω.2) := by
  have hb := (h.basic k).1
  apply Measurable.of_eval
  intro i
  fin_cases i
  · change Measurable (fun ω : α × ℝ => ω.2)
    fun_prop
  · change Measurable (fun ω : α × ℝ => p.b k ω.1 0 + ω.2 * p.b k ω.1 3)
    fun_prop
  · change Measurable (fun ω : α × ℝ => p.b k ω.1 1 + ω.2 * p.b k ω.1 4)
    fun_prop
  · change Measurable (fun ω : α × ℝ => p.b k ω.1 2 + ω.2 * p.b k ω.1 5)
    fun_prop

/-- The native signal is measurable on incidences. -/
theorem measurable_signal (h : p.Valid) (k : ℕ) :
    Measurable (fun ω : α × ℝ => p.signal k ω.1 ω.2) :=
  (p.P k).continuous_eval.measurable.comp (measurable_trajectory h k)

namespace ListFrame

variable {k : ℕ} {r v m ε : ℝ} (f : p.ListFrame k r v m ε)

/-- The original full parent reference dominates a strictly positive explicit
weight. This weight, rather than any retained entry mass, pays for the caps. -/
theorem explicit_original_domination (h : p.Valid) (a : ParentGeometry p k r) :
    ENNReal.ofReal
      ((p.N k ^ (-r)) ^ p.d * f.q ^ 3 * p.N k ^ (-p.ℓ * r) / p.K k) •
      f.law.map (fun ω => (ω.1, f.t₀ + f.q * ω.2)) ≤ p.μ k := by
  have hprior := a.prior_lower f.parent
  rw [← f.q_eq] at hprior
  have hweight : ENNReal.ofReal
      ((p.N k ^ (-r)) ^ p.d * f.q ^ 3 * p.N k ^ (-p.ℓ * r) / p.K k) ≤
      ENNReal.ofReal f.q * p.ν k (p.A k r f.parent) := by
    rw [show (p.N k ^ (-r)) ^ p.d * f.q ^ 3 * p.N k ^ (-p.ℓ * r) / p.K k =
      f.q * ((p.N k ^ (-r)) ^ p.d * f.q ^ 2 * p.N k ^ (-p.ℓ * r) / p.K k) by ring,
      ENNReal.ofReal_mul f.q_pos.le]
    exact mul_le_mul' le_rfl hprior
  apply le_trans _ (f.original_domination.trans (h.basic k).2.2.2.2.1)
  intro E
  simpa only [Measure.smul_apply, smul_eq_mul] using mul_le_mul' hweight
    (le_refl ((f.law.map (fun ω => (ω.1, f.t₀ + f.q * ω.2))) E))

/-- Uniform original base bounds transfer to every incoming normalized frame. -/
theorem normalized_base_bound_ae (h : p.Valid) (a : ParentGeometry p k r) :
    ∀ᵐ ω ∂f.law, ∀ e : Fin 3,
      |p.normalizedPoint k f.t₀ f.q ω e| ≤ 2 * p.K k := by
  have hN : 0 < p.N k := by linarith [h.scale k]
  have hK : 0 < p.K k := by linarith [h.subpower.1 k]
  have hW : 0 < (p.N k ^ (-r)) ^ p.d * f.q ^ 3 *
      p.N k ^ (-p.ℓ * r) / p.K k := by
    have hq := f.q_pos
    positivity
  have hf : Measurable (fun ω : α × ℝ => (ω.1, f.t₀ + f.q * ω.2)) := by fun_prop
  have hh := ae_of_scaled_map_domination f.law (p.μ k) _ hf hW
    (f.explicit_original_domination h a) (h.base_bound_ae k)
  filter_upwards [hh] with ω hω
  simpa only [normalizedPoint_eq] using hω

/-- Integrating one scalar residual cell against a fine original native joint cap.
The external factor may be an original velocity palette atom. -/
theorem original_scalar_cell_cap
    (h : p.Valid) (a : ParentGeometry p k r)
    {ξ δ Δ L : ℝ} (hξ : 0 < ξ) (hδ : 0 < δ) (hΔ : 0 < Δ)
    (hδ1 : δ ≤ 1) (hξg : ξ ≤ p.N k ^ (-p.ℓ * r))
    (hL : 0 ≤ L)
    (hδcell : δ ≤ f.q * ξ)
    (hδtrans : δ ≤ 2 * p.K k * f.q * p.N k ^ (-p.ℓ * r))
    (hmcell : L * δ ≤ f.q * ξ)
    (hmtrans : L * δ ≤ 2 * p.K k * f.q * p.N k ^ (-p.ℓ * r))
    (hv₁ : |f.zv| ≤ L)
    (hv₂ : |p.c k r f.parent 3 + p.c k r f.parent 4 * f.zv| ≤ L)
    (hbg : 216 * p.N k ^ (m / 10) * (2 * p.K k) ^ 2 * δ ≤ Δ)
    (condition : α × ℝ → Prop) (hcond : MeasurableSet {ω | condition ω})
    (weight : ℝ≥0∞)
    (hcap : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      p.μ k {ω | (fun i : Fin 3 =>
        ⌊(![ω.2, p.x k ω.1 ω.2 1, p.x k ω.1 ω.2 2] : Fin 3 → ℝ) i / δ⌋) = q ∧
        ⌊p.signal k ω.1 ω.2 / Δ⌋ = j ∧ condition ω} ≤
          ENNReal.ofReal (p.K k * δ ^ 3 * Δ ^ p.d) * weight)
    (β : Fin 2 → ℤ) (j : ℤ) :
    f.law {ω | scalarCell (f.coeff ω.1) ω.2 ξ = β ∧
      ⌊scalarX (f.coeff ω.1) ω.2 / Δ⌋ = j ∧
      condition (ω.1, f.t₀ + f.q * ω.2)} ≤
      ENNReal.ofReal (8400 * p.K k ^ 3 *
        ((p.N k ^ (-r)) ^ p.d)⁻¹ * ξ ^ 2 * Δ ^ p.d) * weight := by
  let A := (p.N k ^ (-r)) ^ p.d
  let g := p.N k ^ (-p.ℓ * r)
  let W := A * f.q ^ 3 * g / p.K k
  let τ : α × ℝ → α × ℝ := fun ω => (ω.1, f.t₀ + f.q * ω.2)
  let point : α × ℝ → Fin 3 → ℝ := p.normalizedPoint k f.t₀ f.q
  let signal : α × ℝ → ℝ := fun ω => p.signal k ω.1 (f.t₀ + f.q * ω.2)
  let background : (Fin 3 → ℝ) → ℝ := fun x => MvPolynomial.eval x f.background
  let target : Set (α × ℝ) := {ω | scalarCell (f.coeff ω.1) ω.2 ξ = β ∧
      ⌊scalarX (f.coeff ω.1) ω.2 / Δ⌋ = j ∧ condition (τ ω)}
  let support : Set (α × ℝ) := {ω | ω.1 ∈ f.good ∧ ω.2 ∈ Icc (0 : ℝ) 1 ∧
      ∀ e : Fin 3, |point ω e| ≤ 2 * p.K k}
  let E := target ∩ support
  have hN : 0 < p.N k := by linarith [h.scale k]
  have hK : 0 < p.K k := by linarith [h.subpower.1 k]
  have hq := f.q_pos
  have hA : 0 < A := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hN _) _
  have hg : 0 < g := Real.rpow_pos_of_pos hN _
  have hW : 0 < W := by dsimp [W]; positivity
  have hτ : Measurable τ := by dsimp [τ]; fun_prop
  have hb := (h.basic k).1
  have hpoint : Measurable (fun ω : α × ℝ =>
      (![ω.2, p.x k ω.1 ω.2 1, p.x k ω.1 ω.2 2] : Fin 3 → ℝ)) := by
    apply Measurable.of_eval
    intro i
    fin_cases i
    · change Measurable (fun ω : α × ℝ => ω.2)
      fun_prop
    · change Measurable (fun ω : α × ℝ => p.b k ω.1 0 + ω.2 * p.b k ω.1 3)
      fun_prop
    · change Measurable (fun ω : α × ℝ => p.b k ω.1 1 + ω.2 * p.b k ω.1 4)
      fun_prop
  have hsignal : Measurable (fun ω : α × ℝ => p.signal k ω.1 ω.2) :=
    measurable_signal h k
  have hC : 0 ≤ p.K k * Δ ^ p.d := by positivity
  have hfine := fine_cell_cap_of_scaled_map_domination f.law (p.μ k) τ hτ
    _ hpoint _ hsignal condition hcond hW hC hδ
    (f.explicit_original_domination h a) weight
    (by intro q j; simpa only [mul_assoc, mul_left_comm, mul_comm] using hcap q j)
  have ht : ∀ᵐ ω ∂f.law, ω.2 ∈ Icc (0 : ℝ) 1 := by
    have hh : ∀ᵐ ω ∂f.law, ω ∈ (univ : Set α) ×ˢ Icc (0 : ℝ) 1 :=
      ae_iff.mpr f.time_support
    exact hh.mono (fun ω hω => hω.2)
  have hsupp : ∀ᵐ ω ∂f.law, ω ∈ support := by
    filter_upwards [f.good_ae, ht, f.normalized_base_bound_ae h a] with ω hω ht hb
    exact ⟨hω, ht, hb⟩
  have heq : f.law target = f.law E :=
    (measure_inter_conull (ae_iff.mp hsupp)).symm
  change f.law target ≤ _
  rw [heq]
  have hbound := normalized_residual_cell_cap (C := p.K k * Δ ^ p.d / W)
    f.law point signal f.coeff background
    (fun ω => condition (τ ω)) E hq hg hξ hδ hΔ hK.le hL (by positivity) hξg
    (p.c k r f.parent) (a.coefficient_bound f.parent 4)
    hδcell hδtrans hmcell hmtrans hv₁ hv₂ β j
    (by intro ω hω; rfl)
    (by intro ω hω; exact f.scalarY_eq ω.1 hω.2.1 ω.2)
    (by intro ω hω; simpa only [point, background, signal, normalizedPoint_eq] using
      f.scalarX_eq ω.1 hω.2.1 ω.2)
    (by
      intro ω hω
      simpa only [point, normalizedPoint, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, g, f.q_eq] using
        a.transverse f.parent ω.1 (a.fitted_subset f.parent (f.good_subset hω.2.1))
          _ (f.unit_time_mem ω.2 hω.2.2.1))
    (by intro ω hω; exact hω.1.1)
    (by intro ω hω; exact hω.1.2.1)
    (by intro ω hω; exact hω.1.2.2)
    (by
      intro ω hω y hy
      have hbvar := quadratic_background_variation f.background f.background_degree
        f.background_coeff_bound (by linarith [h.subpower.1 k]) hδ.le hδ1 (point ω) y
        hω.2.2.2 (fun i => by simpa only [abs_sub_comm] using hy i)
      have hvar : |background (point ω) - background y| ≤
          216 * p.N k ^ (m / 10) * (2 * p.K k) ^ 2 * δ := by
        simpa only [background, abs_sub_comm] using hbvar
      exact hvar.trans hbg)
    weight (by intro q j; exact hfine q j)
  apply hbound.trans
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  apply le_of_eq
  dsimp [W]
  field_simp [hA.ne', hq.ne', hg.ne', hK.ne']
  ring

end ListFrame

end Parent

end

end Submission.Obl.k4_general_parent_wide_layer_candidates
