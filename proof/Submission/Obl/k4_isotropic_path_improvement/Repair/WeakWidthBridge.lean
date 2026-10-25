-- Part of an offer for o106 assembled by x0678 (o064). Adapted from this LOT tree, o064's
-- repository, origin/x0447 at f61522e4 (x0447's file Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/WeakWidthBridge.lean);
-- only the namespace changed. See that file for the sources it in turn adapts.
import Submission.Obl.k4_quadratic_finite_greedy_cover.Interface
import Submission.Obl.k4_quadratic_atlas_normalization.ChartMonotonicity

/-!
Adapted from this LOT tree o204, session x0733, commitba2d6042,
Submission/Obl/k4_uniform_sampled_isotropic_branches/Interface.lean:
the flexible atlas definition from a rejected split, without assuming
any of that split's geometric assertions. The proofs below keep the original
chart events, so an arbitrary residual mask need not be encoded in them.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.Repair.WeakWidthBridge

open MeasureTheory Submission.Obl.k4_quadratic_finite_greedy_cover

abbrev Ln := ℕ × (Fin 6 → ℝ)
abbrev Ev := Ln × ℝ
abbrev P2 := EuclideanSpace ℝ (Fin 2)
abbrev Po := MvPolynomial (Fin 4) ℝ
abbrev Ob := EuclideanSpace ℝ (Fin 3) × ℤ

def originalMassAtlas (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure Ln) (E : Fin W → Set Ev) (B : Fin W → ℝ)
    (Mi Di : ℕ) (α r₂ : ℝ) (T₂ : ℕ)
    (extra : Matrix (Fin 2) (Fin 2) ℝ → Prop)
    (aux : Fin W → Fin (2 ^ T₂) → Set Ln → Set Ev → Prop → Prop)
    (massFloor : ENNReal) (mass : Fin W → Set Ev → ENNReal) : Prop :=
  ∃ (C₂ : ℕ) (γ₂ : Fin C₂ → Fin W) (j₂ : Fin C₂ → Fin (2 ^ T₂))
    (c₂ u₂ : Fin C₂ → P2) (Q₂ : Fin C₂ → Matrix (Fin 2) (Fin 2) ℝ)
    (R₂ : Fin C₂ → Po) (A₂ : Fin C₂ → Set Ln) (F₂ : Fin C₂ → Set Ev)
    (lst₂ : Fin W → Ob → Finset (Fin C₂)),
    (C₂ : ℝ) ≤ Nk ^ Mi ∧
    (∀ b b', b ≠ b' → γ₂ b = γ₂ b' → j₂ b = j₂ b' → Disjoint (A₂ b) (A₂ b')) ∧
    (∀ w o, ((lst₂ w o).card : ℝ) ≤ Nk ^ α) ∧
    (∀ b, chart Nk Mi Di (Nk ^ α) T₂ ((j₂ b : ℕ) : ℝ) r₂
      (B (γ₂ b)) (E (γ₂ b)) (c₂ b) (u₂ b) (Q₂ b) (R₂ b) (A₂ b) (F₂ b)
      (aux (γ₂ b) (j₂ b) (A₂ b) (F₂ b)
        (∀ p ∈ F₂ b, b ∈ lst₂ (γ₂ b) (obs (B (γ₂ b)) (δ Nk L) p))) ∧ extra (Q₂ b)) ∧
    massFloor ≤ ∑ b, ENNReal.ofReal (ω (γ₂ b)) * mass (γ₂ b) (F₂ b)

/-- A floor on selected subevents certifies the original native chart events,
after paying their mass loss and enlarging slack. -/
theorem system_of_original_mass_atlas
    {Nk L α τ r₂ : ℝ} {W Mi Di T₂ : ℕ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {extra extra' : Matrix (Fin 2) (Fin 2) ℝ → Prop}
    {aux : Fin W → Fin (2 ^ T₂) → Set Ln → Set Ev → Prop → Prop}
    {massFloor : ENNReal} {mass : Fin W → Set Ev → ENNReal}
    (hN : 1 ≤ Nk) (hατ : α ≤ τ) (hB : ∀ w, 0 ≤ B w)
    (haux : ∀ w jt A F known, aux w jt A F known → known)
    (hextra : ∀ Q, extra Q → extra' Q)
    (hmass : ∀ w F, mass w F ≤ ((ν w).prod volume) F)
    (hfloor : ENNReal.ofReal (Nk ^ (-τ)) ≤ massFloor)
    (ha : originalMassAtlas Nk L W ω ν E B Mi Di α r₂ T₂ extra aux massFloor mass) :
    system Nk L W ω ν E B Mi Di τ r₂ T₂ extra' := by
  rcases ha with ⟨C₂, γ₂, j₂, c₂, u₂, Q₂, R₂, A₂, F₂, lst₂,
    hcount, hdisj, hlist, hchart, htotal⟩
  have hslack := Real.rpow_le_rpow_of_exponent_le hN hατ
  refine ⟨C₂, γ₂, j₂, c₂, u₂, Q₂, R₂, A₂, F₂, lst₂,
    hcount, hdisj, fun w o => (hlist w o).trans hslack, ?_, ?_⟩
  · intro b
    refine ⟨?_, hextra _ (hchart b).2⟩
    exact Submission.Obl.k4_quadratic_atlas_normalization.chart_mono hN le_rfl le_rfl
      (Real.rpow_pos_of_pos (zero_lt_one.trans_le hN) _) hslack (hB _)
      (hchart b).1 (haux _ _ _ _ _)
  · exact hfloor.trans (htotal.trans (Finset.sum_le_sum fun b _ =>
      mul_le_mul' le_rfl (hmass _ _)))

/-- A power-small input slack pays the constant-eight substantial-mass loss. -/
theorem eight_kappa_mass_floor {Nk κ σ τ : ℝ}
    (hN : 1 ≤ Nk) (hκ : 0 < κ) (hκN : κ ≤ Nk ^ σ)
    (hστ : σ ≤ τ / 2) (hlarge : 8 ≤ Nk ^ (τ / 2)) :
    Nk ^ (-τ) ≤ κ⁻¹ / 8 := by
  have hNpos : 0 < Nk := zero_lt_one.trans_le hN
  have hκhalf : κ ≤ Nk ^ (τ / 2) :=
    hκN.trans (Real.rpow_le_rpow_of_exponent_le hN hστ)
  have hbig : 8 * κ ≤ Nk ^ τ := by
    calc
      _ ≤ Nk ^ (τ / 2) * Nk ^ (τ / 2) :=
        mul_le_mul hlarge hκhalf hκ.le (by positivity)
      _ = _ := by rw [← Real.rpow_add hNpos]; congr 1; ring
  have hi := inv_anti₀ (by positivity : 0 < 8 * κ) hbig
  rw [Real.rpow_neg hNpos.le]
  simpa only [mul_inv_rev, div_eq_mul_inv] using hi

/-- A middle node leaves a terminal margin for a small width gain. -/
theorem middle_node_width_margin {L r si δ₀ Δ : ℝ}
    (hL : 0 ≤ L) (hsi : si ≤ 1 / 2) (hr : |r - si * L| ≤ δ₀ * L)
    (hδ : δ₀ ≤ 1 / 8) (hΔ : Δ ≤ 1 / 8) :
    r + 2 * Δ * L ≤ L := by
  have h1 := (abs_le.mp hr).2
  have h2 := mul_le_mul_of_nonneg_right hsi hL
  have h3 := mul_le_mul_of_nonneg_right hδ hL
  have h4 := mul_le_mul_of_nonneg_right hΔ hL
  nlinarith

/-- A substantial original-mass narrow atlas gives a width exit at any fixed
smaller gain, keeping its chart events and original observation lists. -/
theorem width_of_original_mass_atlas
    {Nk L α τ κ Δ β : ℝ} {W Mi Di m i : ℕ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {r nw : ℕ → ℝ} {T : ℕ → ℕ} {H : Fin W → Set Ev}
    {aux : Fin W → Fin (2 ^ T i) → Set Ln → Set Ev → Prop → Prop}
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hατ : α ≤ τ) (hB : ∀ w, 0 ≤ B w)
    (hi : i < m) (hroom : r i + 2 * Δ * L ≤ L) (hΔβ : Δ ≤ β)
    (haux : ∀ w jt A F known, aux w jt A F known → known)
    (hfloor : Nk ^ (-τ) ≤ κ⁻¹ / 8)
    (ha : originalMassAtlas Nk L W ω ν E B Mi Di α (r i) (T i)
      (fun Q => |Q.det| * (4 : ℝ) ^ T i ≤ Nk ^ (-(nw i + β * L)))
      aux (ENNReal.ofReal (κ⁻¹ / 8))
      (fun w F => ((ν w).prod volume) (F ∩ H w))) :
    width Nk L W ω ν E B m r T nw Δ Mi Di τ := by
  refine ⟨i, hi, hroom, ?_⟩
  apply system_of_original_mass_atlas hN hατ hB haux
    (fun Q hQ => hQ.trans (Real.rpow_le_rpow_of_exponent_le hN ?_))
    (fun _ _ => measure_mono Set.inter_subset_left) (ENNReal.ofReal_le_ofReal hfloor) ha
  nlinarith [mul_le_mul_of_nonneg_right hΔβ hL]

/-- A middle-level narrow-atlas alternative gives the weaker fixed width exit.
The requested output slack pays the original constant-eight mass loss. -/
theorem width_of_middle_narrow_atlas
    {Nk L α τ κ σ δ₀ Δ u₀ : ℝ} {W Mi Di m : ℕ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {s r nw : ℕ → ℝ} {T : ℕ → ℕ} {H : Fin W → Set Ev}
    {aux : ∀ i, Fin W → Fin (2 ^ T i) → Set Ln → Set Ev → Prop → Prop}
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hατ : α ≤ τ) (hB : ∀ w, 0 ≤ B w)
    (hlevels : ∀ i, i < m → |r i - s i * L| ≤ δ₀ * L)
    (hδ : δ₀ ≤ 1 / 8) (hΔsmall : Δ ≤ 1 / 8) (hΔu : Δ ≤ u₀)
    (hκ : 0 < κ) (hκN : κ ≤ Nk ^ σ) (hστ : σ ≤ τ / 2)
    (hlarge : 8 ≤ Nk ^ (τ / 2))
    (haux : ∀ i w jt A F known, aux i w jt A F known → known)
    (hnarrow : ∃ (i : ℕ) (β : ℝ), i < m ∧ s i ≤ 1 / 2 ∧ u₀ ≤ β ∧
      originalMassAtlas Nk L W ω ν E B Mi Di α (r i) (T i)
        (fun Q => |Q.det| * (4 : ℝ) ^ T i ≤ Nk ^ (-(nw i + β * L)))
        (aux i) (ENNReal.ofReal (κ⁻¹ / 8))
        (fun w F => ((ν w).prod volume) (F ∩ H w))) :
    width Nk L W ω ν E B m r T nw Δ Mi Di τ := by
  obtain ⟨i, β, hi, hsi, hβ, ha⟩ := hnarrow
  exact width_of_original_mass_atlas hN hL hατ hB hi
    (middle_node_width_margin hL hsi (hlevels i hi) hδ hΔsmall)
    (hΔu.trans hβ) (haux i)
    (eight_kappa_mass_floor hN hκ hκN hστ hlarge) ha

end Submission.Obl.k4_isotropic_path_improvement.Repair.WeakWidthBridge
