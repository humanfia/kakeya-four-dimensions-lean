-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.NativePool.Pruning; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- The choice of depths, the native-signal groups at the intermediate depth and the eventual
   numerics follow `Parent.Valid.deepConfinement` of this checkout (`Confine/Deep.lean`), with
   target signal precision `N ^ (-w)` in place of `N ^ (-(r + v)) / 2`, and with a deep depth
   that also resolves the normalized base cells `N ^ (-βb)` of the original block. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.NativePool.Core

/-!
# Native fine-state palette domination inside one original block

For an original block `Q` at depth `r` and any submeasure `θ` of the original incidence measure
carried by `Q`, prune against deep end labels: at the intermediate depth `s' = r + w` every true
block splits into two native-signal groups (accepted o253), and at the deep depth
`t = nativeMultiplier κ ℓ * (r + βb + w)` every deep label inside one group meets at most `81`
native fine states (normalized base cells of side `N ^ (-βb)` and native-signal bins of width
`N ^ (-w)`). Pruning (accepted o236) against the deep original palette caps leaves a submeasure
`θ'`, losing at most `ϑ q_r ν(A_Q)`, on which every native state has conditional palette
domination with constant `324 K / ϑ`.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_profile_density_bounds (eventually_subpower_mul_rpow_lt
  eventually_const_mul_rpow_lt)

noncomputable section

/-- The multiplier of native fine-state pruning: the deep depth is
`nativeMultiplier κ ℓ * (r + βb + w)`. It depends only on `κ`, `ℓ` and the fixed Lipschitz
exponent `supportC` of the accepted native-signal partition. -/
def nativeMultiplier (κ ℓ : ℝ) : ℝ := ((supportC : ℝ) + κ + ℓ + 2) / κ

theorem nativeMultiplier_pos {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ) :
    0 < nativeMultiplier κ ℓ := by
  unfold nativeMultiplier
  positivity

/-- **Native fine-state palette domination inside one original block, after pruning against
deep end labels.** -/
theorem Parent.Valid.nativeStatePruning {α : Type} [MeasurableSpace α] {p : Parent α}
    (h : p.Valid) : ∃ Λ : ℝ, 0 < Λ ∧
    ∀ r βb w mv : ℝ, 0 < r → 0 < βb → 0 < w → 0 < mv → Λ * (r + βb + w) ≤ p.U →
    ∀ ϑ : ℝ, 0 < ϑ → ∀ᶠ k in Filter.atTop,
      ∀ (Q : Fin (p.n k r)) (θ : MeasureTheory.Measure (α × ℝ)), θ ≤ p.μ k →
        (∀ᵐ ω ∂θ, ω.1 ∈ p.B k r Q ∧ ω.2 ∈ block (p.T k r) (p.j k r Q)) →
        ∃ θ' : MeasureTheory.Measure (α × ℝ), θ' ≤ θ ∧
          θ Set.univ ≤ θ' Set.univ +
            ENNReal.ofReal ϑ * (ENNReal.ofReal (p.blockLen k r) * p.ν k (p.A k r Q)) ∧
          ∀ (σ : Fin 4 → ℤ) (j : ℤ),
            θ' {ω | p.nativeState k r Q (p.N k ^ (-βb)) (p.N k ^ (-w)) ω = σ ∧
                ⌊p.b k ω.1 3 / p.N k ^ (-mv)⌋ = j} ≤
              ENNReal.ofReal (324 * p.K k / ϑ) *
                θ' {ω | p.nativeState k r Q (p.N k ^ (-βb)) (p.N k ^ (-w)) ω = σ} *
                p.π k {x | ⌊x / p.N k ^ (-mv)⌋ = j} := by
  refine ⟨nativeMultiplier p.κ p.ℓ, nativeMultiplier_pos h.rate_pos h.transverse_pos, ?_⟩
  intro r βb w mv hr hβb hw hmv hΛ ϑ hϑ
  have hκ := h.rate_pos
  have hℓ := h.transverse_pos
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (supportC : ℝ) + p.κ + p.ℓ + 2 := ⟨_, rfl⟩
  have hC0 : (0 : ℝ) ≤ supportC := Nat.cast_nonneg _
  have hM0 : p.κ + 2 ≤ M := by rw [hM]; linarith
  obtain ⟨s', hs'⟩ : ∃ s' : ℝ, s' = r + w := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = nativeMultiplier p.κ p.ℓ * (r + βb + w) := ⟨_, rfl⟩
  have hκt : p.κ * t = M * (r + βb + w) := by
    rw [ht, hM]
    unfold nativeMultiplier
    field_simp
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = ((supportJ : ℝ) + p.κ + p.ℓ) * s' + 1 := ⟨_, rfl⟩
  have hs'0 : 0 < s' := by rw [hs']; linarith
  have hρ1 : 1 ≤ ρ := by
    rw [hρ]
    have : 0 ≤ ((supportJ : ℝ) + p.κ + p.ℓ) * s' := by positivity
    linarith
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 2 + ρ + r⁻¹ + mv + mv⁻¹ := ⟨_, rfl⟩
  have hrinv : 0 < r⁻¹ := inv_pos.mpr hr
  have hmvinv : 0 < mv⁻¹ := inv_pos.mpr hmv
  have hR : 1 < R := by rw [hRdef]; linarith
  have hR0 : 0 < R := by linarith
  have hRr : R⁻¹ ≤ r := by
    rw [inv_le_comm₀ hR0 hr, hRdef]
    linarith
  have hRmv : R⁻¹ ≤ mv := by
    rw [inv_le_comm₀ hR0 hmv, hRdef]
    linarith
  have hmvR : mv ≤ R := by rw [hRdef]; linarith
  have hRinv1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR.le
  have hRρ : R⁻¹ ≤ ρ := by linarith
  have hρR : ρ ≤ R := by rw [hRdef]; linarith
  -- depths
  have hrs' : r < s' := by rw [hs']; linarith
  have hs't : s' < t := by
    have h1 : (p.κ + 2) * (r + βb + w) ≤ M * (r + βb + w) :=
      mul_le_mul_of_nonneg_right hM0 (by linarith)
    have h2 : p.κ * (r + w) < (p.κ + 2) * (r + βb + w) := by
      nlinarith [mul_pos hκ hβb]
    have h3 : p.κ * s' < p.κ * t := by
      rw [hκt, hs']
      linarith
    exact lt_of_mul_lt_mul_left h3 hκ.le
  have htU : t ≤ p.U := by rw [ht]; exact hΛ
  have hs'U : s' ≤ p.U := by linarith
  have hrU : r ≤ p.U := by linarith
  have hRs' : R⁻¹ ≤ s' := by linarith
  have hRt : R⁻¹ ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  -- exponents
  have hexp2 : ((supportC : ℝ) + p.κ + p.ℓ) * s' - p.κ * t < -w := by
    rw [hκt, hs']
    have he : ((supportC : ℝ) + p.κ + p.ℓ) * (r + w) - M * (r + βb + w) =
        -(((supportC : ℝ) + p.κ + p.ℓ) * βb) - 2 * (r + βb + w) := by
      rw [hM]
      ring
    rw [he]
    have : 0 ≤ ((supportC : ℝ) + p.κ + p.ℓ) * βb := by positivity
    linarith
  have hexpb : p.κ * r + p.ℓ * r - p.κ * t < -βb := by
    rw [hκt]
    have he : p.κ * r + p.ℓ * r - M * (r + βb + w) =
        -(((supportC : ℝ) + 2) * r) - M * (βb + w) := by
      rw [hM]
      ring
    rw [he]
    have h1 : 0 ≤ ((supportC : ℝ) + 2) * r := by positivity
    have h2 : (p.κ + 2) * (βb + w) ≤ M * (βb + w) :=
      mul_le_mul_of_nonneg_right hM0 (by linarith)
    have h3 : βb < (p.κ + 2) * (βb + w) := by
      nlinarith [mul_pos hκ hβb, mul_pos hκ hw]
    linarith
  -- eventual numerics
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [h.scale k]
  have hE1 := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2 14
    (show -s' < -w by linarith) (show (0 : ℝ) ≤ 2 ^ 17 by positivity)
  have hE2 := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    (20 * supportC + 6) hexp2 (show (0 : ℝ) ≤ 288 * 3000000 ^ supportC by positivity)
  have hE4 := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    (20 * supportJ + 1) (show (-1 : ℝ) < 0 by norm_num)
    (show (0 : ℝ) ≤ 3000000 ^ supportJ by positivity)
  have hE5 := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2 5
    hexpb (show (0 : ℝ) ≤ 18 by norm_num)
  have hE6 := eventually_const_mul_rpow_lt h.scale_limit (show -s' < 0 by linarith) (2 / ϑ)
  have hcaps := PreparedModel.eventually_pure_base_caps p.toParams h.toParams_valid p.toModel
    h.toModel_common h.toModel_caps hR
  filter_upwards [h.prepared R hR, h.nested R hR, hcaps, hE1, hE2, hE4, hE5, hE6]
    with k hprep hnest hcap e1 e2 e4 e5 e6
  intro Q θ hθ hθsupp
  have hN : 0 < p.N k := by linarith [hN1 k]
  have hK : 1 ≤ p.K k := h.subpower.1 k
  have hat_r := hprep r hRr hrU
  have hat_s := hprep s' hRs' hs'U
  have hat_t := hprep t hRt htU
  have hnest_rs := hnest r s' hRr hrs' hs'U
  have hnest_rt := hnest r t hRr (hrs'.trans hs't) htU
  have hnest_st := hnest s' t hRs' hs't htU
  -- the physical mesh and the two native-signal groups at the intermediate depth
  have hδ : 0 < p.N k ^ (-ρ) := Real.rpow_pos_of_pos hN _
  have hcapδ := hcap ρ hRρ hρR
  have hres : p.N k ^ (-ρ) / (((2 : ℝ) ^ p.T k s')⁻¹ * p.N k ^ (-p.ℓ * s')) ≤
      (parentFilling (p.K k) (p.N k ^ (-s')) ^ supportJ)⁻¹ := by
    rw [hρ]
    exact resolution_numeric hN hK (by positivity) hat_s.2.1 e4
  have hgroups := fun i => h.parent_groups hs'0.le hat_s i hδ hres hcapδ
  choose E hEm hEsub hEloss hEosc using hgroups
  -- one group confines the native signal of a deep label to `N ^ (-w)`
  have hsig : ∀ (i : Fin (p.n k s')) (e : Fin 2), ∀ z ∈ E i e, ∀ z' ∈ E i e,
      (∀ c : Fin 3, |p.base k z.1 z.2 c - p.base k z'.1 z'.2 c| ≤
        6 * p.K k ^ 2 * ((2 : ℝ) ^ p.T k t)⁻¹) →
      |p.signal k z.1 z.2 - p.signal k z'.1 z'.2| ≤ p.N k ^ (-w) := by
    intro i e z hz z' hz' hdiam
    have hosc := hEosc i e z hz z' hz' (6 * p.K k ^ 2 * ((2 : ℝ) ^ p.T k t)⁻¹) (by positivity)
      hdiam
    have hnum := osc_numeric (C := supportC) hN hK (by positivity) hat_s.2.1 hat_t.1 e1 e2
    have hw2 : p.N k ^ (-w) / 2 ≤ p.N k ^ (-w) := by
      have : 0 < p.N k ^ (-w) := Real.rpow_pos_of_pos hN _
      linarith
    exact (hosc.trans hnum).trans hw2
  -- deep labels resolve the normalized base cells
  have hbase : 3 * p.K k * (6 * p.K k ^ 2 * ((2 : ℝ) ^ p.T k t)⁻¹) / p.blockWidth k r ≤
      p.N k ^ (-βb) := by
    have hwidth : p.blockWidth k r = ((2 : ℝ) ^ p.T k r)⁻¹ * p.N k ^ (-p.ℓ * r) := rfl
    rw [hwidth]
    exact base_numeric hN hK (by positivity) hat_r.2.1 hat_t.1 e5
  -- the deep original palette caps
  have hcapt : ∀ (i : Fin (p.n k t)) (a : ℤ), p.μ k {ω | ω.1 ∈ p.B k t i ∧
      ω.2 ∈ block (p.T k t) (p.j k t i) ∧ ⌊p.b k ω.1 3 / (p.N k ^ (-mv))⌋ = a} ≤
      ENNReal.ofReal (p.K k * ((2 : ℝ) ^ p.T k t)⁻¹) * p.ν k (p.A k t i) *
        p.π k {x : ℝ | ⌊x / (p.N k ^ (-mv))⌋ = a} := by
    intro i a
    have hh := hat_t.2.2.2.2.2.2 i mv a hRmv hmvR
    simpa only [zpow_neg, zpow_natCast] using hh
  -- the loss of the groups
  have hs'small : p.N k ^ (-s') ≤ ϑ / 2 := by
    rw [Real.rpow_zero] at e6
    have h2 : 2 / ϑ * p.N k ^ (-s') = 2 * p.N k ^ (-s') / ϑ := by ring
    rw [h2, div_lt_one hϑ] at e6
    linarith
  have hloss := loss_numeric_half hN hK hs'small
  exact h.nativePrune_core hr.le ht0.le hϑ (Real.rpow_pos_of_pos hN (-βb))
    (Real.rpow_pos_of_pos hN (-w)) hat_r hat_s hat_t hnest_rs hnest_rt hnest_st E hEm hEsub
    hEloss hloss hsig hbase hcapt Q θ hθ hθsupp

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
