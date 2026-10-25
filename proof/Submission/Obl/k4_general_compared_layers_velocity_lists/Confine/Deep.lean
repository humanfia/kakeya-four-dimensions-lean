-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Confine.Deep; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Submission.Obl.k4_general_compared_layers_velocity_lists.Confine.Loss
import Submission.Obl.k4_general_compared_layers_velocity_lists.Confine.Numerics
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/-!
# Deep native-signal confinement of a general parent

Given admissible list exponents `r v m`, set `w = r + v`. At the intermediate depth
`s' = 2 w` every true block is split into two native-signal groups by the accepted
two-group support of a full prepared parent (o253), at a fixed physical base mesh
`N ^ (-((J + κ + ℓ) s' + 1))`; the groups lose a `parentFilling⁻¹ ≤ N ^ (-s')` proportion
of the blocks' incidence mass. On a deep label at depth
`t = r + 3 m / κ + (2 C + 2 κ + 2 ℓ + 2) w / κ`, whose original base coordinates vary by at
most `6 K ^ 2` deep block lengths, the native signal of one group varies by at most
`2 (2K) ^ 14 N ^ (-s') + parentFilling ^ C * 72 K ^ 4 q_t / (q_s' g_s') ≤ N ^ (-w) / 2`.
The multiplier `deepMultiplier κ ℓ` leaves room for `t` below `U`.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_profile_density_bounds (eventually_subpower_mul_rpow_lt
  eventually_const_mul_rpow_lt)

noncomputable section

/-- The universal multiplier of deep confinement. It depends only on the rate `κ`, the
transverse exponent `ℓ` and the fixed Lipschitz exponent `supportC` of the accepted
native-signal partition. -/
def deepMultiplier (κ ℓ : ℝ) : ℝ := 1 + (2 * (supportC : ℝ) + 2 * κ + 2 * ℓ + 5) / κ

theorem deepMultiplier_pos {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ) : 0 < deepMultiplier κ ℓ := by
  unfold deepMultiplier
  have : 0 ≤ (2 * (supportC : ℝ) + 2 * κ + 2 * ℓ + 5) / κ := by positivity
  linarith

/-- **Deep native-signal confinement.** For every admissible triple of list exponents with
`deepMultiplier κ ℓ * m ≤ U`, the native signal is confined on deep original labels. -/
theorem Parent.Valid.deepConfinement {α : Type} [MeasurableSpace α] {p : Parent α}
    (h : p.Valid) :
    0 < deepMultiplier p.κ p.ℓ ∧
    ∀ r v m : ℝ, p.ListExponents r v m → deepMultiplier p.κ p.ℓ * m ≤ p.U →
      p.DeepConfinement r v m := by
  refine ⟨deepMultiplier_pos h.rate_pos h.transverse_pos, ?_⟩
  intro r v m hexp hΛ
  obtain ⟨hr, hv, _hvr, hm, _hℓm, hU⟩ := hexp
  have hκ := h.rate_pos
  have hκ1 := h.rate_le_one
  have hℓ := h.transverse_pos
  have hm0 : 0 < m := by linarith
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = r + v := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hw]; linarith
  have hwm : w ≤ m := by rw [hw]; linarith
  have hrm : r ≤ m := by linarith
  obtain ⟨s', hs'⟩ : ∃ s' : ℝ, s' = 2 * w := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ,
      M = 2 * (supportC : ℝ) + 2 * p.κ + 2 * p.ℓ + 2 := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = r + 3 * m / p.κ + M * w / p.κ := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = ((supportJ : ℝ) + p.κ + p.ℓ) * s' + 1 := ⟨_, rfl⟩
  have hs'0 : 0 < s' := by rw [hs']; linarith
  have hρ1 : 1 ≤ ρ := by
    rw [hρ]
    have : 0 ≤ ((supportJ : ℝ) + p.κ + p.ℓ) * s' := by positivity
    linarith
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 2 + ρ + r⁻¹ := ⟨_, rfl⟩
  have hrinv : 0 < r⁻¹ := inv_pos.mpr hr
  have hR : 1 < R := by rw [hRdef]; linarith
  have hR0 : 0 < R := by linarith
  have hRr : R⁻¹ ≤ r := by
    rw [inv_le_comm₀ hR0 hr, hRdef]
    linarith
  have hRinv1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR.le
  have hRρ : R⁻¹ ≤ ρ := by linarith
  have hρR : ρ ≤ R := by rw [hRdef]; linarith
  -- depths
  have h3m : 3 * m ≤ 3 * m / p.κ := by
    rw [le_div_iff₀ hκ]
    nlinarith
  have hmU : m < p.U := by
    have : 0 < 3 * m / p.κ := by positivity
    linarith
  have hrU : r ≤ p.U := by
    have : 0 < 3 * m / p.κ := by positivity
    linarith
  have hrt : r + 3 * m / p.κ ≤ t := by
    rw [ht]
    have : 0 ≤ M * w / p.κ := by positivity
    linarith
  have htU : t ≤ p.U := by
    have h1 : M * w / p.κ ≤ M * m / p.κ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwm hM0) hκ.le
    have h2 : deepMultiplier p.κ p.ℓ * m = m + 3 * m / p.κ + M * m / p.κ := by
      unfold deepMultiplier
      rw [hM]
      field_simp
      ring
    rw [ht]
    linarith
  have hs'U : s' ≤ p.U := by rw [hs']; linarith
  have hrs' : r < s' := by rw [hs', hw]; linarith
  have hs't : s' < t := by rw [hs']; linarith
  have hRs' : R⁻¹ ≤ s' := by linarith
  have hRt : R⁻¹ ≤ t := by linarith
  have hκt : p.κ * t = p.κ * r + 3 * m + M * w := by
    rw [ht]
    field_simp
  have hexp2 : ((supportC : ℝ) + p.κ + p.ℓ) * s' - p.κ * t < -w := by
    have he : ((supportC : ℝ) + p.κ + p.ℓ) * s' - p.κ * t = -(p.κ * r) - 3 * m - 2 * w := by
      rw [hκt, hs', hM]
      ring
    rw [he]
    have : 0 < p.κ * r := mul_pos hκ hr
    linarith
  refine ⟨t, w, hrt, htU, hw0, ?_⟩
  intro ε hε hεw
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [h.scale k]
  have hE1 := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2 14
    (show -s' < -w by linarith) (show (0 : ℝ) ≤ 2 ^ 17 by positivity)
  have hE2 := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    (20 * supportC + 6) hexp2 (show (0 : ℝ) ≤ 288 * 3000000 ^ supportC by positivity)
  have hE3 := eventually_const_mul_rpow_lt h.scale_limit (show -s' < -w by linarith) 4
  have hE4 := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    (20 * supportJ + 1) (show (-1 : ℝ) < 0 by norm_num)
    (show (0 : ℝ) ≤ 3000000 ^ supportJ by positivity)
  have hcaps := PreparedModel.eventually_pure_base_caps p.toParams h.toParams_valid p.toModel
    h.toModel_common h.toModel_caps hR
  filter_upwards [h.prepared R hR, h.nested R hR, hcaps, hE1, hE2, hE3, hE4]
    with k hprep hnest hcap e1 e2 e3 e4
  intro f
  have hN : 0 < p.N k := by linarith [hN1 k]
  have hK : 1 ≤ p.K k := h.subpower.1 k
  have hat_r := hprep r hRr hrU
  have hat_s := hprep s' hRs' hs'U
  have hat_t := hprep t hRt htU
  have hnest_rs := hnest r s' hRr hrs' hs'U
  have hnest_st := hnest s' t hRs' hs't htU
  -- the physical mesh
  have hδ : 0 < p.N k ^ (-ρ) := Real.rpow_pos_of_pos hN _
  have hcapδ := hcap ρ hRρ hρR
  have hres : p.N k ^ (-ρ) / (((2 : ℝ) ^ p.T k s')⁻¹ * p.N k ^ (-p.ℓ * s')) ≤
      (parentFilling (p.K k) (p.N k ^ (-s')) ^ supportJ)⁻¹ := by
    rw [hρ]
    exact resolution_numeric hN hK (by positivity) hat_s.2.1 e4
  -- the two groups on every block at the intermediate depth
  have hgroups := fun i => h.parent_groups hs'0.le hat_s i hδ hres hcapδ
  choose E hEm hEsub hEloss hEosc using hgroups
  have hBA_s : ∀ i, p.B k s' i ⊆ p.A k s' i := fun i => (hat_s.2.2.1 i).2.2
  have hBA_t : ∀ i, p.B k t i ⊆ p.A k t i := fun i => (hat_t.2.2.1 i).2.2
  refine ⟨fun ω => physGrp E (f.timeMap ω), f.timeMap ⁻¹' p.physBad k s' E,
    (measurable_physGrp hEm).comp f.measurable_timeMap,
    (measurableSet_physBad (fun i => (hat_s.2.2.1 i).2.1) hEm).preimage f.measurable_timeMap,
    ?_, ?_⟩
  · exact (f.law_physBad_le h hat_r hat_s hnest_rs hEm hEloss).trans
      (loss_numeric (hN1 k) hK hεw e3)
  · intro i ω ω' hω hω' hτ hτ' hωbad hω'bad hgrp
    obtain ⟨h', hA', hI'⟩ := hnest_st i
    have hz : f.timeMap ω ∈ E h' (physGrp E (f.timeMap ω)) :=
      mem_physGrp hBA_s hat_s.2.2.2.1 hEsub (hA' (hBA_t i hω)) (hI' hτ) hωbad
    have hz' : f.timeMap ω' ∈ E h' (physGrp E (f.timeMap ω')) :=
      mem_physGrp hBA_s hat_s.2.2.2.1 hEsub (hA' (hBA_t i hω')) (hI' hτ') hω'bad
    have hgrp' : physGrp E (f.timeMap ω') = physGrp E (f.timeMap ω) := hgrp.symm
    rw [hgrp'] at hz'
    have hdiam : ∀ c : Fin 3, |p.base k (f.timeMap ω).1 (f.timeMap ω).2 c -
        p.base k (f.timeMap ω').1 (f.timeMap ω').2 c| ≤
          6 * p.K k ^ 2 * ((2 : ℝ) ^ p.T k t)⁻¹ := fun c =>
      AtDepth.base_diameter hat_t (hN1 k) hK hℓ (by linarith) i (hBA_t i hω) (hBA_t i hω')
        hτ hτ' c
    have hosc := hEosc h' (physGrp E (f.timeMap ω)) (f.timeMap ω) hz (f.timeMap ω') hz'
      (6 * p.K k ^ 2 * ((2 : ℝ) ^ p.T k t)⁻¹) (by positivity) hdiam
    have hnum := osc_numeric (C := supportC) hN hK (by positivity) hat_s.2.1 hat_t.1 e1 e2
    rw [← hw]
    exact hosc.trans hnum

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
