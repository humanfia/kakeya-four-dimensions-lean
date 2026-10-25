-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Common.Apply; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254 (k4_general_parent_wide_layer_candidates), session x0900.
   The eventual numerics use `eventually_subpower_mul_rpow_lt` and
   `eventually_const_mul_rpow_lt` of accepted o213 (`k4_profile_density_bounds`), and the
   group mesh follows `Parent.Valid.nativeStatePruning` (`Field/NativePool/Pruning.lean`). -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Common.Ready
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Common.Numerics
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/-!
# The common affine field on consensus laws

`Parent.Valid.fieldReady_of_consensus`: under the frozen statement of o273
(`CommonFieldPrinciple`, an explicit hypothesis), every consensus law of a compared sample
(native base and velocity meshes `N^(-C₀ (Λ m + θ))` with `θ = r + (1 - d) u / 2`, signal mesh
`N^(-(r + u))`, agreement precision `N^(-θ)`, domination constant `N^η`) yields a field-ready
law with the same precision, for every loss `ε₁`, eventually in `k` and uniformly in the
subpower loss `H ≤ N^δ` of the sample.

The constants: `C₀ > 100` is the constant of o273 for the palette dimension `S = p.S`, and
`Λ = supportC + 3` depends only on the fixed Lipschitz exponent `supportC` of the accepted
native-signal partition (the native base mesh must be fine enough for the two native-signal
groups of a block to confine the signal on one normalized base cell).
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_general_parent_projected_layers (parentFilling)
open Submission.Obl.k4_profile_density_bounds (eventually_subpower_mul_rpow_lt
  eventually_const_mul_rpow_lt)

noncomputable section

set_option maxHeartbeats 4000000 in
/-- **The common affine field on consensus laws.** -/
theorem Parent.Valid.fieldReady_of_consensus {α : Type} [MeasurableSpace α] {p : Parent α}
    (hfield : CommonFieldPrinciple) (h : p.Valid) :
    ∃ C₀ Λ : ℝ, 100 < C₀ ∧ 1 ≤ Λ ∧ ∀ {r u v m : ℝ}, p.ComparedExponents r u v m →
    ∀ ε₁ : ℝ, 0 < ε₁ → ∃ δ η : ℝ, 0 < δ ∧ 0 < η ∧ ∀ᶠ k in Filter.atTop,
      ∀ H : ℝ, 2 ≤ H → p.K k ≤ H → H ≤ p.N k ^ δ →
      ∀ (s : p.ComparedSample k r u v m H),
      ∀ c : p.ConsensusLaw k s (C₀ * (Λ * m + (r + (1 - p.d) * u / 2))) (r + u)
          (C₀ * (Λ * m + (r + (1 - p.d) * u / 2))) (p.N k ^ (-(r + (1 - p.d) * u / 2)))
          (p.N k ^ η),
        Nonempty (p.FieldReady k s (p.N k ^ (-(r + (1 - p.d) * u / 2))) ε₁) := by
  obtain ⟨C₀, hC₀, hpr⟩ := hfield.at h.palette_pos
  have hJ0 : (0 : ℝ) ≤ (supportJ : ℝ) := Nat.cast_nonneg _
  have hCs0 : (0 : ℝ) ≤ (supportC : ℝ) := Nat.cast_nonneg _
  refine ⟨C₀, (supportC : ℝ) + 3, hC₀, by linarith, ?_⟩
  intro r u v m hexp ε₁ hε₁
  obtain ⟨⟨hr, hv, hvr, hrvm, hℓm, hrU⟩, hu, hur, hvu, hmr, hκu⟩ := hexp
  have hκ := h.rate_pos
  have hℓ := h.transverse_pos
  have hd0 := h.dimension_nonneg
  have hd1 := h.dimension_lt_one
  have hm : 0 < m := by linarith
  have hθ : 0 < r + (1 - p.d) * u / 2 := by
    have : 0 < (1 - p.d) * u := mul_pos (by linarith) hu
    linarith
  have hθ2 : r + (1 - p.d) * u / 2 < 2 * r := by
    have : (1 - p.d) * u ≤ u := by nlinarith
    linarith
  have hΛ1 : (1 : ℝ) ≤ (supportC : ℝ) + 3 := by linarith
  have hA : 0 < ((supportC : ℝ) + 3) * m := by positivity
  obtain ⟨η', hη', -, N₀, -, happ⟩ :=
    hpr (((supportC : ℝ) + 3) * m) (r + (1 - p.d) * u / 2) hA hθ (ε₁ / 2) (by positivity)
  -- the exponents
  set θ : ℝ := r + (1 - p.d) * u / 2 with hθdef
  set βb : ℝ := C₀ * (((supportC : ℝ) + 3) * m + θ) with hβb
  set μr : ℝ := min η' r with hμr
  have hμr0 : 0 < μr := lt_min hη' hr
  have hμrη : μr ≤ η' := min_le_left _ _
  have hμrr : μr ≤ r := min_le_right _ _
  set δH : ℝ := μr / 100 with hδH
  set s' : ℝ := r - μr / 2 with hs'
  set ρU : ℝ := ((supportC : ℝ) + 2) * r with hρU
  set ρG : ℝ := ((supportJ : ℝ) + p.κ + p.ℓ) * r + 1 with hρG
  set Mf : ℝ := p.κ * r + p.ℓ * r + βb + ρU + 1 with hMf
  set vMin : ℝ := min η' βb with hvMin
  set R : ℝ := 2 + r⁻¹ + ρG with hR
  have hβbΛ : ((supportC : ℝ) + p.ℓ + 2) * r < βb := by
    have h1 : ((supportC : ℝ) + 3) * (10000 * (1 + p.ℓ) * r) < ((supportC : ℝ) + 3) * m :=
      mul_lt_mul_of_pos_left hmr (by linarith)
    have h2 : ((supportC : ℝ) + p.ℓ + 2) * r ≤ ((supportC : ℝ) + 3) * (10000 * (1 + p.ℓ) * r) := by
      have : 0 ≤ (supportC : ℝ) * p.ℓ * r := by positivity
      nlinarith
    have h3 : ((supportC : ℝ) + 3) * m < βb := by
      rw [hβb]
      have : ((supportC : ℝ) + 3) * m < C₀ * (((supportC : ℝ) + 3) * m) := by nlinarith
      nlinarith
    linarith
  have hβb0 : 0 < βb := by
    have : 0 ≤ ((supportC : ℝ) + p.ℓ + 2) * r := by positivity
    linarith
  have hρG1 : 1 ≤ ρG := by
    have : 0 ≤ ((supportJ : ℝ) + p.κ + p.ℓ) * r := by positivity
    linarith
  have hR1 : 1 < R := by
    have : 0 < r⁻¹ := inv_pos.mpr hr
    linarith
  have hR0 : 0 < R := by linarith
  have hRr : R⁻¹ ≤ r := by
    rw [inv_le_comm₀ hR0 hr]
    linarith
  have hRρG : R⁻¹ ≤ ρG := (inv_le_one_of_one_le₀ hR1.le).trans hρG1
  have hρGR : ρG ≤ R := by
    have : 0 < r⁻¹ := inv_pos.mpr hr
    linarith
  have hrU' : r ≤ p.U := by
    have : 0 < 3 * m / p.κ := by positivity
    linarith
  have hvMin0 : 0 < vMin := lt_min hη' hβb0
  have hvMinMax : vMin ≤ βb := min_le_right _ _
  have hMf0 : 0 < Mf := by
    have : 0 ≤ ρU := by positivity
    have : 0 < p.κ * r := by positivity
    have : 0 < p.ℓ * r := by positivity
    linarith
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [h.scale k]
  -- the eventual facts
  have E1 := h.prepared R hR1
  have E2 := Submission.Obl.k4_general_parent_projected_layers.PreparedModel.eventually_pure_base_caps p.toParams h.toParams_valid p.toModel
    h.toModel_common h.toModel_caps hR1
  have E3 := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    (20 * supportJ + 1) (show (-1 : ℝ) < 0 by norm_num)
    (show (0 : ℝ) ≤ 3000000 ^ supportJ by positivity)
  have E4 := h.eventually_fine_caps hMf0 hr.le hvMin0 hvMinMax
  have E5 := h.scale_limit.eventually (eventually_ge_atTop N₀)
  have E6a := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2 14
    (show -r < -s' by linarith) (show (0 : ℝ) ≤ 3 * 2 ^ 15 by positivity)
  have E6b := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    (20 * supportC + 4) (show ((supportC : ℝ) + p.ℓ) * r - βb < -s' by linarith)
    (show (0 : ℝ) ≤ 144 * 3000000 ^ supportC by positivity)
  have E6c := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    (20 * supportC + 2) (show (supportC : ℝ) * r - ρU < -s' by rw [hρU]; linarith)
    (show (0 : ℝ) ≤ 36 * 3000000 ^ supportC by positivity)
  have E7 := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2 1
    (show -βb < -(p.ℓ * r) - ρU by rw [hρU]; linarith) (show (0 : ℝ) ≤ 1 by norm_num)
  have E8a := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2 3
    (show -Mf < -(p.κ * r) - βb by
      rw [hMf]
      have : 0 ≤ ρU := by positivity
      have : 0 < p.ℓ * r := by positivity
      linarith) (show (0 : ℝ) ≤ 2 by norm_num)
  have E8b := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2 3
    (show -Mf < -(p.κ * r) - p.ℓ * r - ρU by rw [hMf]; linarith) (show (0 : ℝ) ≤ 2 by norm_num)
  have E9 := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2 3
    (show r - s' < η' by rw [hs']; linarith) (show (0 : ℝ) ≤ 67200 by norm_num)
  have E10 := eventually_const_mul_rpow_lt h.scale_limit
    (show 4 * δH < η' by rw [hδH]; linarith) 99
  have E11 := eventually_const_mul_rpow_lt h.scale_limit (show η' / 2 < η' by linarith) 2
  have E12 := eventually_const_mul_rpow_lt h.scale_limit (show 2 * δH < r by rw [hδH]; linarith) 24
  have E13 := eventually_const_mul_rpow_lt h.scale_limit
    (show 4 * δH - m + p.ℓ * r < -θ by
      rw [hδH]
      have : 0 ≤ p.ℓ * r := by positivity
      nlinarith) 32
  have E14 := eventually_const_mul_rpow_lt h.scale_limit (show ε₁ / 2 < ε₁ by linarith) 2
  refine ⟨δH, η' / 2, by positivity, by positivity, ?_⟩
  filter_upwards [E1, E2, E3, E4, E5, E6a, E6b, E6c, E7, E8a, E8b, E9, E10, E11, E12, E13, E14]
    with k hprep hpure e3 hfc e5 e6a e6b e6c e7 e8a e8b e9 e10 e11 e12 e13 e14
  intro H hH2 hKH hHN s c
  have hN : 0 < p.N k := by linarith [h.scale k]
  have hK : 1 ≤ p.K k := h.subpower.1 k
  have hat := hprep r hRr hrU'
  have hq := p.common_blockLen_pos k r
  -- the two native-signal groups of the block
  have hpf0 : 0 < parentFilling (p.K k) (p.N k ^ (-r)) := parentFilling_pos hN hK
  have hres : p.N k ^ (-ρG) / (((2 : ℝ) ^ p.T k r)⁻¹ * p.N k ^ (-p.ℓ * r)) ≤
      (parentFilling (p.K k) (p.N k ^ (-r)) ^ supportJ)⁻¹ :=
    resolution_numeric hN hK (by positivity) hat.2.1 e3
  obtain ⟨E, hEm, hEsub, hEloss, hEosc⟩ := h.parent_groups hr.le hat c.block
    (Real.rpow_pos_of_pos hN (-ρG)) hres (hpure ρG hRρG hρGR)
  have hnum : 2 * (2 * p.K k) ^ 14 * p.N k ^ (-r) +
      parentFilling (p.K k) (p.N k ^ (-r)) ^ supportC *
        (12 * p.K k ^ 2 * ((p.K k + 1) ^ 2 * p.blockLen k r * p.N k ^ (-βb) +
          p.blockLen k r * p.N k ^ (-p.ℓ * r) * p.N k ^ (-ρU)) /
          (p.blockLen k r * p.N k ^ (-p.ℓ * r))) ≤ p.N k ^ (-s') :=
    FieldCommon.osc_bound_numeric hN hK hq rfl rfl rfl e6a e6b e6c
  have hosc : ∀ e, ∀ z ∈ E e, ∀ z' ∈ E e,
      (∀ c' : Fin 3, |p.base k z.1 z.2 c' - p.base k z'.1 z'.2 c'| ≤
        (p.K k + 1) ^ 2 * p.blockLen k r * p.N k ^ (-βb) +
          p.blockWidth k r * p.N k ^ (-ρU)) →
      |p.signal k z.1 z.2 - p.signal k z'.1 z'.2| ≤ p.N k ^ (-s') := by
    intro e z hz z' hz' hbase
    have hD : 0 ≤ (p.K k + 1) ^ 2 * p.blockLen k r * p.N k ^ (-βb) +
        p.blockWidth k r * p.N k ^ (-ρU) := by
      unfold blockWidth
      positivity
    exact (hEosc e z hz z' hz' _ hD hbase).trans hnum
  -- the fine mesh, the shear and the slabs
  have hqlow : (p.K k * p.N k ^ (p.κ * r))⁻¹ ≤ p.blockLen k r := by
    unfold blockLen
    exact inv_anti₀ (by positivity) hat.2.1
  have hw : p.blockWidth k r = p.blockLen k r * p.N k ^ (-(p.ℓ * r)) := by
    unfold blockWidth
    rw [neg_mul]
  have hfine1 := FieldCommon.fine_cell_numeric hN hK hqlow e8a
  have hfine2 : (p.K k + p.K k ^ 2) * p.N k ^ (-Mf) ≤ p.blockWidth k r * p.N k ^ (-ρU) := by
    rw [hw]
    exact FieldCommon.fine_slab_numeric hN hK hqlow e8b
  have hshear : p.K k * p.blockLen k r * p.N k ^ (-βb) ≤ p.blockWidth k r * p.N k ^ (-ρU) := by
    rw [hw]
    exact FieldCommon.shear_numeric hN hq e7
  have hρU0 : 0 ≤ ρU := by positivity
  have hδUK : p.N k ^ (-ρU) ≤ p.K k :=
    (Real.rpow_le_one_of_one_le_of_nonpos (hN1 k) (by linarith)).trans hK
  -- the loss numerics
  obtain ⟨n1, n3, n4, n5⟩ := FieldCommon.loss_numerics (hN1 k) hK hKH hHN (by positivity)
    hε₁.le e10 e12 e13 e14 rfl
  have hmA : m ≤ ((supportC : ℝ) + 3) * m := by nlinarith
  exact Parent.fieldReady_at h hat hKH s hm.le hmA hθ hε₁ c (happ (p.N k) e5 α) hEm hEsub
    hEloss (Real.rpow_pos_of_pos hN _) (by rw [hs']; linarith)
    (by rw [hs']; linarith) hosc hfc hfine1 hfine2 hshear hδUK (min_le_left _ _) le_rfl
    n1 e11.le n3 n4 n5 e9.le

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
