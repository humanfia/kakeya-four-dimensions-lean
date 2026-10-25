-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FJ.V2ResidualCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FJ/V2ResidualCaps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FJ/V2ResidualCaps.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FJ/V2ResidualCaps.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2Residual
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarBoxCaps
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGroupNormalization
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCovers

set_option autoImplicit false

/-!
# Starting groups and residual caps, version 2

The `j = 2` counterparts of x0662's `ScalarStartingGroup.lean` / `ScalarBlockGroup.lean`
(starting-bin palette), `ScalarMovingGroupCaps.lean` / `ScalarResidualCurrentCaps.lean` (the cap
of the residual kernel) and of `original_residual_spatial_palette` (o078, branch `x0260` at
`206ab988`).  The tangential position lies in `ℝ²`, so spatial cells are cubes in
`(y₀, y₁, S)` and the cap exponent is `2 + d`:

* `v2_starting_group_palette`: the scalar `H`-bins at one time number at most `C / H^d`, and each
  carries prior mass at most `C H^d`;
* `UpperHyp.v2_starting_group_palette`: the same for labelled trajectories, `C = 200000 K⁶`;
* `v2_left_residual_group_cap`: inside one normalized starting group, the labels whose tangential
  position at the anchor lies in a fixed `p`-cube and whose current normalized scalar lies in a
  fixed `p`-bin carry normalized mass at most `125 (1 + 2K)² C p^(2+d)`;
* `v2_residual_spatial_palette`: the `p`-cube codes of positions in `[-2K, 2K]²` number at most
  `49 K² p⁻²`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2

open MeasureTheory Set
open scoped BigOperators
open WangZahlLot.Obl.wz_slab_local_linearity
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

noncomputable section

/-- **Starting-bin palette** in version 2. -/
theorem v2_starting_group_palette_of_caps {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν] (A : Set Λ) (hA : MeasurableSet A)
    (Y : Λ → Fin 2 → ℝ) (Z : Λ → ℝ) (hZ : Measurable Z) (S : Set ℝ)
    {H d B BZ Cs Cj K : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) (hB : 1 ≤ B)
    (hBZ : 0 < BZ) (hHBZ : H ≤ 2 * BZ) (hCs : 0 ≤ Cs) (hCj : 0 ≤ Cj)
    (hK : 0 < K) (hS : IntervalAD H d Cs S) (hY : ∀ l ∈ A, ∀ i, |Y l i| ≤ B)
    (hsupport : ∀ l ∈ A, Z l ∈ S ∩ Icc (-BZ) BZ)
    (hjoint : ∀ a b₀ b₁ : ℝ,
      ν.real {l | l ∈ A ∧ Y l 0 ∈ Icc b₀ (b₀ + H) ∧ Y l 1 ∈ Icc b₁ (b₁ + H) ∧
        Z l ∈ Icc a (a + H)} ≤ Cj * H ^ (2 + d))
    (hKcount : 3 * Cs * (2 * BZ) ^ d ≤ K) (hKprior : 245 * B ^ 2 * Cj ≤ K) :
    ∃ J : Finset ℤ, (J.card : ℝ) ≤ K / H ^ d ∧
      (∀ l ∈ A, (⌊Z l / H⌋ : ℤ) ∈ J) ∧
      (∀ b ∈ J, (ν.restrict A).real {l | (⌊Z l / H⌋ : ℤ) = b} ≤ K * H ^ d) ∧
      ∀ b ∈ J, (scalarGroupPrior (ν.restrict A) (fun l => ⌊Z l / H⌋) b (H ^ d)).real univ ≤ K := by
  have hc : 0 < H ^ d := Real.rpow_pos_of_pos hH _
  have hcode : Measurable (fun l => (⌊Z l / H⌋ : ℤ)) := (hZ.div_const H).floor
  obtain ⟨J, hcard, hcover⟩ := intervalAD_grid_list hH hHBZ hS (a := -BZ)
  have hcard' : (J.card : ℝ) ≤ K / H ^ d := by
    apply hcard.trans
    rw [Real.div_rpow (by positivity : 0 ≤ 2 * BZ) hH.le]
    calc
      _ = (3 * Cs * (2 * BZ) ^ d) / H ^ d := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hKcount hc.le
  have hcover' : ∀ l ∈ A, (⌊Z l / H⌋ : ℤ) ∈ J := by
    intro l hl
    obtain ⟨hs, hlo, hhi⟩ := hsupport l hl
    exact hcover _ ⟨hs, hlo, by linarith⟩
  have hcap : ∀ b ∈ J, (ν.restrict A).real {l | (⌊Z l / H⌋ : ℤ) = b} ≤ K * H ^ d := by
    intro b _
    let C := A ∩ {l | (⌊Z l / H⌋ : ℤ) = b}
    let X : Λ → Fin 3 → ℝ := fun l => ![Y l 0, Y l 1, Z l]
    let a : Fin 3 → ℝ := ![-B, -B, H * b]
    let W : Fin 3 → ℝ := ![2 * B, 2 * B, H]
    have hW : ∀ i, 0 ≤ W i := by
      intro i; fin_cases i <;> simp [W] <;> positivity
    have hbox : ∀ l ∈ C, ∀ i, X l i ∈ Icc (a i) (a i + W i) := by
      intro l hl i
      have hy0 := abs_le.mp (hY l hl.1 0)
      have hy1 := abs_le.mp (hY l hl.1 1)
      have hz := (mesh_lower_endpoint hH hl.2).1
      fin_cases i
      · show Y l 0 ∈ Icc (-B) (-B + 2 * B)
        exact ⟨hy0.1, by linarith [hy0.2]⟩
      · show Y l 1 ∈ Icc (-B) (-B + 2 * B)
        exact ⟨hy1.1, by linarith [hy1.2]⟩
      · show Z l ∈ Icc (H * b) (H * b + H)
        exact ⟨hz.1, by linarith [hz.2]⟩
    have hcube : ∀ e : Fin 3 → ℝ,
        ν.real {l | l ∈ A ∧ ∀ i, X l i ∈ Icc (e i) (e i + H)} ≤ Cj * H ^ (2 + d) := by
      intro e
      refine le_trans (measureReal_mono ?_ (measure_ne_top ν _)) (hjoint (e 2) (e 0) (e 1))
      intro l hl
      have h0 : Y l 0 ∈ Icc (e 0) (e 0 + H) := hl.2 0
      have h1 : Y l 1 ∈ Icc (e 1) (e 1 + H) := hl.2 1
      have h2 : Z l ∈ Icc (e 2) (e 2 + H) := hl.2 2
      exact ⟨hl.1, h0, h1, h2⟩
    have hrect := original_rectangular_cap ν A C X a W hH
      (mul_nonneg hCj (Real.rpow_nonneg hH.le _)) hW inter_subset_left hbox hcube
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, W, Matrix.cons_val_zero,
      Matrix.cons_val_succ] at hrect
    have h5 : 2 * H / H + 3 = 5 := by field_simp; ring
    rw [h5] at hrect
    have hgrid : 2 * (2 * B) / H + 3 ≤ 7 * B / H := by
      rw [div_add' _ _ _ hH.ne', div_le_div_iff_of_pos_right hH]
      nlinarith
    have hgrid0 : 0 ≤ 2 * (2 * B) / H + 3 := by positivity
    have hraw : ν.real C ≤ 245 * B ^ 2 * Cj * H ^ d := by
      refine hrect.trans ?_
      have hpow : H ^ (2 + d) = H ^ 2 * H ^ d := by
        rw [Real.rpow_add hH]; norm_num
      calc (2 * (2 * B) / H + 3) * ((2 * (2 * B) / H + 3) * 5) * (Cj * H ^ (2 + d))
          ≤ (7 * B / H) * ((7 * B / H) * 5) * (Cj * H ^ (2 + d)) := by
            gcongr
        _ = 245 * B ^ 2 * Cj * H ^ d := by
            rw [hpow]; field_simp; ring
    have hraw' : ν.real C ≤ K * H ^ d :=
      hraw.trans (mul_le_mul_of_nonneg_right hKprior hc.le)
    change (ν.restrict A).real ((fun l => (⌊Z l / H⌋ : ℤ)) ⁻¹' {b}) ≤ K * H ^ d
    rw [Measure.real, Measure.restrict_apply (hcode (MeasurableSet.singleton b))]
    simpa [C, Measure.real, Set.preimage, inter_comm] using hraw'
  refine ⟨J, hcard', hcover', hcap, ?_⟩
  intro b hb
  rw [scalarGroupPrior_real _ _ _ hc MeasurableSet.univ, univ_inter]
  exact (div_le_iff₀ hc).mpr (hcap b hb)

/-- The constant of the version-2 starting groups. -/
def v2GroupConst (K : ℝ) : ℝ := 200000 * K ^ 6

namespace UpperHyp

variable {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ} {c : Λ → Fin 7 → ℝ}
  {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {K ζ d : ℝ}

/-- **Starting-bin palette of labelled trajectories** at one time `t₀`. -/
theorem v2_starting_group_palette [IsFiniteMeasure ν] (h : UpperHyp ν c E F K ζ d)
    (hK : 1 ≤ K) (hd0 : 0 ≤ d) (hd : d ≤ 1) {H t₀ : ℝ} (hH : 0 < H) (hH1 : H ≤ 1)
    (hζH : ζ ≤ H) :
    ∃ J : Finset ℤ, (J.card : ℝ) ≤ v2GroupConst K / H ^ d ∧
      (∀ l, (l, t₀) ∈ E → (⌊zS F (c l) t₀ / H⌋ : ℤ) ∈ J) ∧
      (∀ b ∈ J, (ν.restrict ((fun l => (l, t₀)) ⁻¹' E)).real
        {l | (⌊zS F (c l) t₀ / H⌋ : ℤ) = b} ≤ v2GroupConst K * H ^ d) ∧
      ∀ b ∈ J, (scalarGroupPrior (ν.restrict ((fun l => (l, t₀)) ⁻¹' E))
        (fun l => ⌊zS F (c l) t₀ / H⌋) b (H ^ d)).real univ ≤ v2GroupConst K := by
  let A : Set Λ := (fun l => (l, t₀)) ⁻¹' E
  have hA : MeasurableSet A := measurable_prodMk_right h.event_measurable
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hK0 : 0 ≤ K := hKpos.le
  have hKsq : 1 ≤ K ^ 2 := by nlinarith
  have hBY : 1 ≤ 2 * K := by linarith
  have hBZ : 0 < 7 * K ^ 2 := by positivity
  have hHBZ : H ≤ 2 * (7 * K ^ 2) := by nlinarith
  have hY : ∀ l ∈ A, ∀ i, |zy (c l) t₀ i| ≤ 2 * K := fun l hl => (h.active_bounds hl).2.1
  have hsupport : ∀ l ∈ A, zS F (c l) t₀ ∈ scalarSupport c F E t₀ ∩
      Icc (-(7 * K ^ 2)) (7 * K ^ 2) := by
    intro l hl
    have hb := (h.active_bounds hl).2.2.2.2
    refine ⟨⟨l, hl, rfl⟩, abs_le.mp (hb.trans (by nlinarith))⟩
  have hSH : IntervalAD H d K (scalarSupport c F E t₀) := by
    intro r R a hHr hrR
    exact h.support_AD t₀ r R a (hζH.trans hHr) hrR
  have hjoint : ∀ a b₀ b₁ : ℝ,
      ν.real {l | l ∈ A ∧ zy (c l) t₀ 0 ∈ Icc b₀ (b₀ + H) ∧ zy (c l) t₀ 1 ∈ Icc b₁ (b₁ + H) ∧
        zS F (c l) t₀ ∈ Icc a (a + H)} ≤ (125 * K ^ 4) * H ^ (2 + d) := by
    intro a b₀ b₁
    have hh := h.anchor_joint_cap hK hd0 hd t₀ a b₀ b₁ H hζH hH
    refine le_trans (measureReal_mono ?_ (measure_ne_top ν _)) hh
    rintro l ⟨hl, h0, h1, h2⟩
    exact ⟨hl, h2, h0, h1⟩
  have hbase : 1 ≤ 2 * (7 * K ^ 2) := by nlinarith
  have hpow : (2 * (7 * K ^ 2)) ^ d ≤ 2 * (7 * K ^ 2) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hbase hd
  have hK36 : K ^ 3 ≤ K ^ 6 := pow_le_pow_right₀ hK (by norm_num)
  have hcount : 3 * K * (2 * (7 * K ^ 2)) ^ d ≤ v2GroupConst K := by
    have hh := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 3 * K)
    unfold v2GroupConst
    nlinarith [pow_nonneg hK0 6]
  have hprior : 245 * (2 * K) ^ 2 * (125 * K ^ 4) ≤ v2GroupConst K := by
    unfold v2GroupConst
    nlinarith [pow_nonneg hK0 6]
  exact v2_starting_group_palette_of_caps ν A hA (fun l => zy (c l) t₀) (fun l => zS F (c l) t₀)
    (measurable_zS_at h.measurable_c F t₀) (scalarSupport c F E t₀)
    hH hH1 hBY hBZ hHBZ hK0 (by positivity) (by unfold v2GroupConst; positivity) hSH hY hsupport
    hjoint hcount hprior

end UpperHyp

/-- **The cap of the residual kernel** inside one normalized starting group. -/
theorem v2_left_residual_group_cap {Λ : Type*} [MeasurableSpace Λ]
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c) (ν : Measure Λ) [IsFiniteMeasure ν]
    {E : Set (Λ × ℝ)} (hE : MeasurableSet E) {F : ℝ → Fin 2 → ℝ} (hF : Measurable F)
    (s : ℝ) (bin : ℤ) {H p K C d anchor : ℝ}
    (hH : 0 < H) (hH1 : H ≤ 1) (hp : 0 < p) (hHp : H ≤ p)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hanchor : anchor ∈ Icc (0 : ℝ) 1)
    (hblock : E ⊆ univ ×ˢ Icc s (s + H))
    (hcoeff : ∀ q ∈ E, |c q.1 4| ≤ K ∧ |c q.1 6| ≤ K)
    (hcap : ∀ t a b₀ b₁ : ℝ,
      ν.real {l | (l, t) ∈ E ∧ zy (c l) t 0 ∈ Icc b₀ (b₀ + H * p) ∧
        zy (c l) t 1 ∈ Icc b₁ (b₁ + H * p) ∧ zS F (c l) t ∈ Icc a (a + H * p)} ≤
        C * (H * p) ^ (2 + d)) :
    let t₀ := s + H * anchor
    let A := {l | (l, t₀) ∈ E ∧ (⌊zS F (c l) t₀ / H⌋ : ℤ) = bin}
    let νb := scalarGroupPrior (ν.restrict ((fun l => (l, t₀)) ⁻¹' E))
      (fun l => ⌊zS F (c l) t₀ / H⌋) bin (H ^ d)
    ∀ u (j : Fin 2 → ℤ) (z : ℤ), νb.real {l | (l, u) ∈ scalarLeftBlockEvent E A s H ∧
      (fun i => (⌊zy (c l) t₀ i / p⌋ : ℤ)) = j ∧
        (⌊v2LeftObservation c F s H bin (u, l) / p⌋ : ℤ) = z} ≤
        125 * (1 + 2 * K) ^ 2 * C * p ^ (2 + d) := by
  intro t₀ A νb u j z
  let Aanchor : Set Λ := (fun l => (l, t₀)) ⁻¹' E
  let Q := scalarLeftBlockEvent E A s H
  let B : Set Λ := {l | (l, u) ∈ Q ∧ (fun i => (⌊zy (c l) t₀ i / p⌋ : ℤ)) = j ∧
    (⌊v2LeftObservation c F s H bin (u, l) / p⌋ : ℤ) = z}
  have hcode : Measurable (fun l => (⌊zS F (c l) t₀ / H⌋ : ℤ)) :=
    ((measurable_zS_at hc F t₀).div_const H).floor
  have hAm : MeasurableSet A :=
    (measurable_prodMk_right hE).inter (hcode (MeasurableSet.singleton bin))
  have hQm := scalarLeftBlockEvent_measurable hE hAm s H
  have hycode : Measurable (fun l => (fun i => (⌊zy (c l) t₀ i / p⌋ : ℤ))) := by
    apply measurable_pi_lambda
    intro i
    exact ((measurable_zy_coord_at hc t₀ i).div_const p).floor
  have hBm : MeasurableSet B := (measurable_prodMk_right hQm).inter
    ((hycode (MeasurableSet.singleton j)).inter
      ((((v2LeftObservation_measurable hc hF s H bin).comp
        (measurable_const.prodMk measurable_id)).div_const p).floor (MeasurableSet.singleton z)))
  have hBsub : B ⊆ Aanchor ∩ ((fun l => (⌊zS F (c l) t₀ / H⌋ : ℤ)) ⁻¹' {bin}) :=
    fun l hl => ⟨hl.1.2.1, hl.1.2.2⟩
  have hc0 : 0 < H ^ d := Real.rpow_pos_of_pos hH _
  rw [show νb = scalarGroupPrior (ν.restrict Aanchor) (fun l => ⌊zS F (c l) t₀ / H⌋) bin (H ^ d)
    from rfl, original_scalar_group_real ν Aanchor _ bin hc0 hBm hBsub]
  -- the current box
  have hmove : ∀ l ∈ B, ∀ i, |zy (c l) (s + H * u) i - zy (c l) t₀ i| ≤ K * H := by
    intro l hl i
    have hu := (scalarLeftBlockEvent_unit hH hblock hl.1).2
    have hud : |u - anchor| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hanchor.1, hanchor.2]
    have hv := hcoeff (l, s + H * u) hl.1.1
    have hvi : |zv (c l) i| ≤ K := by
      fin_cases i
      · simpa using hv.1
      · simpa using hv.2
    have he : zy (c l) (s + H * u) i - zy (c l) t₀ i = zv (c l) i * (H * (u - anchor)) := by
      rw [zy_add (c l) (s + H * u) t₀]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, t₀]
      ring
    rw [he, abs_mul, abs_mul, abs_of_pos hH]
    calc |zv (c l) i| * (H * |u - anchor|) ≤ K * (H * 1) :=
          mul_le_mul hvi (mul_le_mul_of_nonneg_left hud hH.le) (by positivity) hK
      _ = K * H := by ring
  let X : Λ → Fin 3 → ℝ := fun l =>
    ![zy (c l) (s + H * u) 0, zy (c l) (s + H * u) 1, zS F (c l) (s + H * u)]
  let a : Fin 3 → ℝ := ![p * j 0 - K * H, p * j 1 - K * H, H * bin + H * (p * z)]
  let W : Fin 3 → ℝ := ![(1 + 2 * K) * p, (1 + 2 * K) * p, H * p]
  have hW : ∀ i, 0 ≤ W i := by
    intro i; fin_cases i <;> simp [W] <;> positivity
  have hKH : K * H ≤ K * p := mul_le_mul_of_nonneg_left hHp hK
  have hbox : ∀ l ∈ B, ∀ i, X l i ∈ Icc (a i) (a i + W i) := by
    intro l hl i
    have hcube : ∀ i, zy (c l) t₀ i ∈ Icc (p * j i) (p * j i + p) := by
      intro i
      have hji : (⌊zy (c l) t₀ i / p⌋ : ℤ) = j i := congrFun hl.2.1 i
      exact (mesh_lower_endpoint hp hji).1
    have hZ : v2LeftObservation c F s H bin (u, l) ∈ Icc (p * z) (p * z + p) :=
      (mesh_lower_endpoint hp hl.2.2).1
    have hm0 := abs_le.mp (hmove l hl 0)
    have hm1 := abs_le.mp (hmove l hl 1)
    have hc0' := hcube 0
    have hc1' := hcube 1
    fin_cases i
    · show zy (c l) (s + H * u) 0 ∈
        Icc (p * j 0 - K * H) (p * j 0 - K * H + (1 + 2 * K) * p)
      constructor <;> linarith [hm0.1, hm0.2, hc0'.1, hc0'.2]
    · show zy (c l) (s + H * u) 1 ∈
        Icc (p * j 1 - K * H) (p * j 1 - K * H + (1 + 2 * K) * p)
      constructor <;> linarith [hm1.1, hm1.2, hc1'.1, hc1'.2]
    · show zS F (c l) (s + H * u) ∈
        Icc (H * bin + H * (p * z)) (H * bin + H * (p * z) + H * p)
      have hZ' : (zS F (c l) (s + H * u) - H * bin) / H ∈ Icc (p * z) (p * z + p) := hZ
      have hlo := (le_div_iff₀ hH).mp hZ'.1
      have hhi := (div_le_iff₀ hH).mp hZ'.2
      constructor <;> linarith
  have hcubes : ∀ e : Fin 3 → ℝ,
      ν.real {l | l ∈ {l | (l, s + H * u) ∈ E} ∧ ∀ i, X l i ∈ Icc (e i) (e i + H * p)} ≤
        C * (H * p) ^ (2 + d) := by
    intro e
    refine le_trans (measureReal_mono ?_ (measure_ne_top ν _))
      (hcap (s + H * u) (e 2) (e 0) (e 1))
    intro l hl
    have h0 : zy (c l) (s + H * u) 0 ∈ Icc (e 0) (e 0 + H * p) := hl.2 0
    have h1 : zy (c l) (s + H * u) 1 ∈ Icc (e 1) (e 1 + H * p) := hl.2 1
    have h2 : zS F (c l) (s + H * u) ∈ Icc (e 2) (e 2 + H * p) := hl.2 2
    exact ⟨hl.1, h0, h1, h2⟩
  have hq : 0 < H * p := mul_pos hH hp
  have hrect := original_rectangular_cap ν {l | (l, s + H * u) ∈ E} B X a W hq
    (mul_nonneg hC (Real.rpow_nonneg hq.le _)) hW (fun l hl => hl.1.1) hbox hcubes
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, W, Matrix.cons_val_zero,
    Matrix.cons_val_succ] at hrect
  have h5 : 2 * (H * p) / (H * p) + 3 = 5 := by field_simp; ring
  rw [h5] at hrect
  have hgrid : 2 * ((1 + 2 * K) * p) / (H * p) + 3 ≤ 5 * (1 + 2 * K) / H := by
    have e : 2 * ((1 + 2 * K) * p) / (H * p) = 2 * (1 + 2 * K) / H := by
      field_simp
    rw [e, div_add' _ _ _ hH.ne', div_le_div_iff_of_pos_right hH]
    nlinarith
  have hgrid0 : 0 ≤ 2 * ((1 + 2 * K) * p) / (H * p) + 3 := by positivity
  have hpow : (H * p) ^ (2 + d) = H ^ 2 * (H ^ d * p ^ (2 + d)) := by
    rw [Real.mul_rpow hH.le hp.le, Real.rpow_add hH]; norm_num; ring
  have hraw : ν.real B ≤ H ^ d * (125 * (1 + 2 * K) ^ 2 * C * p ^ (2 + d)) := by
    refine hrect.trans ?_
    calc (2 * ((1 + 2 * K) * p) / (H * p) + 3) * ((2 * ((1 + 2 * K) * p) / (H * p) + 3) * 5) *
          (C * (H * p) ^ (2 + d))
        ≤ (5 * (1 + 2 * K) / H) * ((5 * (1 + 2 * K) / H) * 5) * (C * (H * p) ^ (2 + d)) := by
          gcongr
      _ = H ^ d * (125 * (1 + 2 * K) ^ 2 * C * p ^ (2 + d)) := by
          rw [hpow]; field_simp; ring
  rw [div_le_iff₀ hc0]
  linarith

/-- **The cube-code palette** of tangential positions in `[-2K, 2K]²`. -/
theorem v2_residual_spatial_palette {Λ : Type*} (A : Set Λ) (Y : Λ → Fin 2 → ℝ)
    {K p : ℝ} (hK : 1 ≤ K) (hp : 0 < p) (hp1 : p ≤ 1)
    (hY : ∀ l ∈ A, ∀ i, |Y l i| ≤ 2 * K) :
    ∃ J : Finset (Fin 2 → ℤ), (J.card : ℝ) ≤ 49 * K ^ 2 * p ^ (-(2 : ℝ)) ∧
      ∀ l ∈ A, (fun i => (⌊Y l i / p⌋ : ℤ)) ∈ J := by
  classical
  choose J hcard hcover _ using fun i : Fin 2 =>
    bounded_scalar_grid_indices A (fun l => Y l i) (by positivity : (0 : ℝ) ≤ 2 * K) hp
      (fun l hl => hY l hl i)
  refine ⟨Fintype.piFinset J, ?_, fun l hl => Fintype.mem_piFinset.mpr (fun i => hcover i l hl)⟩
  have hone : ∀ i, ((J i).card : ℝ) ≤ 7 * K / p := by
    intro i
    refine (hcard i).trans ?_
    rw [div_add' _ _ _ hp.ne', div_le_div_iff_of_pos_right hp]
    nlinarith
  rw [Fintype.card_piFinset, Nat.cast_prod, Fin.prod_univ_two]
  have h0 := hone 0
  have h1 := hone 1
  calc ((J 0).card : ℝ) * ((J 1).card : ℝ) ≤ (7 * K / p) * (7 * K / p) :=
        mul_le_mul h0 h1 (Nat.cast_nonneg _) (by positivity)
    _ = 49 * K ^ 2 * p ^ (-(2 : ℝ)) := by
        rw [Real.rpow_neg hp.le, Real.rpow_two]; field_simp; ring

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2
