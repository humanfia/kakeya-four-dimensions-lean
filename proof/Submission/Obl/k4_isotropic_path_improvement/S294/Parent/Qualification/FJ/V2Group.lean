-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FJ.V2Group, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FJ/V2Group.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FJ/V2Group.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FJ/V2Group.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2Data
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarAnisotropicCaps
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGroupNormalization
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGridGeometry
import Mathlib.MeasureTheory.Function.Floor

set_option autoImplicit false

/-!
# Sliced starting groups in version 2 (paper `tex-05`, "Fitting one row component")

The `j = 2` counterpart of `ScalarStartingGroup.lean` / `ScalarBlockGroup.lean` of o078 (session
x0662, branch `x0662` at `f2bac599`).  At an anchor time `t₀`, the labelled trajectories are
grouped by the `H`-bin of their scalar `S(t₀)` and the `p`-bin of the OTHER tangential coordinate
`y_{k'}(t₀)` (`k' = Fin.rev k`, the slice of the paper), and every group is normalized by its
geometric weight `H^d p`:

* `slicedCode`;
* `sliced_group_palette`: at most `252 K⁴ / (H^d p)` occupied groups, each of original mass at
  most `250000 K⁶ H^d p` (x0662's `original_normalized_sliced_cap_enlarged` with the sheared
  anchor cap of `V2Data`);
* `exists_sliced_starting_group`: one normalized group carries a fixed fraction of any event.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

noncomputable section

variable {Λ : Type*} [MeasurableSpace Λ]

/-- The sliced group of a trajectory at the anchor time `t₀`. -/
def slicedCode (c : Λ → Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ) (t₀ H p : ℝ) (k : Fin 2) (l : Λ) :
    ℤ × ℤ :=
  (⌊zS F (c l) t₀ / H⌋, ⌊zy (c l) t₀ (Fin.rev k) / p⌋)

theorem measurable_zS_at {c : Λ → Fin 7 → ℝ} (hc : Measurable c) (F : ℝ → Fin 2 → ℝ) (t : ℝ) :
    Measurable (fun l => zS F (c l) t) := by
  have hcomp : ∀ e : Fin 7, Measurable (fun l => c l e) :=
    fun e => (measurable_pi_apply e).comp hc
  have h0 := hcomp 0; have h1 := hcomp 1; have h2 := hcomp 2; have h3 := hcomp 3
  have h4 := hcomp 4; have h5 := hcomp 5; have h6 := hcomp 6
  simp only [zS, zx, dot_two, zy_zero, zy_one]
  fun_prop

theorem measurable_zy_at {c : Λ → Fin 7 → ℝ} (hc : Measurable c) (t : ℝ) (i : Fin 2) :
    Measurable (fun l => zy (c l) t i) := by
  have hcomp : ∀ e : Fin 7, Measurable (fun l => c l e) :=
    fun e => (measurable_pi_apply e).comp hc
  have h3 := hcomp 3; have h4 := hcomp 4; have h5 := hcomp 5; have h6 := hcomp 6
  fin_cases i
  · simp only [Fin.zero_eta, zy_zero]; fun_prop
  · simp only [Fin.mk_one, zy_one]; fun_prop

theorem measurable_slicedCode {c : Λ → Fin 7 → ℝ} (hc : Measurable c) (F : ℝ → Fin 2 → ℝ)
    (t₀ H p : ℝ) (k : Fin 2) : Measurable (slicedCode c F t₀ H p k) :=
  (((measurable_zS_at hc F t₀).div_const H).floor).prodMk
    (((measurable_zy_at hc t₀ (Fin.rev k)).div_const p).floor)

/-- The sheared anchor cap in the coordinates `(y_k, y_{k'}, S)`. -/
theorem sliced_anchor_cube_cap {ν : Measure Λ} [IsFiniteMeasure ν] {c : Λ → Fin 7 → ℝ}
    {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {K ζ d : ℝ} (h : UpperHyp ν c E F K ζ d)
    (hK : 1 ≤ K) (hd0 : 0 ≤ d) (hd : d ≤ 1) (t₀ : ℝ) (k : Fin 2) (r : ℝ) (hr : ζ ≤ r)
    (hr0 : 0 < r) (b : Fin 3 → ℝ) :
    ν.real {l | l ∈ (fun l => (l, t₀)) ⁻¹' E ∧ ∀ i,
      (![zy (c l) t₀ k, zy (c l) t₀ (Fin.rev k), zS F (c l) t₀] : Fin 3 → ℝ) i ∈
        Icc (b i) (b i + r)} ≤ 125 * K ^ 4 * r ^ (2 + d) := by
  rcases fin_two_eq 0 k with rfl | rfl
  · refine (measureReal_mono ?_ (measure_ne_top ν _)).trans
      (h.anchor_joint_cap hK hd0 hd t₀ (b 2) (b 0) (b 1) r hr hr0)
    rintro l ⟨hl, hX⟩
    have h0 := hX 0; have h1 := hX 1; have h2 := hX 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
    exact ⟨hl, h2, h0, by simpa [Fin.rev] using h1⟩
  · refine (measureReal_mono ?_ (measure_ne_top ν _)).trans
      (h.anchor_joint_cap hK hd0 hd t₀ (b 2) (b 1) (b 0) r hr hr0)
    rintro l ⟨hl, hX⟩
    have h0 := hX 0; have h1 := hX 1; have h2 := hX 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
    exact ⟨hl, h2, by simpa [Fin.rev] using h1, by simpa [Fin.rev] using h0⟩

/-- **The sliced palette.** -/
theorem sliced_group_palette {ν : Measure Λ} [IsFiniteMeasure ν] {c : Λ → Fin 7 → ℝ}
    {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {K ζ d H p : ℝ} (h : UpperHyp ν c E F K ζ d)
    (hK : 1 ≤ K) (hd0 : 0 ≤ d) (hd : d ≤ 1) (hH : 0 < H) (hH1 : H ≤ 1) (hζH : ζ ≤ H)
    (hHp : H ≤ p) (hp1 : p ≤ 1) (t₀ : ℝ) (k : Fin 2) :
    ∃ J : Finset (ℤ × ℤ), (J.card : ℝ) ≤ 250000 * K ^ 6 / (H ^ d * p) ∧
      (∀ l, (l, t₀) ∈ E → slicedCode c F t₀ H p k l ∈ J) ∧
      ∀ b ∈ J, (ν.restrict ((fun l => (l, t₀)) ⁻¹' E)).real
        (slicedCode c F t₀ H p k ⁻¹' {b}) ≤ 250000 * K ^ 6 * (H ^ d * p) := by
  classical
  set A : Set Λ := (fun l => (l, t₀)) ⁻¹' E with hAdef
  have hA : MeasurableSet A := measurable_prodMk_right h.event_measurable
  have hK0 : 0 ≤ K := by linarith
  have hp : 0 < p := hH.trans_le hHp
  have hHd : 0 < H ^ d := Real.rpow_pos_of_pos hH d
  set BZ : ℝ := 4 * K ^ 2 + 3 * K with hBZ
  have hBZ1 : 1 ≤ BZ := by rw [hBZ]; nlinarith
  -- the scalar bins
  have hSH : IntervalAD H d K (scalarSupport c F E t₀) := by
    intro r R a hHr hrR
    exact h.support_AD t₀ r R a (hζH.trans hHr) hrR
  obtain ⟨JZ, hJZcard, hJZcover⟩ := intervalAD_grid_list (a := -BZ) hH
    (show H ≤ 2 * BZ by linarith) hSH
  -- the slice bins
  set JW : Finset ℤ := Finset.Icc ⌊-(2 * K) / p⌋ ⌊(2 * K) / p⌋ with hJW
  have hJWcard : (JW.card : ℝ) ≤ 6 * K / p := by
    have := card_Icc_floor_le (y₀ := 0) (δ := 2 * K) hp (by positivity)
    simp only [zero_sub, zero_add] at this
    have h2 : 2 * (2 * K) / p + 2 ≤ 6 * K / p := by
      rw [div_add' _ _ _ hp.ne', div_le_div_iff_of_pos_right hp]; nlinarith
    rw [hJW]
    have e : -(2 * K) / p = (-(2 * K)) / p := rfl
    linarith
  refine ⟨JZ ×ˢ JW, ?_, ?_, ?_⟩
  · -- count
    rw [Finset.card_product, Nat.cast_mul]
    have hpow : (2 * BZ / H) ^ d ≤ 2 * BZ / H ^ d := by
      rw [Real.div_rpow (by positivity) hH.le]
      gcongr
      calc (2 * BZ) ^ d ≤ (2 * BZ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) hd
        _ = 2 * BZ := Real.rpow_one _
    have hZc : (JZ.card : ℝ) ≤ 3 * K * (2 * BZ) / H ^ d := by
      calc (JZ.card : ℝ) ≤ 3 * (K * (2 * BZ / H) ^ d) := hJZcard
        _ ≤ 3 * (K * (2 * BZ / H ^ d)) := by gcongr
        _ = 3 * K * (2 * BZ) / H ^ d := by ring
    have hBZK : 2 * BZ ≤ 14 * K ^ 2 := by rw [hBZ]; nlinarith
    calc (JZ.card : ℝ) * JW.card ≤ (3 * K * (2 * BZ) / H ^ d) * (6 * K / p) := by
          gcongr
      _ = 18 * K ^ 2 * (2 * BZ) / (H ^ d * p) := by field_simp; ring
      _ ≤ 18 * K ^ 2 * (14 * K ^ 2) / (H ^ d * p) := by gcongr
      _ ≤ 250000 * K ^ 6 / (H ^ d * p) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          have h46 : K ^ 4 ≤ K ^ 6 := pow_le_pow_right₀ hK (by norm_num)
          nlinarith [pow_nonneg hK0 4]
  · -- cover
    intro l hl
    have hb := h.active_bounds hl
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · have hS := abs_le.mp hb.2.2.2.2
      exact hJZcover _ ⟨⟨l, hl, rfl⟩, by linarith [hS.1], by linarith [hS.2]⟩
    · have hW := floor_mem_Icc_of_abs_le hp (y := zy (c l) t₀ (Fin.rev k)) (y₀ := 0)
        (δ := 2 * K) (by simpa using hb.2.1 (Fin.rev k))
      simpa [hJW, slicedCode, neg_div] using hW
  · -- per-group cap
    intro b _
    set G : Set Λ := A ∩ slicedCode c F t₀ H p k ⁻¹' {b} with hG
    have hGsub : G ⊆ A := inter_subset_left
    have hbox : ∀ l ∈ G,
        (![zy (c l) t₀ k, zy (c l) t₀ (Fin.rev k), zS F (c l) t₀] : Fin 3 → ℝ) 0 ∈
          Icc (-(2 * K)) (-(2 * K) + (4 * K) * 1) ∧
        (![zy (c l) t₀ k, zy (c l) t₀ (Fin.rev k), zS F (c l) t₀] : Fin 3 → ℝ) 1 ∈
          Icc (p * b.2) (p * b.2 + (4 * K) * p) ∧
        (![zy (c l) t₀ k, zy (c l) t₀ (Fin.rev k), zS F (c l) t₀] : Fin 3 → ℝ) 2 ∈
          Icc (H * b.1) (H * b.1 + H * 1) := by
      intro l hl
      have hb' := h.active_bounds hl.1
      have hcode : slicedCode c F t₀ H p k l = b := hl.2
      simp only [slicedCode, Prod.ext_iff] at hcode
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      have hy := abs_le.mp (hb'.2.1 k)
      have hw := (mesh_lower_endpoint hp hcode.2).1
      have hz := (mesh_lower_endpoint hH hcode.1).1
      refine ⟨⟨hy.1, by linarith [hy.2]⟩, ⟨hw.1, ?_⟩, ⟨hz.1, by linarith [hz.2]⟩⟩
      have : p ≤ (4 * K) * p := by nlinarith
      linarith [hw.2]
    have hcube : ∀ b' : Fin 3 → ℝ,
        ν.real {l | l ∈ A ∧ ∀ i,
          (![zy (c l) t₀ k, zy (c l) t₀ (Fin.rev k), zS F (c l) t₀] : Fin 3 → ℝ) i ∈
            Icc (b' i) (b' i + H * 1)} ≤ (125 * K ^ 4) * (H * 1) ^ (2 + d) := by
      intro b'
      simpa only [mul_one] using
        sliced_anchor_cube_cap h hK hd0 hd t₀ k H hζH hH b'
    have hh := original_normalized_sliced_cap_enlarged ν A G
      (fun l => ![zy (c l) t₀ k, zy (c l) t₀ (Fin.rev k), zS F (c l) t₀])
      ![-(2 * K), p * b.2, H * b.1] hH hH1 (L := 4 * K) (by linarith) hHp
      (r := 1) (by norm_num) le_rfl (by positivity) hGsub
      (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] using hbox) hcube
    have hraw : ν.real G ≤ 250000 * K ^ 6 * (H ^ d * p) := by
      have hpos : 0 < H ^ d * p := mul_pos hHd hp
      have h1 := (div_le_iff₀ hpos).mp hh
      have hcoef : 125 * (4 * K) ^ 2 * (125 * K ^ 4) * (1 : ℝ) ^ (1 + d) ≤ 250000 * K ^ 6 := by
        rw [Real.one_rpow]; nlinarith [pow_nonneg hK0 6]
      exact h1.trans (mul_le_mul_of_nonneg_right hcoef hpos.le)
    rw [Measure.real, Measure.restrict_apply
      (measurable_slicedCode h.measurable_c F t₀ H p k (MeasurableSet.singleton b))]
    rw [inter_comm]
    exact hraw

/-- **One normalized sliced group carries a fixed fraction of an event.** -/
theorem exists_sliced_starting_group {Θ : Type*} [MeasurableSpace Θ] {ν : Measure Λ}
    [IsFiniteMeasure ν] {c : Λ → Fin 7 → ℝ} {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ}
    {K ζ d H p δ : ℝ} (h : UpperHyp ν c E F K ζ d)
    (hK : 1 ≤ K) (hd0 : 0 ≤ d) (hd : d ≤ 1) (hH : 0 < H) (hH1 : H ≤ 1) (hζH : ζ ≤ H)
    (hHp : H ≤ p) (hp1 : p ≤ 1) (t₀ : ℝ) (k : Fin 2)
    (μ : Measure Θ) [IsFiniteMeasure μ] {P : Set (Θ × Λ)} (hP : MeasurableSet P)
    (hPA : P ⊆ univ ×ˢ ((fun l => (l, t₀)) ⁻¹' E))
    (hδ : 0 < δ) (hmass : δ ≤ (μ.prod ν).real P) :
    ∃ b : ℤ × ℤ,
      (scalarGroupPrior (ν.restrict ((fun l => (l, t₀)) ⁻¹' E))
        (slicedCode c F t₀ H p k) b (H ^ d * p)).real univ ≤ 250000 * K ^ 6 ∧
      δ / (250000 * K ^ 6) ≤
        (μ.prod (scalarGroupPrior (ν.restrict ((fun l => (l, t₀)) ⁻¹' E))
          (slicedCode c F t₀ H p k) b (H ^ d * p))).real
            (P ∩ (univ ×ˢ {l | slicedCode c F t₀ H p k l = b})) := by
  set A : Set Λ := (fun l => (l, t₀)) ⁻¹' E with hAdef
  have hA : MeasurableSet A := measurable_prodMk_right h.event_measurable
  have hp : 0 < p := hH.trans_le hHp
  have hc : 0 < H ^ d * p := mul_pos (Real.rpow_pos_of_pos hH d) hp
  have hcode := measurable_slicedCode h.measurable_c F t₀ H p k
  obtain ⟨J, hcard, hcover, hcap⟩ := sliced_group_palette h hK hd0 hd hH hH1 hζH hHp hp1 t₀ k
  have hprod : μ.prod (ν.restrict A) = (μ.prod ν).restrict (univ ×ˢ A) := by
    simpa only [Measure.restrict_univ] using
      (Measure.prod_restrict (μ := μ) (ν := ν) univ A)
  have hmass' : δ ≤ (μ.prod (ν.restrict A)).real P := by
    simpa only [hprod, Measure.real, Measure.restrict_apply hP, inter_eq_left.mpr hPA] using hmass
  have hKpos : 0 < 250000 * K ^ 6 := by positivity
  obtain ⟨b, hb, hprior, hgroup⟩ := exists_original_normalized_scalar_group μ (ν.restrict A)
    hP (slicedCode c F t₀ H p k) hcode J hc hKpos hδ
    (fun q hq => hcover q.2 (hPA hq).2) hmass' hcard hcap
  refine ⟨b, hprior, ?_⟩
  change δ / (250000 * K ^ 6) ≤
    (μ.prod (scalarGroupPrior (ν.restrict A) (slicedCode c F t₀ H p k) b (H ^ d * p))).real
      (P ∩ (univ ×ˢ (slicedCode c F t₀ H p k ⁻¹' {b})))
  rw [original_scalar_group_mass μ (ν.restrict A) _ b hc
    (hP.inter (MeasurableSet.univ.prod (hcode (MeasurableSet.singleton b))))]
  rw [original_scalar_group_mass μ (ν.restrict A) _ b hc hP] at hgroup
  simpa only [inter_assoc, inter_self] using hgroup

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2
