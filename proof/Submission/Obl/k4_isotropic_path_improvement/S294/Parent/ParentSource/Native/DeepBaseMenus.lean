-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.DeepBaseMenus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/DeepBaseMenus.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/DeepBaseMenus.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/DeepBaseMenus.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.FineAnchorPosition
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeDeepScale
import Submission.Lib.K4ListedExceptions.FrameCodes

/-! A whole deeper original assignment resolves the native base of its
earlier ancestor. One sufficiently small deeper packet meets at most27
base-grid codes, independently of the grid's total size. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4ListedExceptions

noncomputable def PathData.nativeBaseCoordinates {W : ℕ} (p : PathData W)
    (b : Fin p.C) (x : (ℕ × (Fin 6 → ℝ)) × ℝ) : Fin 3 → ℝ :=
  ![(x.2 - (p.j b : ℝ) / (2 : ℝ) ^ p.T (p.lev b)) /
      ((2 : ℝ) ^ p.T (p.lev b))⁻¹,
    packetPosition (p.Q b) (p.c b) (p.u b) x.1 x.2 0,
    packetPosition (p.Q b) (p.c b) (p.u b) x.1 x.2 1]

noncomputable def PathData.observedNativeBaseCoordinates {W : ℕ} (p : PathData W)
    (b : Fin p.C) (o : EuclideanSpace ℝ (Fin 3) × ℤ) : Fin 3 → ℝ :=
  ![(o.1 0 - (p.j b : ℝ) / (2 : ℝ) ^ p.T (p.lev b)) /
      ((2 : ℝ) ^ p.T (p.lev b))⁻¹,
    observedPacketPosition (p.Q b) (p.c b) (p.u b) o 0,
    observedPacketPosition (p.Q b) (p.c b) (p.u b) o 1]

theorem PathData.native_base_exact_observation {W : ℕ} (p : PathData W)
    (b : Fin p.C) (B a : ℝ) (x : (ℕ × (Fin 6 → ℝ)) × ℝ) :
    p.nativeBaseCoordinates b x = p.observedNativeBaseCoordinates b (obs B a x) := rfl

section Path

variable {W : ℕ} {p : PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {profile : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
  {Mp Dp : ℕ} {σ : ℝ}

theorem PathData.Valid.deep_original_base_box
    (hp : p.Valid Nk L ω ν E B profile κ₁ m s δ₀ Mp Dp σ) (hN : 1 ≤ Nk)
    (b f : Fin p.C) (hA : p.A f ⊆ p.A b) :
    ∃ anchor : Fin 3 → ℝ, ∀ x ∈ p.F f, ∀ j : Fin 3,
      |p.nativeBaseCoordinates b x j - anchor j| ≤
        (1 + p.κ ^ 3 * Nk ^ (2 * δ₀ * L) + 2 * p.κ) *
          ((2 : ℝ) ^ p.T (p.lev b) / (2 : ℝ) ^ p.T (p.lev f)) := by
  have hκ : 0 ≤ p.κ := by linarith [hp.1]
  let startOld := (p.j b : ℝ) / (2 : ℝ) ^ p.T (p.lev b)
  let startDeep := (p.j f : ℝ) / (2 : ℝ) ^ p.T (p.lev f)
  let qOld := ((2 : ℝ) ^ p.T (p.lev b))⁻¹
  let qDeep := ((2 : ℝ) ^ p.T (p.lev f))⁻¹
  let ratio := (2 : ℝ) ^ p.T (p.lev b) / (2 : ℝ) ^ p.T (p.lev f)
  let R := (1 + p.κ ^ 3 * Nk ^ (2 * δ₀ * L) + 2 * p.κ) * ratio
  have hqOld : 0 < qOld := by dsimp only [qOld]; positivity
  have hratio : 0 ≤ ratio := by dsimp only [ratio]; positivity
  have hratioEq : qDeep / qOld = ratio := by
    dsimp only [qDeep, qOld, ratio]
    simp only [div_eq_mul_inv, inv_inv]
    ac_rfl
  have hend : startDeep + qDeep =
      ((p.j f : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev f) := by dsimp only [startDeep, qDeep]; ring
  have htStart : startDeep ∈ Icc ((p.j f : ℝ) / (2 : ℝ) ^ p.T (p.lev f))
      (((p.j f : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev f)) := by
    refine ⟨le_rfl, ?_⟩
    rw [← hend]
    exact le_add_of_nonneg_right (by dsimp only [qDeep]; positivity)
  let center := p.fineAnchorPosition b f startDeep
  let anchor : Fin 3 → ℝ := ![(startDeep - startOld) / qOld, center 0, center 1]
  refine ⟨anchor, ?_⟩
  intro x hx j
  rcases hp.2.2.2.2.2.2.2 f with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hF, _⟩
  have hxl : x.1 ∈ p.A f := (hF x hx).2.1
  have hxt : x.2 ∈ Icc ((p.j f : ℝ) / (2 : ℝ) ^ p.T (p.lev f))
      (((p.j f : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev f)) := (hF x hx).2.2.1
  have htime : startDeep ≤ x.2 ∧ x.2 ≤ startDeep + qDeep := by
    exact ⟨hxt.1, by rw [hend]; exact hxt.2⟩
  let α := (x.2 - startDeep) / qOld
  have hαnonneg : 0 ≤ α := div_nonneg (by linarith [htime.1]) hqOld.le
  have hα : |α| ≤ ratio := by
    rw [abs_of_nonneg hαnonneg]
    exact (div_le_div_of_nonneg_right (by linarith [htime.2]) hqOld.le).trans_eq hratioEq
  have hvel : ‖packetVelocity qOld (p.Q b) (p.u b) x.1‖ ≤ 2 * p.κ := by
    simpa only [packetVelocity, v, Submission.Lib.K4XInterface.gv] using
      hp.normalized_velocity_bound b x.1 (hA hxl)
  have hposition : packetPosition (p.Q b) (p.c b) (p.u b) x.1 x.2 =
      packetPosition (p.Q b) (p.c b) (p.u b) x.1 startDeep +
        α • packetVelocity qOld (p.Q b) (p.u b) x.1 := by
    have ht : startDeep + qOld * α = x.2 := by dsimp only [α]; field_simp; ring
    rw [← ht, packetPosition_affine]
  have hanchor := hp.fine_anchor_position_bound hN b f x.1 hxl startDeep htStart
  have hspatial : ‖packetPosition (p.Q b) (p.c b) (p.u b) x.1 x.2 - center‖ ≤
      (p.κ ^ 3 * Nk ^ (2 * δ₀ * L) + 2 * p.κ) * ratio := by
    calc
      _ = ‖(packetPosition (p.Q b) (p.c b) (p.u b) x.1 x.2 -
          packetPosition (p.Q b) (p.c b) (p.u b) x.1 startDeep) +
          (packetPosition (p.Q b) (p.c b) (p.u b) x.1 startDeep - center)‖ := by congr 1; abel
      _ ≤ ‖packetPosition (p.Q b) (p.c b) (p.u b) x.1 x.2 -
          packetPosition (p.Q b) (p.c b) (p.u b) x.1 startDeep‖ +
          ‖packetPosition (p.Q b) (p.c b) (p.u b) x.1 startDeep - center‖ := norm_add_le _ _
      _ = |α| * ‖packetVelocity qOld (p.Q b) (p.u b) x.1‖ +
          ‖packetPosition (p.Q b) (p.c b) (p.u b) x.1 startDeep - center‖ := by
        rw [hposition]
        simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      _ ≤ ratio * (2 * p.κ) + p.κ ^ 3 * Nk ^ (2 * δ₀ * L) * ratio :=
        add_le_add (mul_le_mul hα hvel (norm_nonneg _) hratio) hanchor
      _ = _ := by ring
  have hnonneg : 0 ≤ p.κ ^ 3 * Nk ^ (2 * δ₀ * L) + 2 * p.κ := by positivity
  have htimeR : ratio ≤ R := by
    dsimp only [R]
    nlinarith [mul_nonneg hnonneg hratio]
  have hspatialR : (p.κ ^ 3 * Nk ^ (2 * δ₀ * L) + 2 * p.κ) * ratio ≤ R := by
    dsimp only [R]
    nlinarith
  have htcoord : |(x.2 - startOld) / qOld - (startDeep - startOld) / qOld| ≤ R := by
    have heq : (x.2 - startOld) / qOld - (startDeep - startOld) / qOld = α := by dsimp only [α]; ring
    rw [heq]
    exact hα.trans htimeR
  have hcoord (k : Fin 2) :
      |packetPosition (p.Q b) (p.c b) (p.u b) x.1 x.2 k - center k| ≤ R := by
    calc
      _ ≤ ‖packetPosition (p.Q b) (p.c b) (p.u b) x.1 x.2 - center‖ := by
        simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
          (PiLp.norm_apply_le (packetPosition (p.Q b) (p.c b) (p.u b) x.1 x.2 - center) k)
      _ ≤ R := hspatial.trans hspatialR
  fin_cases j
  · exact htcoord
  · exact hcoord 0
  · exact hcoord 1

theorem PathData.Valid.exists_deep_base_code_menu
    (hp : p.Valid Nk L ω ν E B profile κ₁ m s δ₀ Mp Dp σ) (hN : 1 ≤ Nk)
    (b f : Fin p.C) (hA : p.A f ⊆ p.A b) {mesh : ℝ} (hmesh : 0 < mesh)
    (hsmall : (1 + p.κ ^ 3 * Nk ^ (2 * δ₀ * L) + 2 * p.κ) *
      ((2 : ℝ) ^ p.T (p.lev b) / (2 : ℝ) ^ p.T (p.lev f)) ≤ mesh) :
    ∃ Menu : Finset (Fin 3 → ℤ), Menu.card = 27 ∧
      ∀ x ∈ p.F f, (fun j => ⌊p.nativeBaseCoordinates b x j / mesh⌋) ∈ Menu := by
  obtain ⟨anchor, hanchor⟩ := hp.deep_original_base_box hN b f hA
  let Menu := integerCodeBox 1 (fun j => ⌊anchor j / mesh⌋)
  refine ⟨Menu, by simp only [Menu, card_integerCodeBox]; norm_num, ?_⟩
  intro x hx
  apply floor_code_mem_integerCodeBox 1 (p.nativeBaseCoordinates b x) anchor (fun _ => mesh)
    (fun _ => hmesh)
  intro j
  simpa only [Nat.cast_one, one_mul] using (hanchor x hx j).trans hsmall

theorem PathData.Valid.exists_deep_base_code_menu_of_path_powers
    (hp : p.Valid Nk L ω ν E B profile κ₁ m s δ₀ Mp Dp σ) (hN : 1 ≤ Nk)
    (b f : Fin p.C) (hA : p.A f ⊆ p.A b) (hδL : 0 ≤ δ₀ * L)
    {sourcePower slack meshExponent : ℝ} (hκpower : p.κ ≤ Nk ^ sourcePower)
    (hfour : 4 ≤ Nk ^ slack)
    (hgap : meshExponent + 3 * sourcePower + slack + 4 * δ₀ * L ≤
      κ₁ * (s (p.lev f) - s (p.lev b)) * L) :
    ∃ Menu : Finset (Fin 3 → ℤ), Menu.card = 27 ∧
      ∀ x ∈ p.F f, (fun j => ⌊p.nativeBaseCoordinates b x j / Nk ^ (-meshExponent)⌋) ∈ Menu := by
  have hb : p.lev b < m := (hp.2.2.2.2.2.2.2 b).1
  have hf : p.lev f < m := (hp.2.2.2.2.2.2.2 f).1
  apply hp.exists_deep_base_code_menu hN b f hA (Real.rpow_pos_of_pos (zero_lt_one.trans_le hN) _)
  exact native_deep_base_scale_bound hN hp.1 hδL
    (hp.2.2.2.2.1 (p.lev b) hb).2.2.2.1 (hp.2.2.2.2.1 (p.lev f) hf).2.2.1
    hκpower hfour hgap

end Path

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
