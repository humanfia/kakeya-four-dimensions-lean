-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.PacketData.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Containers
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.DyadicPrisms
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Greedy

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open Module MeasureTheory Set Metric
open scoped ENNReal

abbrev PhysicalPacket (n : ℕ) := ShadedCell (Fin n)

def PhysicalPacket.Valid {n : ℕ} (C : PhysicalPacket n) (δ d : ℝ)
    (x v : Fin n → E) (Y : Fin n → Set E) : Prop :=
  C.indices.Nonempty ∧ IsCompact C.region ∧ Convex ℝ C.region ∧
  C.region ⊆ closedBall (0 : E) 1 ∧
  (∀ i ∈ C.indices, closedTube δ (x i) (v i) ⊆ C.region) ∧
  (∀ i ∈ C.indices, MeasurableSet (C.shading i)) ∧
  (∀ i ∈ C.indices, C.shading i ⊆ Y i) ∧
  (∀ i ∈ C.indices, C.shading i ⊆ closedTube δ (x i) (v i)) ∧
  (∀ i ∈ C.indices, ENNReal.ofReal d * volume (closedTube δ (x i) (v i)) ≤ volume (C.shading i))

lemma PhysicalPacket.Valid.support_subset {n : ℕ} {C : PhysicalPacket n} {δ d : ℝ}
    {x v : Fin n → E} {Y : Fin n → Set E} (hC : C.Valid δ d x v Y) :
    C.support ⊆ C.region := by
  intro p hp
  obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp hp
  exact hC.2.2.2.2.1 i hi (hC.2.2.2.2.2.2.2.1 i hi hpi)

lemma PhysicalPacket.Valid.mono_density {n : ℕ} {C : PhysicalPacket n} {δ d d' : ℝ}
    {x v : Fin n → E} {Y : Fin n → Set E} (hC : C.Valid δ d x v Y) (hdd' : d' ≤ d) :
    C.Valid δ d' x v Y := by
  obtain ⟨hne, hc, hconv, hbound, hwhole, hm, hsub, hbody, hd⟩ := hC
  exact ⟨hne, hc, hconv, hbound, hwhole, hm, hsub, hbody, fun i hi =>
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal hdd') _).trans (hd i hi)⟩

/-- A terminal affine cell, with its dyadic shape recorded for final pigeonholing. -/
structure AffineCell (n K : ℕ) where
  indices : Finset (Fin n)
  first : Fin (K + 1)
  second : Fin (K + 1)
  affine : E ≃ᵃ[ℝ] E
  jacobian : ℝ
  center : Fin n → E
  axes : Fin n → OrthonormalBasis (Fin 3) ℝ E
  shading : Fin n → Set E

noncomputable def AffineCell.a {n K : ℕ} (C : AffineCell n K) : ℝ := (1 / 2 : ℝ) ^ C.first.val
noncomputable def AffineCell.b {n K : ℕ} (C : AffineCell n K) : ℝ := (1 / 2 : ℝ) ^ C.second.val
def AffineCell.body {n K : ℕ} (C : AffineCell n K) (i : Fin n) : Set E :=
  prism C.a C.b (C.center i) (C.axes i)
def AffineCell.support {n K : ℕ} (C : AffineCell n K) : Set E :=
  C.affine '' (⋃ i ∈ C.indices, C.shading i)

def AffineCell.Valid {n K : ℕ} (C : AffineCell n K) (δ h : ℝ)
    (x v : Fin n → E) (Y : Fin n → Set E) : Prop :=
  C.indices.Nonempty ∧ δ ^ (100 : ℕ) ≤ C.a ∧ C.a ≤ C.b ∧ C.b ≤ 1 / 1000000 ∧
  δ * h ≤ C.b ∧ δ ^ (100 : ℕ) ≤ C.jacobian ∧ C.jacobian ≤ δ ^ (-100 : ℝ) ∧
  (∀ Q : Set E, volume (C.affine '' Q) = ENNReal.ofReal C.jacobian * volume Q) ∧
  (∀ i ∈ C.indices, C.body i ⊆ ball (0 : E) (1 / 100)) ∧
  (∀ i ∈ C.indices, tube δ (x i) (v i) ⊆ C.affine '' C.body i) ∧
  (∀ i ∈ C.indices, MeasurableSet (C.shading i)) ∧
  (∀ i ∈ C.indices, C.shading i ⊆ C.body i ∩ C.affine ⁻¹' Y i) ∧
  (∀ i ∈ C.indices, ENNReal.ofReal h * volume (C.body i) ≤ volume (C.shading i)) ∧
  (∀ i ∈ C.indices, ∀ p ∈ C.shading i, ∀ r : ℝ, C.a ≤ r → r ≤ 1 →
    ENNReal.ofReal h * volume (C.body i ∩ ball p r) ≤ volume (C.shading i ∩ ball p r)) ∧
  (∀ p, (∃ i ∈ C.indices, p ∈ C.shading i) → ∃ i ∈ C.indices, ∃ j ∈ C.indices,
    p ∈ C.shading i ∧ p ∈ C.shading j ∧
      h ≤ C.a / C.b + min ‖C.axes i 0 - C.axes j 0‖ ‖C.axes i 0 + C.axes j 0‖) ∧
  (∀ (ν : E) (s r : ℝ), ‖ν‖ = 1 → 0 < r →
    ENNReal.ofReal (Set.ncard {i : Fin n | i ∈ C.indices ∧ C.body i ⊆
      ball (0 : E) 1 ∩ slab (innerSL ℝ ν) s r} : ℝ) ≤
    ENNReal.ofReal (h⁻¹ * (C.indices.card : ℝ)) *
      volume (ball (0 : E) 1 ∩ slab (innerSL ℝ ν) s r))

lemma affine_preimage_density (f : E ≃ᵃ[ℝ] E) {D : ℝ} (hD : 0 < D)
    (hf : ∀ Q : Set E, volume (f '' Q) = ENNReal.ofReal D * volume Q)
    {U Y : Set E} (d : ℝ≥0∞) (hd : d * volume U ≤ volume Y) :
    d * volume (f ⁻¹' U) ≤ volume (f ⁻¹' Y) := by
  apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hD).ne' ENNReal.ofReal_ne_top).mp
  have hU := hf (f ⁻¹' U)
  have hY := hf (f ⁻¹' Y)
  rw [image_preimage_eq _ f.surjective] at hU hY
  calc ENNReal.ofReal D * (d * volume (f ⁻¹' U))
      = d * volume U := by rw [mul_left_comm, ← hU]
    _ ≤ volume Y := hd
    _ = _ := hY

lemma affine_preimage_weights (f : E ≃ᵃ[ℝ] E) {D : ℝ} (hD : 0 < D)
    (hf : ∀ Q : Set E, volume (f '' Q) = ENNReal.ofReal D * volume Q)
    {U : Set E} (hUc : IsCompact U) {w C : ℝ} (hw : 0 ≤ w) (hC : 0 ≤ C)
    (hvol : ENNReal.ofReal w ≤ volume U ∧ volume U ≤ ENNReal.ofReal (C * w)) :
    w / D ≤ (volume (f ⁻¹' U)).toReal ∧ (volume (f ⁻¹' U)).toReal ≤ C * (w / D) := by
  have he := hf (f ⁻¹' U)
  rw [image_preimage_eq _ f.surjective] at he
  have her : (volume U).toReal = D * (volume (f ⁻¹' U)).toReal := by
    rw [he, ENNReal.toReal_mul, ENNReal.toReal_ofReal hD.le]
  have hlo := ENNReal.toReal_mono hUc.measure_ne_top hvol.1
  rw [ENNReal.toReal_ofReal hw, her] at hlo
  have hhi := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol.2
  rw [ENNReal.toReal_ofReal (mul_nonneg hC hw), her] at hhi
  constructor
  · rw [div_le_iff₀ hD]
    nlinarith
  · rw [← mul_div_assoc, le_div_iff₀ hD]
    nlinarith

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
