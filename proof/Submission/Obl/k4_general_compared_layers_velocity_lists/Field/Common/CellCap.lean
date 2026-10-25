-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Common.CellCap; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254 (k4_general_parent_wide_layer_candidates), session x0900.
   The moving-slab integration is `measure_resolved_moving_slab` of accepted o248
   (`k4_wide_velocity_lists_scalar_preparation/ResidualCaps.lean`), used as is. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Common.Quadratic
import Submission.Obl.k4_general_compared_layers_velocity_lists.Lists.Geometry
import Submission.Obl.k4_wide_velocity_lists_scalar_preparation.ResidualCaps

/-!
# Normalized base cells of an original block, on native-signal groups

Inside one original block `Q`, cut a normalized base cell `(τ, ζ)` of side `δ` into transverse
slabs of normalized width `δU`. If on each of two groups the native signal varies by at most
`Δ` between incidences whose base points differ by at most `(K + 1)^2 q δ + w δU`, every slab
of one group lies in a moving box carrying at most seven native-signal bins of width `Δ` per
fine base cell, and the fine original caps integrate to the volume of the slab. Summing over
the slabs and the two groups gives the original mass of the cell on the groups.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4MovingMeshBoxes (movingBox)
open Submission.Obl.k4_wide_velocity_lists_scalar_preparation (measure_resolved_moving_slab)

noncomputable section

namespace FieldCommon

theorem floor_cell {a δ : ℝ} {n : ℤ} (hδ : 0 < δ) (h : ⌊a / δ⌋ = n) :
    (n : ℝ) * δ ≤ a ∧ a < ((n : ℝ) + 1) * δ := by
  have hlo := (le_div_iff₀ hδ).mp (Int.floor_le (a / δ))
  have hhi := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (a / δ))
  rw [h] at hlo hhi
  exact ⟨hlo, hhi⟩

theorem abs_sub_floor_cell {a δ : ℝ} {n : ℤ} (hδ : 0 < δ) (h : ⌊a / δ⌋ = n) :
    |a - (n : ℝ) * δ| ≤ δ := by
  obtain ⟨hlo, hhi⟩ := floor_cell hδ h
  rw [abs_le]
  constructor <;> nlinarith

theorem abs_sub_of_floor_eq {a a' δ : ℝ} {n : ℤ} (hδ : 0 < δ) (h : ⌊a / δ⌋ = n)
    (h' : ⌊a' / δ⌋ = n) : |a - a'| ≤ δ := by
  obtain ⟨hlo, hhi⟩ := floor_cell hδ h
  obtain ⟨hlo', hhi'⟩ := floor_cell hδ h'
  rw [abs_le]
  constructor <;> nlinarith

theorem floor_mem_Icc {a M δ : ℝ} (hδ : 0 < δ) (ha : |a| ≤ M) :
    ⌊a / δ⌋ ∈ Finset.Icc ⌊-M / δ⌋ ⌊M / δ⌋ := by
  rw [Finset.mem_Icc]
  rw [abs_le] at ha
  constructor
  · apply Int.floor_le_floor
    exact div_le_div_of_nonneg_right ha.1 hδ.le
  · apply Int.floor_le_floor
    exact div_le_div_of_nonneg_right ha.2 hδ.le

theorem card_floor_Icc_le {M δ : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) :
    ((Finset.Icc ⌊-M / δ⌋ ⌊M / δ⌋).card : ℝ) ≤ 2 * M / δ + 2 := by
  rw [Int.card_Icc]
  have h1 : (⌊-M / δ⌋ : ℝ) > -M / δ - 1 := by
    have := Int.lt_floor_add_one (-M / δ)
    linarith
  have h2 : (⌊M / δ⌋ : ℝ) ≤ M / δ := Int.floor_le _
  have hMδ : 0 ≤ M / δ := div_nonneg hM hδ.le
  have hnn : 0 ≤ ⌊M / δ⌋ + 1 - ⌊-M / δ⌋ := by
    have : ⌊-M / δ⌋ ≤ ⌊M / δ⌋ := Int.floor_le_floor (by
      have : -M / δ ≤ M / δ := by rw [neg_div]; linarith
      exact this)
    omega
  have hcast : ((⌊M / δ⌋ + 1 - ⌊-M / δ⌋).toNat : ℝ) =
      ((⌊M / δ⌋ + 1 - ⌊-M / δ⌋ : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
  rw [hcast]
  push_cast
  have hneg : -M / δ = -(M / δ) := neg_div _ _
  have : 2 * M / δ = 2 * (M / δ) := by ring
  rw [this]
  linarith

end FieldCommon

namespace Parent

variable {α : Type} [MeasurableSpace α] {p : Parent α}

/-- The fine base point `(t, x₁, x₂)` of an incidence. -/
def finePoint (p : Parent α) (k : ℕ) (ω : α × ℝ) : Fin 3 → ℝ :=
  ![ω.2, p.x k ω.1 ω.2 1, p.x k ω.1 ω.2 2]

theorem finePoint_eq_base (p : Parent α) (k : ℕ) (ω : α × ℝ) (c : Fin 3) :
    p.finePoint k ω c = p.base k ω.1 ω.2 c := by
  fin_cases c <;> rfl

/-- **Original mass of a normalized base cell on two native-signal groups.** -/
theorem group_cell_cap (h : p.Valid) {k : ℕ} {r : ℝ} (a : ParentGeometry p k r)
    (Q : Fin (p.n k r)) {E : Fin 2 → Set (α × ℝ)}
    (hEsub : ∀ e, E e ⊆ p.B k r Q ×ˢ block (p.T k r) (p.j k r Q))
    {δ δU δf Δ : ℝ} (hδ : 0 < δ) (hδU : 0 < δU) (hδf : 0 < δf) (hΔ : 0 < Δ)
    (hosc : ∀ e, ∀ z ∈ E e, ∀ z' ∈ E e,
      (∀ c : Fin 3, |p.base k z.1 z.2 c - p.base k z'.1 z'.2 c| ≤
        (p.K k + 1) ^ 2 * p.blockLen k r * δ + p.blockWidth k r * δU) →
      |p.signal k z.1 z.2 - p.signal k z'.1 z'.2| ≤ Δ)
    (hcap : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      p.μ k {ω | (fun i => ⌊p.finePoint k ω i / δf⌋) = q ∧
        ⌊p.signal k ω.1 ω.2 / Δ⌋ = j} ≤ ENNReal.ofReal (p.K k * Δ ^ p.d * δf ^ 3))
    (hfine1 : (p.K k + p.K k ^ 2) * δf ≤ p.blockLen k r * δ)
    (hfine2 : (p.K k + p.K k ^ 2) * δf ≤ p.blockWidth k r * δU)
    (q0 q1 : ℤ) :
    p.μ k ({ω | ⌊p.tauN k r Q ω / δ⌋ = q0 ∧ ⌊p.zetaN k r Q ω / δ⌋ = q1} ∩ ⋃ e, E e) ≤
      ENNReal.ofReal ((2 * p.K k / δU + 2) * 2 * (4200 * (p.K k * Δ ^ p.d) *
        (p.blockLen k r * δ) * (p.blockLen k r * δ) *
        (p.K k * p.blockLen k r * δ + p.blockWidth k r * δU))) := by
  classical
  set K := p.K k with hKdef
  set q := p.blockLen k r with hqdef
  set w := p.blockWidth k r with hwdef
  set t₀ := p.blockStart k r Q with ht₀def
  set c := p.c k r Q with hcdef
  have hK : 1 ≤ K := h.subpower.1 k
  have hK0 : 0 ≤ K := by linarith
  have hN : 0 < p.N k := by linarith [h.scale k]
  have hq : 0 < q := p.common_blockLen_pos k r
  have hg : 0 < p.N k ^ (-p.ℓ * r) := Real.rpow_pos_of_pos hN _
  have hw : 0 < w := mul_pos hq hg
  have hcK : ∀ e, |c e| ≤ K := a.coefficient_bound Q
  have hL0 : 0 ≤ K + K ^ 2 := by positivity
  have hL1 : 1 ≤ K + K ^ 2 := by nlinarith
  have hΔd : 0 ≤ Δ ^ p.d := Real.rpow_nonneg hΔ.le _
  -- the transverse coordinate is bounded on the block
  have hUbound : ∀ ω ∈ p.B k r Q ×ˢ block (p.T k r) (p.j k r Q), |p.uN k r Q ω| ≤ K := by
    intro ω hω
    have htr := a.transverse Q ω.1 (a.fitted_subset Q hω.1) ω.2 hω.2
    unfold uN tiltY
    rw [abs_div, abs_of_pos hw, div_le_iff₀ hw]
    have he : p.x k ω.1 ω.2 2 - (p.c k r Q 2 + p.c k r Q 3 * ω.2 +
        p.c k r Q 4 * p.x k ω.1 ω.2 1) =
        p.x k ω.1 ω.2 2 - p.c k r Q 2 - ω.2 * p.c k r Q 3 -
          p.c k r Q 4 * p.x k ω.1 ω.2 1 := by ring
    rw [he]
    calc _ ≤ p.K k * ((2 : ℝ) ^ p.T k r)⁻¹ * p.N k ^ (-p.ℓ * r) := htr
      _ = K * w := by rw [hwdef]; unfold blockWidth blockLen; ring
  -- the cut into transverse slabs and groups
  set cell : Set (α × ℝ) :=
    {ω | ⌊p.tauN k r Q ω / δ⌋ = q0 ∧ ⌊p.zetaN k r Q ω / δ⌋ = q1} with hcell
  let piece : ℤ → Fin 2 → Set (α × ℝ) := fun u0 e =>
    (cell ∩ E e) ∩ {ω | ⌊p.uN k r Q ω / δU⌋ = u0}
  set U : Finset ℤ := Finset.Icc ⌊-K / δU⌋ ⌊K / δU⌋ with hUdef
  have hcover : cell ∩ ⋃ e, E e ⊆ ⋃ u0 ∈ U, ⋃ e ∈ (Finset.univ : Finset (Fin 2)), piece u0 e := by
    intro ω hω
    obtain ⟨hωc, hωE⟩ := hω
    obtain ⟨e, he⟩ := mem_iUnion.mp hωE
    have hU := FieldCommon.floor_mem_Icc hδU (hUbound ω (hEsub e he))
    exact mem_iUnion₂.mpr ⟨_, hU, mem_iUnion₂.mpr ⟨e, Finset.mem_univ _, ⟨hωc, he⟩, rfl⟩⟩
  -- one slab of one group
  set B : ℝ := 4200 * (K * Δ ^ p.d) * (q * δ) * (q * δ) * (K * q * δ + w * δU) with hBdef
  have hpiece : ∀ u0 e, p.μ k (piece u0 e) ≤ ENNReal.ofReal B := by
    intro u0 e
    by_cases hne : (piece u0 e).Nonempty
    swap
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty]
      exact bot_le
    obtain ⟨ω₀, hω₀⟩ := hne
    -- normalized coordinates of a slab point
    have hcoord : ∀ ω ∈ piece u0 e,
        |ω.2 - (t₀ + q * ((q0 : ℝ) * δ))| ≤ q * δ ∧
        |p.x k ω.1 ω.2 1 - ((c 0 + q * ((q1 : ℝ) * δ)) + ω.2 * c 1)| ≤ q * δ ∧
        |p.x k ω.1 ω.2 2 - ((c 2 + c 4 * (c 0 + q * ((q1 : ℝ) * δ)) + w * ((u0 : ℝ) * δU)) +
          ω.2 * (c 3 + c 4 * c 1))| ≤ K * q * δ + w * δU := by
      intro ω hω
      obtain ⟨⟨⟨hτ, hζ⟩, -⟩, hu⟩ := hω
      have hτ' := FieldCommon.abs_sub_floor_cell hδ hτ
      have hζ' := FieldCommon.abs_sub_floor_cell hδ hζ
      have hu' := FieldCommon.abs_sub_floor_cell hδU hu
      have htime : ω.2 = t₀ + q * p.tauN k r Q ω := by
        unfold tauN
        rw [← hqdef, ← ht₀def]
        field_simp
        ring
      have hmajor : p.x k ω.1 ω.2 1 = c 0 + c 1 * ω.2 + q * p.zetaN k r Q ω := by
        unfold zetaN
        rw [← hqdef, ← hcdef]
        field_simp
        ring
      have htrans : p.x k ω.1 ω.2 2 = c 2 + c 3 * ω.2 + c 4 * p.x k ω.1 ω.2 1 +
          w * p.uN k r Q ω := by
        unfold uN tiltY
        rw [← hwdef, ← hcdef]
        field_simp
        ring
      refine ⟨?_, ?_, ?_⟩
      · rw [htime]
        calc |t₀ + q * p.tauN k r Q ω - (t₀ + q * ((q0 : ℝ) * δ))| =
              |q * (p.tauN k r Q ω - (q0 : ℝ) * δ)| := by ring_nf
          _ = q * |p.tauN k r Q ω - (q0 : ℝ) * δ| := by rw [abs_mul, abs_of_pos hq]
          _ ≤ q * δ := mul_le_mul_of_nonneg_left hτ' hq.le
      · rw [hmajor]
        calc |c 0 + c 1 * ω.2 + q * p.zetaN k r Q ω - ((c 0 + q * ((q1 : ℝ) * δ)) + ω.2 * c 1)| =
              |q * (p.zetaN k r Q ω - (q1 : ℝ) * δ)| := by ring_nf
          _ = q * |p.zetaN k r Q ω - (q1 : ℝ) * δ| := by rw [abs_mul, abs_of_pos hq]
          _ ≤ q * δ := mul_le_mul_of_nonneg_left hζ' hq.le
      · rw [htrans, hmajor]
        have he : c 2 + c 3 * ω.2 + c 4 * (c 0 + c 1 * ω.2 + q * p.zetaN k r Q ω) +
            w * p.uN k r Q ω - ((c 2 + c 4 * (c 0 + q * ((q1 : ℝ) * δ)) +
              w * ((u0 : ℝ) * δU)) + ω.2 * (c 3 + c 4 * c 1)) =
            c 4 * (q * (p.zetaN k r Q ω - (q1 : ℝ) * δ)) +
              w * (p.uN k r Q ω - (u0 : ℝ) * δU) := by ring
        rw [he]
        calc _ ≤ |c 4 * (q * (p.zetaN k r Q ω - (q1 : ℝ) * δ))| +
              |w * (p.uN k r Q ω - (u0 : ℝ) * δU)| := abs_add_le _ _
          _ = |c 4| * (q * |p.zetaN k r Q ω - (q1 : ℝ) * δ|) +
              w * |p.uN k r Q ω - (u0 : ℝ) * δU| := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_pos hq, abs_of_pos hw]
          _ ≤ K * (q * δ) + w * δU := by
              gcongr
              · exact hcK 4
          _ = K * q * δ + w * δU := by ring
    -- base distances inside one slab
    have hdist : ∀ ω ∈ piece u0 e, ∀ c' : Fin 3,
        |p.base k ω.1 ω.2 c' - p.base k ω₀.1 ω₀.2 c'| ≤ (K + 1) ^ 2 * q * δ + w * δU := by
      intro ω hω
      obtain ⟨⟨⟨hτ, hζ⟩, -⟩, hu⟩ := hω
      obtain ⟨⟨⟨hτ₀, hζ₀⟩, -⟩, hu₀⟩ := hω₀
      have dτ := FieldCommon.abs_sub_of_floor_eq hδ hτ hτ₀
      have dζ := FieldCommon.abs_sub_of_floor_eq hδ hζ hζ₀
      have du := FieldCommon.abs_sub_of_floor_eq hδU hu hu₀
      have htime : ∀ ω' : α × ℝ, ω'.2 = t₀ + q * p.tauN k r Q ω' := by
        intro ω'
        unfold tauN
        rw [← hqdef, ← ht₀def]
        field_simp
        ring
      have hmajor : ∀ ω' : α × ℝ,
          p.x k ω'.1 ω'.2 1 = c 0 + c 1 * ω'.2 + q * p.zetaN k r Q ω' := by
        intro ω'
        unfold zetaN
        rw [← hqdef, ← hcdef]
        field_simp
        ring
      have htrans : ∀ ω' : α × ℝ, p.x k ω'.1 ω'.2 2 =
          c 2 + c 3 * ω'.2 + c 4 * p.x k ω'.1 ω'.2 1 + w * p.uN k r Q ω' := by
        intro ω'
        unfold uN tiltY
        rw [← hwdef, ← hcdef]
        field_simp
        ring
      have dt : |ω.2 - ω₀.2| ≤ q * δ := by
        rw [htime ω, htime ω₀]
        calc |t₀ + q * p.tauN k r Q ω - (t₀ + q * p.tauN k r Q ω₀)| =
              |q * (p.tauN k r Q ω - p.tauN k r Q ω₀)| := by ring_nf
          _ = q * |p.tauN k r Q ω - p.tauN k r Q ω₀| := by rw [abs_mul, abs_of_pos hq]
          _ ≤ q * δ := mul_le_mul_of_nonneg_left dτ hq.le
      have d1 : |p.x k ω.1 ω.2 1 - p.x k ω₀.1 ω₀.2 1| ≤ (K + 1) * q * δ := by
        rw [hmajor ω, hmajor ω₀]
        have he : c 0 + c 1 * ω.2 + q * p.zetaN k r Q ω -
            (c 0 + c 1 * ω₀.2 + q * p.zetaN k r Q ω₀) =
            c 1 * (ω.2 - ω₀.2) + q * (p.zetaN k r Q ω - p.zetaN k r Q ω₀) := by ring
        rw [he]
        calc _ ≤ |c 1 * (ω.2 - ω₀.2)| + |q * (p.zetaN k r Q ω - p.zetaN k r Q ω₀)| :=
              abs_add_le _ _
          _ = |c 1| * |ω.2 - ω₀.2| + q * |p.zetaN k r Q ω - p.zetaN k r Q ω₀| := by
              rw [abs_mul, abs_mul, abs_of_pos hq]
          _ ≤ K * (q * δ) + q * δ := by
              gcongr
              · exact hcK 1
          _ = (K + 1) * q * δ := by ring
      have d2 : |p.x k ω.1 ω.2 2 - p.x k ω₀.1 ω₀.2 2| ≤ (K + 1) ^ 2 * q * δ + w * δU := by
        rw [htrans ω, htrans ω₀]
        have he : c 2 + c 3 * ω.2 + c 4 * p.x k ω.1 ω.2 1 + w * p.uN k r Q ω -
            (c 2 + c 3 * ω₀.2 + c 4 * p.x k ω₀.1 ω₀.2 1 + w * p.uN k r Q ω₀) =
            c 3 * (ω.2 - ω₀.2) + c 4 * (p.x k ω.1 ω.2 1 - p.x k ω₀.1 ω₀.2 1) +
              w * (p.uN k r Q ω - p.uN k r Q ω₀) := by ring
        rw [he]
        calc _ ≤ |c 3 * (ω.2 - ω₀.2)| + |c 4 * (p.x k ω.1 ω.2 1 - p.x k ω₀.1 ω₀.2 1)| +
              |w * (p.uN k r Q ω - p.uN k r Q ω₀)| := by
              grw [abs_add_le, abs_add_le]
          _ = |c 3| * |ω.2 - ω₀.2| + |c 4| * |p.x k ω.1 ω.2 1 - p.x k ω₀.1 ω₀.2 1| +
              w * |p.uN k r Q ω - p.uN k r Q ω₀| := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_pos hw]
          _ ≤ K * (q * δ) + K * ((K + 1) * q * δ) + w * δU := by
              gcongr
              · exact hcK 3
              · exact hcK 4
          _ ≤ (K + 1) ^ 2 * q * δ + w * δU := by
              have : 0 ≤ q * δ := by positivity
              nlinarith
      have hpos : 0 ≤ q * δ := by positivity
      have hwpos : 0 ≤ w * δU := by positivity
      intro c'
      fin_cases c'
      · change |ω.2 - ω₀.2| ≤ _
        nlinarith
      · change |p.x k ω.1 ω.2 1 - p.x k ω₀.1 ω₀.2 1| ≤ _
        nlinarith
      · change |p.x k ω.1 ω.2 2 - p.x k ω₀.1 ω₀.2 2| ≤ _
        exact d2
    have hbound := measure_resolved_moving_slab (p.μ k) (p.finePoint k)
      (fun ω => p.signal k ω.1 ω.2) (fun _ => (0 : ℝ)) (fun _ => True) (piece u0 e)
      (δ := δf) (Δ := Δ) (radius := q * δ) (L := K + K ^ 2) (C := K * Δ ^ p.d)
      hδf hΔ (by nlinarith) hL0 (by positivity)
      (t₀ + q * ((q0 : ℝ) * δ)) (p.signal k ω₀.1 ω₀.2)
      ![c 0 + q * ((q1 : ℝ) * δ), c 2 + c 4 * (c 0 + q * ((q1 : ℝ) * δ)) + w * ((u0 : ℝ) * δU)]
      ![c 1, c 3 + c 4 * c 1] ![q * δ, K * q * δ + w * δU]
      (by
        intro i
        fin_cases i
        · change |c 1| ≤ K + K ^ 2
          nlinarith [hcK 1]
        · change |c 3 + c 4 * c 1| ≤ K + K ^ 2
          calc |c 3 + c 4 * c 1| ≤ |c 3| + |c 4| * |c 1| := by
                rw [← abs_mul]; exact abs_add_le _ _
            _ ≤ K + K * K := by
                gcongr
                · exact hcK 3
                · exact hcK 4
                · exact hcK 1
            _ = K + K ^ 2 := by ring)
      (by
        intro i
        fin_cases i
        · change δf ≤ q * δ
          nlinarith
        · change δf ≤ K * q * δ + w * δU
          have : 0 ≤ K * q * δ := by positivity
          nlinarith)
      (by
        intro i
        fin_cases i
        · exact hfine1
        · change (K + K ^ 2) * δf ≤ K * q * δ + w * δU
          have : 0 ≤ K * q * δ := by positivity
          linarith)
      (by
        intro ω hω
        obtain ⟨h0, h1, h2⟩ := hcoord ω hω
        refine ⟨h0, ?_⟩
        intro i
        fin_cases i
        · exact h1
        · exact h2)
      (fun _ _ => trivial)
      (by
        intro ω hω
        simp only [sub_zero]
        exact hosc e ω hω.1.2 ω₀ hω₀.1.2 (hdist ω hω))
      (by
        intro ω _ y _
        simp only [sub_self, abs_zero]
        exact hΔ.le)
      1
      (by
        intro qq j
        simp only [and_true, mul_one]
        calc p.μ k {ω | (fun i => ⌊p.finePoint k ω i / δf⌋) = qq ∧
              ⌊p.signal k ω.1 ω.2 / Δ⌋ = j} ≤ ENNReal.ofReal (K * Δ ^ p.d * δf ^ 3) :=
              hcap qq j
          _ = ENNReal.ofReal (K * Δ ^ p.d * δf ^ 3) := rfl)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one] at hbound
    rw [hBdef]
    exact hbound
  -- summing over slabs and groups
  have hcard := FieldCommon.card_floor_Icc_le hδU hK0
  have hB : 0 ≤ B := by positivity
  clear_value B
  have hsum : ∑ _u0 ∈ U, ∑ _e ∈ (Finset.univ : Finset (Fin 2)), ENNReal.ofReal B =
      ENNReal.ofReal ((U.card : ℝ) * 2 * B) := by
    rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      nsmul_eq_mul, show ((U.card : ℝ) * 2 * B) = (U.card : ℝ) * (2 * B) by ring,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_natCast]
    norm_num
  calc p.μ k (cell ∩ ⋃ e, E e) ≤
        p.μ k (⋃ u0 ∈ U, ⋃ e ∈ (Finset.univ : Finset (Fin 2)), piece u0 e) := measure_mono hcover
    _ ≤ ∑ u0 ∈ U, p.μ k (⋃ e ∈ (Finset.univ : Finset (Fin 2)), piece u0 e) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ u0 ∈ U, ∑ e ∈ (Finset.univ : Finset (Fin 2)), p.μ k (piece u0 e) :=
        Finset.sum_le_sum (fun u0 _ => measure_biUnion_finset_le _ _)
    _ ≤ ∑ _u0 ∈ U, ∑ _e ∈ (Finset.univ : Finset (Fin 2)), ENNReal.ofReal B :=
        Finset.sum_le_sum (fun u0 _ => Finset.sum_le_sum (fun e _ => hpiece u0 e))
    _ = ENNReal.ofReal ((U.card : ℝ) * 2 * B) := hsum
    _ ≤ ENNReal.ofReal ((2 * K / δU + 2) * 2 * B) := by
        apply ENNReal.ofReal_le_ofReal
        gcongr

end Parent

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
