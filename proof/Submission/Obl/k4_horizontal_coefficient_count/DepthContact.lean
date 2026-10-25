import Submission.Obl.k4_horizontal_coefficient_count.DepthGeometry
import Submission.Obl.k4_horizontal_coefficient_count.ContactCap

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set
open scoped ENNReal BigOperators
open Submission.Obl.k4_critical_switching_state_preparation.Inherited

noncomputable section
namespace DepthData

variable {α : Type} [MeasurableSpace α] {D : DepthData α} (h : D.Hyp)

omit h in
def basePoint (D : DepthData α) (p : α × ℝ) : Fin 3 → ℝ :=
  ![p.2, X1 (D.b p.1) p.2, X2 (D.b p.1) p.2]

omit h in
def MeetsGroup (D : DepthData α) (g : ℤ × ℤ × ℤ) (i : Fin D.n) : Prop :=
  ∃ l ∈ D.B i, l ∈ groupSet D.b D.χ D.a g ∩ goodSet D.b D.K D.χ

include h

theorem Hyp.enlarged_true_box (i : Fin D.n) {l : α} (hl : l ∈ D.B i)
    {t : ℝ} (ht : t ∈ tblock D.q (D.j i)) :
    D.basePoint (l, t) ∈ horizontalTrueBox (D.c i) (D.midpoint (D.j i))
      (D.K * D.q) (8 * D.K ^ 2) := by
  exact h.enlarged_true_bounds i hl ht

/-- One good trajectory locates every complete incidence witness of its label. -/
theorem Hyp.group_contact_box {g : ℤ × ℤ × ℤ} {i : Fin D.n}
    (hi : D.MeetsGroup g i) (hsmall : D.K * D.q ≤ 1) :
    ∀ p ∈ D.B i ×ˢ tblock D.q (D.j i),
      D.basePoint p ∈ contactOuterBox (D.midpoint (D.j i)) (D.groupReference g)
        (D.K * D.q) (8 * (8 * D.K ^ 2) * (D.K * D.q))
        (32 * (8 * D.K ^ 2) ^ 2 * (D.K * D.q) ^ 2) := by
  obtain ⟨l, hlB, hg, hl⟩ := hi
  have hK0 : 0 ≤ D.K := by linarith [h.hK]
  have hK1 : 0 < D.K := by linarith [h.hK]
  have hq := h.q_pos
  have hH : 0 < D.K * D.q := mul_pos hK1 hq
  have hG : 1 ≤ 8 * D.K ^ 2 := by nlinarith [h.hK]
  have hKG : D.K ≤ 8 * D.K ^ 2 := by nlinarith [h.hK]
  have h2KG : 2 * D.K ≤ 8 * D.K ^ 2 := by nlinarith [h.hK]
  have h3G : 3 ≤ 8 * D.K ^ 2 := by nlinarith [h.hK]
  have hm := h.midpoint_abs_le_one (D.j i)
  have hmid : D.midpoint (D.j i) ∈ tblock D.q (D.j i) := by
    dsimp [midpoint, tblock]
    constructor <;> nlinarith
  have hunit := h.block_subset_unit (D.j i) hmid
  obtain ⟨hp, hv⟩ := h.reference_coefficient_bounds g hg hl
  have hgap := h.group_reference_errors g hg hl hunit
  obtain ⟨hcenter, htilt⟩ := h.enlarged_center_tilt i
  have haH := h.a_le_enlarged_square
  have hcZ : |D.basePoint (l, D.midpoint (D.j i)) 1 -
      referenceZ (D.groupReference g) (D.basePoint (l, D.midpoint (D.j i)) 0)| ≤
      (8 * D.K ^ 2) * D.a :=
    hgap.1.trans (by nlinarith [mul_le_mul_of_nonneg_right h3G h.ha0.le, h.ha0])
  have hcY : |D.basePoint (l, D.midpoint (D.j i)) 2 -
      referenceY (D.groupReference g) (D.basePoint (l, D.midpoint (D.j i)) 0)| ≤
      (8 * D.K ^ 2) * D.a :=
    hgap.2.trans (mul_le_mul_of_nonneg_right h3G h.ha0.le)
  have hwhole := horizontalTrueBox_common_contact (D.c i) (D.groupReference g)
    (D.basePoint (l, D.midpoint (D.j i))) (D.midpoint (D.j i)) (D.K * D.q)
    (8 * D.K ^ 2) D.a hH hsmall hG haH hm ((h.hc i 1).trans hKG)
    (hv.trans h2KG) hcenter htilt (h.enlarged_true_box i hlB hmid) hcZ hcY
  intro p hp'
  obtain ⟨hZ, hY⟩ := hwhole (D.basePoint p) (h.enlarged_true_box i hp'.1 hp'.2)
  rw [mem_contactOuterBox_iff]
  exact ⟨(h.block_time_gap _ hp'.2).trans (by nlinarith [h.hK]), hZ, hY⟩

/-- The fine base cap is unchanged when its three integer indices are bundled. -/
theorem Hyp.base_cell_cap (v : Fin 3 → ℤ) :
    D.μ {p | (fun e => ⌊D.basePoint p e / D.w⌋) = v} ≤
      ENNReal.ofReal ((4 * D.K ^ 2) * D.w ^ 3) := by
  apply le_trans (measure_mono ?_) (h.cap0 (v 0) (v 1) (v 2))
  intro p hp
  exact ⟨congrFun hp 0, congrFun hp 1, congrFun hp 2⟩

/-- The original whole-witness floors count labels, before restriction to a group. -/
theorem Hyp.block_label_count (g : ℤ × ℤ × ℤ) (j : Fin (2 ^ D.T))
    (S : Finset (Fin D.n)) (hS : ∀ i ∈ S, D.j i = j ∧ D.MeetsGroup g i) :
    (S.card : ℝ) * D.a ^ D.d ≤ 33554432 * D.K ^ 15 := by
  classical
  have hK : 0 < D.K := by linarith [h.hK]
  have hq := h.q_pos
  have hKD : D.K ≠ 0 := hK.ne'
  have hcover : ∃ U : Set (α × ℝ),
      (∀ i ∈ S, D.B i ×ˢ tblock D.q (D.j i) ⊆ U) ∧
      D.μ U ≤ ENNReal.ofReal ((33554432 * D.K ^ 12) * D.q ^ 4) := by
    by_cases hsmall : D.K * D.q ≤ 1
    · by_cases hSne : S.Nonempty
      · obtain ⟨i, hiS⟩ := hSne
        obtain ⟨l, hlB, hg, hl⟩ := (hS i hiS).2
        obtain ⟨hv, hctr⟩ := h.reference_midpoint_bounds g hg hl j
        have hm := h.midpoint_abs_le_one j
        let U : Set (α × ℝ) := {p | D.basePoint p ∈ contactOuterBox (D.midpoint j)
          (D.groupReference g) (D.K * D.q) (8 * (8 * D.K ^ 2) * (D.K * D.q))
          (32 * (8 * D.K ^ 2) ^ 2 * (D.K * D.q) ^ 2)}
        refine ⟨U, ?_, ?_⟩
        · intro i hiS p hp
          have hh := h.group_contact_box (hS i hiS).2 hsmall p hp
          rw [(hS i hiS).1] at hh
          exact hh
        · have hmass := contact_box_measure_cap D.μ D.basePoint (fun _ => True)
            (K := 8 * D.K ^ 2) (C := 4 * D.K ^ 2) (p := D.groupReference g)
            (mul_pos hK hq) hsmall (by nlinarith [h.hK]) h.hw0
            (by nlinarith [h.hwq] : D.w ≤ (D.K * D.q) ^ 2)
            (by positivity : 0 ≤ 4 * D.K ^ 2) hm
            hv hctr
            (by simpa only [and_true] using h.base_cell_cap)
          have heq : 16384 * (4 * D.K ^ 2) * (8 * D.K ^ 2) ^ 3 * (D.K * D.q) ^ 4 =
              (33554432 * D.K ^ 12) * D.q ^ 4 := by ring
          rw [heq] at hmass
          simpa only [and_true, U] using hmass
      · refine ⟨∅, ?_, ?_⟩
        · intro i hi
          exact (hSne ⟨i, hi⟩).elim
        · simp only [measure_empty]
          exact bot_le
    · refine ⟨univ, fun _ _ => subset_univ _, ?_⟩
      apply h.mu_mass_le.trans
      apply ENNReal.ofReal_le_ofReal
      exact h.large_block_mass_bound (by linarith)
  obtain ⟨U, hU, hmass⟩ := hcover
  have hcount := witness_count_of_fourth_power_bound D.μ S
    (fun i => D.B i ×ˢ tblock D.q (D.j i)) U (θ := D.a ^ D.d / D.K ^ 3) hq
    (div_nonneg (Real.rpow_nonneg h.ha0.le _) (pow_nonneg hK.le 3))
    (by positivity : 0 ≤ 33554432 * D.K ^ 12)
    (fun i _ => (h.hB i).prod measurableSet_Icc)
    (by
      intro i hi i' hi' hne
      exact h.witness_disjoint hne ((hS i hi).1.trans (hS i' hi').1.symm))
    hU (fun i _ => h.incidence_witness_floor i) hmass
  calc
    (S.card : ℝ) * D.a ^ D.d = ((S.card : ℝ) * (D.a ^ D.d / D.K ^ 3)) * D.K ^ 3 := by field_simp [hKD]
    _ ≤ (33554432 * D.K ^ 12) * D.K ^ 3 := mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := by ring

end DepthData
end
end Submission.Obl.k4_horizontal_coefficient_count
