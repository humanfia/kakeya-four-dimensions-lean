import Submission.Obl.k4_critical_conditional_row_preparation.NativeJointCap
import Submission.Obl.k4_critical_conditional_row_preparation.Atlas
import Submission.Obl.k4_critical_conditional_row_preparation.FrozenRows
import Submission.Obl.k4_critical_conditional_row_preparation.JointScales

namespace Submission.Obl.k4_critical_conditional_row_preparation
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators
namespace Data
variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The original joint cap with independent physical base and velocity meshes.
Adapted from o211/x0736 `NativeJointCap.original_label_joint_cap`; its original
provenance is recorded in NativeJointCap.lean in this subtree. -/
theorem AssignmentLevel.physical_rectangle_joint_cap
    (h : cfg.Valid) {k : ℕ} {s : ℝ} (a : cfg.AssignmentLevel k s)
    (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ)
    (hL : ∀ e : Fin 3, |L e.succ| ≤ 8 * cfg.K k ^ 4)
    (hfit : ∀ l ∈ cfg.B k s i, ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
      |cfg.b k l 2 + t * cfg.b k l 5 - affineBaseValue L
        ![t, cfg.b k l 0 + t * cfg.b k l 3, cfg.b k l 1 + t * cfg.b k l 4]| ≤
          cfg.K k * cfg.N k ^ (-s))
    (δ ξ w t₀ Z₀ : ℝ) (hδ : 0 < δ) (hξ : 0 < ξ)
    (hδcell : δ ≤ w)
    (hδtrans : δ ≤ cfg.K k * cfg.timeLength k s * cfg.N k ^ (-cfg.ℓ * s))
    (hmesh : 3 * δ ≤ cfg.N k ^ (-s))
    (hcap : cfg.NativeFineJointCap k s δ ξ) :
    ∀ (q : Fin 2 → ℤ) (j : ℤ),
      cfg.μ k {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ I (cfg.T k s) (cfg.j k s i) ∧
        ⌊(p.2 - t₀) / w⌋ = q 0 ∧
        ⌊(cfg.b k p.1 0 + p.2 * cfg.b k p.1 3 - Z₀) / w⌋ = q 1 ∧
        ⌊cfg.b k p.1 3 / ξ⌋ = j} ≤
      ENNReal.ofReal (27648 * cfg.K k ^ 11 * cfg.timeLength k s ^ 2 *
        (cfg.N k ^ (-s)) ^ cfg.d * w ^ 2) * cfg.π k {w | ⌊w / ξ⌋ = j} := by
  intro q j
  let H := cfg.timeLength k s
  let K := cfg.K k
  let Q := 8 * K ^ 4
  let B := K * H * cfg.N k ^ (-cfg.ℓ * s)
  let point : α × ℝ → Fin 3 → ℝ := fun p =>
    ![p.2, cfg.b k p.1 0 + p.2 * cfg.b k p.1 3, cfg.b k p.1 1 + p.2 * cfg.b k p.1 4]
  let value : α × ℝ → ℝ := fun p => cfg.b k p.1 2 + p.2 * cfg.b k p.1 5
  let velocity : α × ℝ → ℤ := fun p => ⌊cfg.b k p.1 3 / ξ⌋
  let U : Set (α × ℝ) := {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ I (cfg.T k s) (cfg.j k s i) ∧
    ⌊(p.2 - t₀) / w⌋ = q 0 ∧
    ⌊(cfg.b k p.1 0 + p.2 * cfg.b k p.1 3 - Z₀) / w⌋ = q 1 ∧ velocity p = j}
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 1 ≤ K := h.subpower.1 k
  have hKpos : 0 < K := by linarith
  have hQ : 1 ≤ Q := by dsimp [Q]; nlinarith [one_le_pow₀ hK (n := 4)]
  have hKQ : K ≤ Q := by
    have hh := pow_le_pow_right₀ hK (show 1 ≤ 4 by norm_num)
    dsimp [Q]
    simpa only [pow_one] using hh.trans (by nlinarith [pow_nonneg hKpos.le 4])
  have hH : 0 < H := by dsimp [H, timeLength]; positivity
  have hw : 0 < w := hδ.trans_le hδcell
  have ha : 0 < cfg.N k ^ (-s) := Real.rpow_pos_of_pos hN _
  have hg : cfg.N k ^ (-cfg.ℓ * s) ≤ K * H := by
    rw [h.horizontal_rate]
    exact (time_length_comparison hN hKpos a.time_lower a.time_upper).2
  have hB : B ≤ K ^ 2 * H ^ 2 := by
    dsimp [B]
    have hh := mul_le_mul_of_nonneg_left hg (mul_nonneg hKpos.le hH.le)
    nlinarith only [hh]
  have hbound := original_native_joint_cap_rectangle (cfg.μ k) U point value velocity j
    δ (cfg.N k ^ (-s)) w B Q
    (t₀ + w * q 0) (Z₀ + w * q 1) K ((cfg.N k ^ (-s)) ^ cfg.d)
    (cfg.π k {w | ⌊w / ξ⌋ = j})
    ![cfg.c k s i 2, cfg.c k s i 3, cfg.c k s i 4] L
    hδ ha hQ hKpos.le (by positivity) hδcell hδtrans hmesh
    ((a.coefficient_bound i 3).trans hKQ) ((a.coefficient_bound i 4).trans hKQ) hL
    (fun p hp => by simpa only [point, Matrix.cons_val_zero, div_one, one_mul] using physical_interval_of_normalized_floor p.2 t₀ 1 w (q 0) (by norm_num) hw (by simpa only [div_one] using hp.2.2.1))
    (fun p hp => by simpa only [div_one, one_mul] using physical_interval_of_normalized_floor _ Z₀ 1 w (q 1) (by norm_num) hw (by simpa only [div_one, point, Matrix.cons_val_one, Matrix.cons_val_zero] using hp.2.2.2.1))
    (fun p hp => by
      have hh := (a.geometry i p.1 (a.fitted_subset i hp.1) p.2 hp.2.1).2.1
      simpa [point, x, B, H, K, mul_comm] using hh)
    (fun p hp => (hfit p.1 hp.1 p.2 hp.2.1).trans (mul_le_mul_of_nonneg_right hKQ ha.le))
    (fun p hp => hp.2.2.2.2) (fun q b => hcap q b j)
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right _ (zero_le : 0 ≤ cfg.π k {w | ⌊w / ξ⌋ = j})
  apply ENNReal.ofReal_le_ofReal
  calc
    432 * K * Q ^ 2 * w ^ 2 * B * (cfg.N k ^ (-s)) ^ cfg.d ≤
        432 * K * Q ^ 2 * w ^ 2 * (K ^ 2 * H ^ 2) * (cfg.N k ^ (-s)) ^ cfg.d := by gcongr
    _ = 27648 * K ^ 11 * H ^ 2 * (cfg.N k ^ (-s)) ^ cfg.d * w ^ 2 := by dsimp [Q]; ring


end Data

/-- A pair code for a physical horizontal square. -/
def basePair {α : Type*} (b : α → Fin 6 → ℝ) (t₀ Z₀ w : ℝ) (p : α × ℝ) : ℤ × ℤ :=
  (⌊(p.2 - t₀) / w⌋, ⌊(b p.1 0 + p.2 * b p.1 3 - Z₀) / w⌋)

theorem measurable_basePair {α : Type*} [MeasurableSpace α]
    (b : α → Fin 6 → ℝ) (hb : Measurable b) (t₀ Z₀ w : ℝ) :
    Measurable (basePair b t₀ Z₀ w) := by
  apply Measurable.prodMk
  · exact Int.measurable_floor.comp ((measurable_snd.sub_const t₀).div_const w)
  · apply Int.measurable_floor.comp
    fun_prop

def baseOptions (w t₀ Z₀ td Zd R : ℝ) : Finset (ℤ × ℤ) :=
  (floorBand w (td - t₀) R) ×ˢ (floorBand w (Zd - Z₀) R)

theorem mem_baseOptions {α : Type*} (b : α → Fin 6 → ℝ)
    (w t₀ Z₀ td Zd R : ℝ) (p : α × ℝ) (hw : 0 < w)
    (ht : |p.2 - td| ≤ R) (hZ : |b p.1 0 + p.2 * b p.1 3 - Zd| ≤ R) :
    basePair b t₀ Z₀ w p ∈ baseOptions w t₀ Z₀ td Zd R := by
  apply Finset.mem_product.mpr
  constructor
  · apply mem_floorBand hw
    convert ht using 1
    congr 1
    ring
  · apply mem_floorBand hw
    convert hZ using 1
    congr 1
    ring

/-- Fine-cell count times the original cap reference is bounded by the
original physical fourth-power weight, independently of the mesh. -/
theorem baseOptions_reference_bound
    (w t₀ Z₀ td Zd H K A : ℝ) (hw : 0 < w) (hH : 0 < H)
    (hK : 1 ≤ K) (hA : 0 ≤ A) (hwH : w ≤ H) :
    ((baseOptions w t₀ Z₀ td Zd (2 * K * H)).card : ℝ) * (H ^ 2 * A * w ^ 2) ≤
      36 * K ^ 2 * H ^ 4 * A := by
  have hK0 : 0 ≤ K := by linarith
  have hHK : H ≤ K * H := le_mul_of_one_le_left hH.le hK
  have hband (x : ℝ) : ((floorBand w x (2 * K * H)).card : ℝ) * w ≤ 6 * K * H := by
    have hc := mul_le_mul_of_nonneg_right (floorBand_card (center := x) (radius := 2 * K * H) hw (by positivity)) hw.le
    have heq : (2 * (2 * K * H) / w + 2) * w = 4 * K * H + 2 * w := by field_simp; ring
    rw [heq] at hc
    linarith only [hc, hwH, hHK]
  have hc : ((baseOptions w t₀ Z₀ td Zd (2 * K * H)).card : ℝ) * w ^ 2 ≤
      36 * K ^ 2 * H ^ 2 := by
    rw [baseOptions, Finset.card_product, Nat.cast_mul]
    calc
      _ = (((floorBand w (td - t₀) (2 * K * H)).card : ℝ) * w) *
          (((floorBand w (Zd - Z₀) (2 * K * H)).card : ℝ) * w) := by ring
      _ ≤ (6 * K * H) * (6 * K * H) :=
        mul_le_mul (hband _) (hband _) (by positivity) (by positivity)
      _ = _ := by ring
  calc
    _ = (((baseOptions w t₀ Z₀ td Zd (2 * K * H)).card : ℝ) * w ^ 2) * (H ^ 2 * A) := by ring
    _ ≤ (36 * K ^ 2 * H ^ 2) * (H ^ 2 * A) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

end
end Submission.Obl.k4_critical_conditional_row_preparation
