/- Adapted from our LOT tree o211, session x0736, commit fb9fb2638e83e4e42cdf985859ec4b5deb228222,
`Submission/Obl/k4_critical_affine_derivative_preparation/NativeJointCap.lean`.
Earlier provenance comments in that file are retained below. -/

import Submission.Obl.k4_critical_conditional_row_preparation.AffineEntries
import Submission.Obl.k4_critical_conditional_row_preparation.JointCapRecovery

namespace Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

open MeasureTheory Set
open scoped ENNReal

/-- A normalized floor cell is contained in the corresponding physical
closed interval, with side length equal to the true time length times mesh. -/
theorem physical_interval_of_normalized_floor
    (x center H ξ : ℝ) (j : ℤ) (hH : 0 < H) (hξ : 0 < ξ)
    (hfloor : ⌊((x - center) / H) / ξ⌋ = j) :
    x ∈ Icc (center + H * ξ * j) (center + H * ξ * j + H * ξ) := by
  have hlo := Int.floor_le (((x - center) / H) / ξ)
  have hhi := Int.lt_floor_add_one (((x - center) / H) / ξ)
  rw [hfloor] at hlo hhi
  have hlo' := (le_div_iff₀ hH).mp ((le_div_iff₀ hξ).mp hlo)
  have hhi' := (div_lt_iff₀ hH).mp ((div_lt_iff₀ hξ).mp hhi)
  constructor <;> nlinarith only [hlo', hhi']

theorem floor_bin_eq_Ico (ξ : ℝ) (j : ℤ) (hξ : 0 < ξ) :
    {w : ℝ | ⌊w / ξ⌋ = j} = Ico ((j : ℝ) * ξ) (((j : ℝ) + 1) * ξ) := by
  ext w
  simp only [mem_ofPred_eq, mem_Ico, Int.floor_eq_iff]
  rw [le_div_iff₀ hξ, div_lt_iff₀ hξ]

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The exact original native fine-grid cap, with its original palette factor. -/
def NativeFineJointCap (cfg : Data α) (k : ℕ) (s δ ξ : ℝ) : Prop :=
  ∀ (q : Fin 3 → ℤ) (b j : ℤ),
      cfg.μ k {p | (fun e : Fin 3 =>
          ⌊(![p.2, cfg.b k p.1 0 + p.2 * cfg.b k p.1 3,
            cfg.b k p.1 1 + p.2 * cfg.b k p.1 4] : Fin 3 → ℝ) e / δ⌋) = q ∧
        ⌊(cfg.b k p.1 2 + p.2 * cfg.b k p.1 5) / (cfg.N k ^ (-s))⌋ = b ∧
        ⌊cfg.b k p.1 3 / ξ⌋ = j} ≤
        ENNReal.ofReal (cfg.K k * δ ^ 3 * (cfg.N k ^ (-s)) ^ cfg.d) *
          cfg.π k {w | ⌊w / ξ⌋ = j}

/-- A two-coordinate Row cell on the actual normalized time law. -/
def normalizedRowCell (cfg : Data α) (k : ℕ) (H t₀ Z₀ ξ : ℝ)
    (q : Fin 2 → ℤ) (j : ℤ) : Set (α × ℝ) :=
  {p | ⌊p.2 / ξ⌋ = q 0 ∧
    ⌊((cfg.b k p.1 0 + t₀ * cfg.b k p.1 3 - Z₀) / H + p.2 * cfg.b k p.1 3) / ξ⌋ = q 1 ∧
    ⌊cfg.b k p.1 3 / ξ⌋ = j}

theorem measurableSet_normalizedRowCell (cfg : Data α) (k : ℕ)
    (hb : Measurable (cfg.b k)) (H t₀ Z₀ ξ : ℝ) (q : Fin 2 → ℤ) (j : ℤ) :
    MeasurableSet (cfg.normalizedRowCell k H t₀ Z₀ ξ q j) := by
  have hb₀ : Measurable (fun p : α × ℝ => cfg.b k p.1 0) :=
    ((measurable_pi_apply 0).comp hb).comp measurable_fst
  have hb₃ : Measurable (fun p : α × ℝ => cfg.b k p.1 3) :=
    ((measurable_pi_apply 3).comp hb).comp measurable_fst
  have h₀ : MeasurableSet {p : α × ℝ | ⌊p.2 / ξ⌋ = q 0} := (Int.measurable_floor.comp (measurable_snd.div_const ξ)) (measurableSet_singleton (q 0))
  have hbase := (((hb₀.add (hb₃.const_mul t₀)).sub_const Z₀).div_const H).add
    (measurable_snd.mul hb₃)
  have h₁ := (Int.measurable_floor.comp (hbase.div_const ξ)) (measurableSet_singleton (q 1))
  have hv := (Int.measurable_floor.comp (hb₃.div_const ξ)) (measurableSet_singleton j)
  exact h₀.inter (h₁.inter hv)

/-- The original true reference is positive and has the fourth-power
lower bound needed to pay for its original joint cells. -/
theorem AssignmentLevel.original_reference_floor
    (h : cfg.Valid) {k : ℕ} {s : ℝ} (a : cfg.AssignmentLevel k s)
    (i : Fin (cfg.n k s)) :
    0 < cfg.timeLength k s * (cfg.ν k).real (cfg.A k s i) ∧
      cfg.timeLength k s ^ 4 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 2 ≤
        cfg.timeLength k s * (cfg.ν k).real (cfg.A k s i) := by
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 0 < cfg.K k := by linarith [h.subpower.1 k]
  have hH : 0 < cfg.timeLength k s := by unfold timeLength; positivity
  have hlower := mul_le_mul_of_nonneg_left (a.critical_prior_bounds h i).1 hH.le
  have heq : cfg.timeLength k s *
      (cfg.timeLength k s ^ 3 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 2) =
      cfg.timeLength k s ^ 4 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 2 := by ring
  rw [heq] at hlower
  exact ⟨(by positivity : 0 < cfg.timeLength k s ^ 4 * (cfg.N k ^ (-s)) ^ cfg.d /
    cfg.K k ^ 2).trans_le hlower, hlower⟩

/-- At one original true label, integrate the frozen native joint caps over
a normalized position cell. The actual transverse and hidden ranges are
used, together with the earlier full true assignment reference. -/
theorem AssignmentLevel.original_label_joint_cap
    (h : cfg.Valid) {k : ℕ} {s : ℝ} (a : cfg.AssignmentLevel k s)
    (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ)
    (hL : ∀ e : Fin 3, |L e.succ| ≤ 8 * cfg.K k ^ 4)
    (hfit : ∀ l ∈ cfg.B k s i, ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
      |cfg.b k l 2 + t * cfg.b k l 5 - affineBaseValue L
        ![t, cfg.b k l 0 + t * cfg.b k l 3, cfg.b k l 1 + t * cfg.b k l 4]| ≤
          cfg.K k * cfg.N k ^ (-s))
    (δ ξ t₀ Z₀ : ℝ) (hδ : 0 < δ) (hξ : 0 < ξ)
    (hδcell : δ ≤ cfg.timeLength k s * ξ)
    (hδtrans : δ ≤ cfg.K k * cfg.timeLength k s * cfg.N k ^ (-cfg.ℓ * s))
    (hmesh : 3 * δ ≤ cfg.N k ^ (-s))
    (hcap : cfg.NativeFineJointCap k s δ ξ) :
    ∀ (q : Fin 2 → ℤ) (j : ℤ),
      cfg.μ k {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ I (cfg.T k s) (cfg.j k s i) ∧
        ⌊((p.2 - t₀) / cfg.timeLength k s) / ξ⌋ = q 0 ∧
        ⌊((cfg.b k p.1 0 + p.2 * cfg.b k p.1 3 - Z₀) / cfg.timeLength k s) / ξ⌋ = q 1 ∧
        ⌊cfg.b k p.1 3 / ξ⌋ = j} ≤
      ENNReal.ofReal (27648 * cfg.K k ^ 11 * cfg.timeLength k s ^ 4 *
        (cfg.N k ^ (-s)) ^ cfg.d * ξ ^ 2) * cfg.π k {w | ⌊w / ξ⌋ = j} := by
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
    ⌊((p.2 - t₀) / H) / ξ⌋ = q 0 ∧
    ⌊((cfg.b k p.1 0 + p.2 * cfg.b k p.1 3 - Z₀) / H) / ξ⌋ = q 1 ∧ velocity p = j}
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 1 ≤ K := h.subpower.1 k
  have hKpos : 0 < K := by linarith
  have hQ : 1 ≤ Q := by dsimp [Q]; nlinarith [one_le_pow₀ hK (n := 4)]
  have hKQ : K ≤ Q := by
    have hh := pow_le_pow_right₀ hK (show 1 ≤ 4 by norm_num)
    dsimp [Q]
    simpa only [pow_one] using hh.trans (by nlinarith [pow_nonneg hKpos.le 4])
  have hH : 0 < H := by dsimp [H, timeLength]; positivity
  have ha : 0 < cfg.N k ^ (-s) := Real.rpow_pos_of_pos hN _
  have hg : cfg.N k ^ (-cfg.ℓ * s) ≤ K * H := by
    rw [h.horizontal_rate]
    exact (time_length_comparison hN hKpos a.time_lower a.time_upper).2
  have hB : B ≤ K ^ 2 * H ^ 2 := by
    dsimp [B]
    have hh := mul_le_mul_of_nonneg_left hg (mul_nonneg hKpos.le hH.le)
    nlinarith only [hh]
  have hbound := original_native_joint_cap_rectangle (cfg.μ k) U point value velocity j
    δ (cfg.N k ^ (-s)) (H * ξ) B Q
    (t₀ + H * ξ * q 0) (Z₀ + H * ξ * q 1) K ((cfg.N k ^ (-s)) ^ cfg.d)
    (cfg.π k {w | ⌊w / ξ⌋ = j})
    ![cfg.c k s i 2, cfg.c k s i 3, cfg.c k s i 4] L
    hδ ha hQ hKpos.le (by positivity) hδcell hδtrans hmesh
    ((a.coefficient_bound i 3).trans hKQ) ((a.coefficient_bound i 4).trans hKQ) hL
    (fun p hp => physical_interval_of_normalized_floor p.2 t₀ H ξ (q 0) hH hξ hp.2.2.1)
    (fun p hp => physical_interval_of_normalized_floor _ Z₀ H ξ (q 1) hH hξ hp.2.2.2.1)
    (fun p hp => by
      have hh := (a.geometry i p.1 (a.fitted_subset i hp.1) p.2 hp.2.1).2.1
      simpa [point, x, B, H, K, mul_comm] using hh)
    (fun p hp => (hfit p.1 hp.1 p.2 hp.2.1).trans (mul_le_mul_of_nonneg_right hKQ ha.le))
    (fun p hp => hp.2.2.2.2) (fun q b => hcap q b j)
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right _ (zero_le : 0 ≤ cfg.π k {w | ⌊w / ξ⌋ = j})
  apply ENNReal.ofReal_le_ofReal
  calc
    432 * K * Q ^ 2 * (H * ξ) ^ 2 * B * (cfg.N k ^ (-s)) ^ cfg.d ≤
        432 * K * Q ^ 2 * (H * ξ) ^ 2 * (K ^ 2 * H ^ 2) * (cfg.N k ^ (-s)) ^ cfg.d := by gcongr
    _ = 27648 * K ^ 11 * H ^ 4 * (cfg.N k ^ (-s)) ^ cfg.d * ξ ^ 2 := by dsimp [Q]; ring

/-- The actual continuous law, divided by its original full true-label
reference, satisfies Row's joint cell cap with a fixed polynomial loss. -/
theorem AssignmentLevel.normalized_label_joint_cap
    (h : cfg.Valid) {k : ℕ} {s : ℝ} (a : cfg.AssignmentLevel k s)
    (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ)
    (hL : ∀ e : Fin 3, |L e.succ| ≤ 8 * cfg.K k ^ 4)
    (hfit : ∀ l ∈ cfg.B k s i, ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
      |cfg.b k l 2 + t * cfg.b k l 5 - affineBaseValue L
        ![t, cfg.b k l 0 + t * cfg.b k l 3, cfg.b k l 1 + t * cfg.b k l 4]| ≤
          cfg.K k * cfg.N k ^ (-s))
    (σ : Measure (α × ℝ)) (hσ : σ ≤ (cfg.μ k).restrict
      (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)))
    (δ ξ t₀ Z₀ : ℝ) (hδ : 0 < δ) (hξ : 0 < ξ)
    (hδcell : δ ≤ cfg.timeLength k s * ξ)
    (hδtrans : δ ≤ cfg.K k * cfg.timeLength k s * cfg.N k ^ (-cfg.ℓ * s))
    (hmesh : 3 * δ ≤ cfg.N k ^ (-s))
    (hcap : cfg.NativeFineJointCap k s δ ξ) :
    ∀ (q : Fin 2 → ℤ) (j : ℤ),
      (ENNReal.ofReal (cfg.timeLength k s * (cfg.ν k).real (cfg.A k s i))⁻¹ •
        σ.map (unitTimeMap t₀ (cfg.timeLength k s)))
        (cfg.normalizedRowCell k (cfg.timeLength k s) t₀ Z₀ ξ q j) ≤
      ENNReal.ofReal (27648 * cfg.K k ^ 13 * ξ ^ 2) *
        cfg.π k (Ico ((j : ℝ) * ξ) (((j : ℝ) + 1) * ξ)) := by
  intro q j
  let H := cfg.timeLength k s
  let W := H * (cfg.ν k).real (cfg.A k s i)
  let E := cfg.normalizedRowCell k H t₀ Z₀ ξ q j
  have hE : MeasurableSet E := cfg.measurableSet_normalizedRowCell k (h.basic k).1 H t₀ Z₀ ξ q j
  have hH : 0 < H := by dsimp [H, timeLength]; positivity
  have hK : 0 < cfg.K k := by linarith [h.subpower.1 k]
  have hW : 0 < W := (a.original_reference_floor h i).1
  have hpaid : H ^ 4 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 2 ≤ W :=
    (a.original_reference_floor h i).2
  have hpos (p : α × ℝ) :
      (cfg.b k p.1 0 + t₀ * cfg.b k p.1 3 - Z₀) / H +
          ((p.2 - t₀) / H) * cfg.b k p.1 3 =
      (cfg.b k p.1 0 + p.2 * cfg.b k p.1 3 - Z₀) / H := by ring
  have hphysical : σ ((unitTimeMap t₀ H) ⁻¹' E) ≤
      ENNReal.ofReal ((27648 * cfg.K k ^ 11) * H ^ 4 *
        (cfg.N k ^ (-s)) ^ cfg.d * ξ ^ 2) * cfg.π k {w | ⌊w / ξ⌋ = j} := by
    calc
      _ ≤ ((cfg.μ k).restrict (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)))
          ((unitTimeMap t₀ H) ⁻¹' E) := hσ _
      _ = cfg.μ k {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ I (cfg.T k s) (cfg.j k s i) ∧
          ⌊((p.2 - t₀) / H) / ξ⌋ = q 0 ∧
          ⌊((cfg.b k p.1 0 + p.2 * cfg.b k p.1 3 - Z₀) / H) / ξ⌋ = q 1 ∧
          ⌊cfg.b k p.1 3 / ξ⌋ = j} := by
        rw [Measure.restrict_apply ((measurable_unitTimeMap t₀ H) hE)]
        congr 1
        ext p
        simp only [E, normalizedRowCell, mem_inter_iff, mem_preimage, mem_prod,
          unitTimeMap, mem_ofPred_eq, hpos]
        tauto
      _ ≤ _ := a.original_label_joint_cap h i L hL hfit δ ξ t₀ Z₀ hδ hξ
        hδcell hδtrans hmesh hcap q j
  have hnormalized := original_normalized_event_joint_cap σ E hE t₀ H
    ((cfg.N k ^ (-s)) ^ cfg.d) W (27648 * cfg.K k ^ 11) (cfg.K k) ξ
    (cfg.π k {w | ⌊w / ξ⌋ = j}) hW hK (by positivity) hpaid hphysical
  apply hnormalized.trans_eq
  rw [floor_bin_eq_Ico ξ j hξ]
  congr 2
  ring

end Data

end

end Submission.Obl.k4_critical_conditional_row_preparation
