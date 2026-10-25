/- Adapted from this LOT tree, obligation o119, session x0404, commit b1aa67e,
   Submission/Obl/k4_finite_width_critical_contradiction/CompWorlds.lean. -/
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.CompEncode
import Submission.Obl.k4_dyadic_crop_worlds.Assembly

/-!
# Finitely many worlds as one encoded world

World `c : Fin W` is sent to the trajectories with index `≡ c (mod W)`, with the hidden
coefficients rescaled by `b c` and shifted by `o c` (`CompEncode`).  This file proves
that the encoded prior and event are tempered (in the formats `PriorFormat`/`EventFormat`
of accepted o089), and that the encoded incidence law is the weighted sum of the
pushed-forward world laws.
-/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder.Comp

attribute [local simp] encCoeff_zero encCoeff_one encCoeff_two encCoeff_three encCoeff_four encCoeff_five

open MeasureTheory Set
open Submission.Obl.k4_dyadic_crop_worlds (BoolFormat PriorFormat EventFormat)

abbrev Traj := ℕ × (Fin 6 → ℝ)
abbrev Inc := Traj × ℝ

/-- The encoded trajectory of world `c` out of `W`. -/
def encTraj (W c : ℕ) (b o : ℝ) (l : Traj) : Traj := (W * l.1 + c, encCoeff b o l.2)

/-- The encoded incidence of world `c` out of `W`. -/
def encInc (W c : ℕ) (b o : ℝ) (p : Inc) : Inc := (encTraj W c b o p.1, p.2)

theorem measurable_encTraj (W c : ℕ) (b o : ℝ) : Measurable (encTraj W c b o) :=
  (measurable_of_countable (fun i : ℕ => W * i + c)).comp measurable_fst |>.prodMk
    ((measurable_encCoeff b o).comp measurable_snd)

theorem measurable_encInc (W c : ℕ) (b o : ℝ) : Measurable (encInc W c b o) :=
  ((measurable_encTraj W c b o).comp measurable_fst).prodMk measurable_snd

/-- The world of an encoded index. -/
def worldOf {W : ℕ} (hW : 0 < W) (i : ℕ) : Fin W := ⟨i % W, Nat.mod_lt _ hW⟩

theorem worldOf_enc {W : ℕ} (hW : 0 < W) (c : Fin W) (i : ℕ) :
    worldOf hW (W * i + c) = c := by
  ext; simp [worldOf, Nat.add_mod, Nat.mod_eq_of_lt c.isLt]

theorem enc_div {W : ℕ} (hW : 0 < W) (c : Fin W) (i : ℕ) : (W * i + c) / W = i := by
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt c.isLt, zero_add]

/-- The encoded event: an incidence is in it when its decoding lies in the event of the
world named by its index. -/
noncomputable def encEvent {W : ℕ} (hW : 0 < W) (b o : Fin W → ℝ) (E : Fin W → Set Inc) :
    Set Inc :=
  {p | ((p.1.1 / W, decCoeff (b (worldOf hW p.1.1)) (o (worldOf hW p.1.1)) p.1.2), p.2) ∈
    E (worldOf hW p.1.1)}

theorem encInc_mem_encEvent {W : ℕ} (hW : 0 < W) {b o : Fin W → ℝ} (E : Fin W → Set Inc)
    (c : Fin W) (hb : b c ≠ 0) (p : Inc) :
    encInc W c (b c) (o c) p ∈ encEvent hW b o E ↔ p ∈ E c := by
  simp only [encEvent, encInc, encTraj, mem_ofPred_eq, worldOf_enc, enc_div hW,
    decCoeff_encCoeff hb]

theorem preimage_encInc_encEvent {W : ℕ} (hW : 0 < W) {b o : Fin W → ℝ}
    (E : Fin W → Set Inc) (c : Fin W) (hb : b c ≠ 0) :
    encInc W c (b c) (o c) ⁻¹' encEvent hW b o E = E c := by
  ext p; exact encInc_mem_encEvent hW E c hb p

theorem measurableSet_encEvent {W : ℕ} (hW : 0 < W) (b o : Fin W → ℝ) {E : Fin W → Set Inc}
    (hE : ∀ c, MeasurableSet (E c)) : MeasurableSet (encEvent hW b o E) := by
  have h : encEvent hW b o E = ⋃ c : Fin W, ({p : Inc | worldOf hW p.1.1 = c} ∩
      (fun p : Inc => ((p.1.1 / W, decCoeff (b c) (o c) p.1.2), p.2)) ⁻¹' E c) := by
    ext p
    simp only [encEvent, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage]
    constructor
    · intro hp; exact ⟨_, rfl, hp⟩
    · rintro ⟨c, rfl, hp⟩; exact hp
  rw [h]
  refine MeasurableSet.iUnion fun c => MeasurableSet.inter ?_ ?_
  · exact (measurable_of_countable (fun i : ℕ => worldOf hW i)).comp
      (measurable_fst.comp measurable_fst) (measurableSet_singleton c)
  · refine MeasurableSet.preimage (hE c) ?_
    refine Measurable.prodMk (Measurable.prodMk ?_ ?_) measurable_snd
    · exact (measurable_of_countable (fun i : ℕ => i / W)).comp
        (measurable_fst.comp measurable_fst)
    · exact (measurable_decCoeff _ _).comp (measurable_snd.comp measurable_fst)

/-- The encoded prior: the weighted sum of the encoded world priors. -/
noncomputable def encPrior (W : ℕ) (a b o : Fin W → ℝ) (ν : Fin W → Measure Traj) :
    Measure Traj :=
  ∑ c, ENNReal.ofReal (a c) • Measure.map (encTraj W c (b c) (o c)) (ν c)

/-- The encoded incidence law is the weighted sum of the encoded world laws. -/
theorem encLaw_eq {W : ℕ} (hW : 0 < W) (a b o : Fin W → ℝ) (ν : Fin W → Measure Traj)
    [∀ c, SFinite (ν c)] (E : Fin W → Set Inc) (hE : ∀ c, MeasurableSet (E c))
    (hb : ∀ c, b c ≠ 0) :
    ((encPrior W a b o ν).prod volume).restrict (encEvent hW b o E) =
      ∑ c, ENNReal.ofReal (a c) • Measure.map (encInc W c (b c) (o c))
        (((ν c).prod volume).restrict (E c)) := by
  have hEm := measurableSet_encEvent hW b o hE
  have hprod : (encPrior W a b o ν).prod volume = ∑ c, ENNReal.ofReal (a c) •
      Measure.map (encInc W c (b c) (o c)) ((ν c).prod volume) := by
    unfold encPrior
    rw [← Measure.sum_fintype, Measure.prod_sum_left]
    rw [← Measure.sum_fintype]
    congr 1
    funext c
    rw [Measure.prod_smul_left]
    congr 1
    have h := Measure.map_prod_map (ν c) (volume : Measure ℝ)
      (measurable_encTraj W c (b c) (o c)) measurable_id
    rw [Measure.map_id] at h
    rw [h]
    rfl
  rw [hprod]
  ext S hS
  rw [Measure.restrict_apply hS]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  rw [Measure.map_apply (measurable_encInc _ _ _ _) (hS.inter hEm),
    Measure.map_apply (measurable_encInc _ _ _ _) hS,
    Measure.restrict_apply ((measurable_encInc _ _ _ _) hS), preimage_inter,
    preimage_encInc_encEvent hW E c (hb c)]

end Submission.Obl.k4_native_calibrated_homogeneous_remainder.Comp
