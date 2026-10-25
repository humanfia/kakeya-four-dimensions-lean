-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.PhysicalRowSelection, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/PhysicalRowSelection.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943 (branch x0943), commit 091cac36bec8e0bad842d8b69de784224c046045,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/PhysicalRowSelection.lean,
by x1037 (o287): the bounded physical model `Qualification.PhysicalModel` replaces the frozen packet.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/PhysicalRowSelection.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.FiniteStates
import Submission.Lib.K4VelocityStrips
import Submission.Lib.K4IncidenceWitnesses
import Submission.Lib.K4QuadraticSheets
import Submission.Lib.K4CommonLocalChoice


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory
open scoped BigOperators

noncomputable section

/-- **Physical row selection.** Coarse lists at TRUE physical cells construct actual physical row
comparison. Boundary transport is derived, and the selected law is a
literal union of whole ORIGINAL fine states, with its exact mass loss. -/
theorem original_physical_row_selection (p : PhysicalModel) (μ : Measure Ev)
    (E : Set Ev) (hE : MeasurableSet E) (hfull : ∀ᵐ z ∂μ, z ∈ E)
    (G : (Fin 4 → ℤ) → Fin 3 → ℝ) (b ρ B : ℝ)
    (hb : 0 < b) (hbρ : b ≤ ρ) (hB : 0 ≤ B)
    (hbound : ∀ z ∈ E, ‖G (p.physicalState b z)‖ ≤ B)
    (L : ℕ) (hL : 1 ≤ L) (s : ℕ → ℝ) (lists : ℕ → ℕ)
    (A : ℝ) (hA : 1 ≤ A) (hs0 : s 0 = 1) (hspos : ∀ i, 0 < s i)
    (hbgrid : ∀ i < L, b ≤ s i)
    (hratio : ∀ i, i + 1 < L → s i ≤ A * s (i+1)) (hfloor : s (L-1) ≤ ρ)
    (hlist : ∀ i < L, ∀ n : Fin 4 → ℤ, ∃ V : Finset (Fin 3 → ℤ), V.card ≤ lists i ∧
      ∀ z ∈ E, Submission.Lib.K4CommonLocalChoice.cell (s i)
        (originalPhysicalCoordinates (p.signal z.1) (p.position z.1) (p.velocity z.1) z.2) = n →
          Submission.Lib.K4CommonLocalChoice.cell (s i) (G (p.physicalState b z)) ∈ V) :
    ∃ U : Set (Fin 4 → ℤ), MeasurableSet U ∧
      μ univ ≤ (∏ i ∈ Finset.range L, ((4 : ENNReal) ^ 4 * ((7 : ℕ) ^ 4 * lists i))) *
        μ ((p.physicalState b) ⁻¹' U) ∧
      ∀ z ∈ E, p.physicalState b z ∈ U → ∀ z' ∈ E, p.physicalState b z' ∈ U →
        ‖G (p.physicalState b z) - G (p.physicalState b z')‖ ≤
          6 * (A+B) *
            (‖originalPhysicalCoordinates (p.signal z.1) (p.position z.1) (p.velocity z.1) z.2 -
              originalPhysicalCoordinates (p.signal z'.1) (p.position z'.1) (p.velocity z'.1) z'.2‖ + ρ) := by
  classical
  let X : Ev → Fin 4 → ℝ := fun z =>
    originalPhysicalCoordinates (p.signal z.1) (p.position z.1) (p.velocity z.1) z.2
  let corner : (Fin 4 → ℤ) → Fin 4 → ℝ := fun q j => b * (q j : ℝ)
  let Z : Ev → Fin 4 → ℝ := fun z => corner (p.physicalState b z)
  let Y : Ev → Fin 3 → ℝ := fun z => G (p.physicalState b z)
  have hZm : Measurable Z := (measurable_of_countable corner).comp (p.measurable_physicalState b)
  have hYm : Measurable Y := (measurable_of_countable G).comp (p.measurable_physicalState b)
  have hround (z : Ev) : ‖Z z - X z‖ ≤ b := by
    apply (pi_norm_le_iff_of_nonneg hb.le).mpr
    intro j
    change |b * (⌊X z j / b⌋ : ℝ) - X z j| ≤ b
    simpa only [mul_comm,abs_sub_comm] using
      Submission.Lib.K4VelocityStrips.midpoint_floor_center_bound hb (X z j)
  let near : (Fin 4 → ℤ) → Finset (Fin 4 → ℤ) := fun n =>
    Fintype.piFinset fun j => Finset.Icc (n j - 1) (n j + 1)
  have hnearCard (n : Fin 4 → ℤ) : (near n).card ≤ (7 : ℕ) ^ 4 := by
    have hh := Submission.Lib.K4IncidenceWitnesses.card_pi_grid_of_diameter (near n)
      (R := 2) (by norm_num) (by
        intro q hq q' hq' j
        have hqj := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hq j)
        have hqj' := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hq' j)
        have hd : |q j - q' j| ≤ (2 : ℤ) := abs_le.mpr ⟨by omega,by omega⟩
        exact_mod_cast hd)
    norm_num only [Fintype.card_fin] at hh
    exact_mod_cast hh
  have htransport (i : ℕ) (hi : i < L) (n : Fin 4 → ℤ) :
      ∃ V : Finset (Fin 3 → ℤ), V.card ≤ (7 : ℕ) ^ 4 * lists i ∧
        ∀ z ∈ E, Submission.Lib.K4CommonLocalChoice.cell (s i) (Z z) = n →
          Submission.Lib.K4CommonLocalChoice.cell (s i) (Y z) ∈ V := by
    have hex (q : Fin 4 → ℤ) := hlist i hi q
    choose table hcard hknown using hex
    let V := (near n).biUnion table
    refine ⟨V,?_,?_⟩
    · calc
        V.card ≤ ∑ q ∈ near n, (table q).card := Finset.card_biUnion_le
        _ ≤ ∑ _q ∈ near n, lists i := Finset.sum_le_sum fun q _ => hcard q
        _ = (near n).card * lists i := by simp
        _ ≤ (7 : ℕ) ^ 4 * lists i := Nat.mul_le_mul_right (lists i) (hnearCard n)
    · intro z hz hn
      let q := Submission.Lib.K4CommonLocalChoice.cell (s i) (X z)
      have hqn : q ∈ near n := by
        apply Fintype.mem_piFinset.mpr
        intro j
        have hclose : |X z j - Z z j| ≤ s i := by
          have hh := (norm_le_pi_norm (Z z - X z) j).trans (hround z)
          simpa only [Pi.sub_apply,Real.norm_eq_abs,abs_sub_comm] using hh.trans (hbgrid i hi)
        have hf := Submission.Lib.K4QuadraticSheets.floor_sub_le_one_of_abs_le (hspos i) hclose
        have hc : ⌊Z z j / s i⌋ = n j := congrFun hn j
        rw [hc] at hf
        exact Finset.mem_Icc.mpr ⟨by have := (abs_le.mp hf).1; change _ ≤ q j; dsimp [q,Submission.Lib.K4CommonLocalChoice.cell]; omega,
          by have := (abs_le.mp hf).2; change q j ≤ _; dsimp [q,Submission.Lib.K4CommonLocalChoice.cell]; omega⟩
      exact Finset.mem_biUnion.mpr ⟨q,hqn,hknown q z hz rfl⟩
  have htuples : ∀ i < L, ∀ (_ω : Unit) (n : Fin 4 → ℤ),
      ∃ V : Finset (Fin 3 → ℤ), V.card ≤ (7 : ℕ) ^ 4 * lists i ∧
        ∀ z ∈ E, () = _ω → Submission.Lib.K4CommonLocalChoice.cell (s i) (Z z) = n →
          Submission.Lib.K4CommonLocalChoice.cell (s i) (Y z) ∈ V := by
    intro i hi _ω n
    obtain ⟨V,hV,hk⟩ := htransport i hi n
    exact ⟨V,hV,fun z hz _ hn => hk z hz hn⟩
  obtain ⟨S,P,hS,hsub,hpredicate,hmass,hcmp⟩ :=
    Submission.Lib.K4CommonLocalChoice.common_local_choice μ (fun _ : Ev => ()) measurable_const
      Z hZm Y hYm E hE B hB hbound L hL s (fun i => (7 : ℕ) ^ 4 * lists i)
      A hA hs0 hspos hratio htuples
  let U : Set (Fin 4 → ℤ) := {q | P () (corner q) (G q)}
  have hU : MeasurableSet U := (Set.to_countable U).measurableSet
  have hSin (z : Ev) : z ∈ S ↔ z ∈ E ∧ p.physicalState b z ∈ U := hpredicate z
  have hmass' : μ E ≤ (∏ i ∈ Finset.range L, ((4 : ENNReal) ^ 4 * ((7 : ℕ) ^ 4 * lists i))) * μ S := by
    have hh := hmass ()
    norm_num at hh ⊢
    exact hh
  have hEfull : μ E = μ univ := by
    apply measure_congr
    filter_upwards [hfull] with z hz
    simp only [hz,mem_univ]
  refine ⟨U,hU,?_,?_⟩
  · rw [← hEfull]
    exact hmass'.trans (mul_le_mul' le_rfl (measure_mono (fun z hz => ((hSin z).mp hz).2)))
  · intro z hz hu z' hz' hu'
    have hc := hcmp z ((hSin z).mpr ⟨hz,hu⟩) z' ((hSin z').mpr ⟨hz',hu'⟩) rfl
    have hpositions : ‖Z z - Z z'‖ ≤ ‖X z - X z'‖ + 2 * b := by
      have h1 := dist_triangle (Z z) (X z) (Z z')
      have h2 := dist_triangle (X z) (X z') (Z z')
      simp only [dist_eq_norm] at h1 h2
      have h3 : dist (Z z') (X z') ≤ b := by
        simpa only [dist_eq_norm] using hround z'
      rw [dist_comm,dist_eq_norm] at h3
      linarith [hround z]
    have hinner : ‖Z z - Z z'‖ + s (L-1) ≤ 3 * (‖X z - X z'‖ + ρ) := by
      linarith [norm_nonneg (X z - X z')]
    exact hc.trans ((mul_le_mul_of_nonneg_left hinner (by positivity)).trans_eq (by ring))

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
