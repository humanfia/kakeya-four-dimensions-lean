import Submission.Obl.k4_horizontal_coefficient_count.CellCap
import Submission.Obl.k4_critical_switching_state_preparation.Inherited.ContactGrid
import Submission.Obl.k4_scalar_initial_true_horizon.FiniteCardBound

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set
open scoped ENNReal BigOperators
open Submission.Obl.k4_critical_switching_state_preparation.Inherited

/-- The accepted fourth-power contact count also supplies a finite complete
cell cover. Absolute bounds on the reference intercepts are unnecessary. -/
theorem finite_contact_box_codes {m H K δ : ℝ} {p : Fin 3 → ℝ}
    (hH : 0 < H) (hH1 : H ≤ 1) (hK : 1 ≤ K) (hδ : 0 < δ) (hδH : δ ≤ H ^ 2)
    (hm : |m| ≤ 1) (hv : |p 2| ≤ K) (hcenter : |p 0 + m * p 2| ≤ K) :
    ∃ F : Finset (Fin 3 → ℤ),
      (F.card : ℝ) * δ ^ 3 ≤ 16384 * K ^ 3 * H ^ 4 ∧
      ∀ z ∈ contactOuterBox m p H (8 * K * H) (32 * K ^ 2 * H ^ 2),
        (fun e => ⌊z e / δ⌋) ∈ F := by
  classical
  let Q : Set (Fin 3 → ℤ) :=
    (fun z e => ⌊z e / δ⌋) '' contactOuterBox m p H (8 * K * H) (32 * K ^ 2 * H ^ 2)
  have hcount (F : Finset (Fin 3 → ℤ)) (hF : (F : Set _) ⊆ Q) :
      (F.card : ℝ) * δ ^ 3 ≤ 16384 * K ^ 3 * H ^ 4 := by
    apply contactGrid_count hH hH1 hK hδ hδH hm hv hcenter F
    intro j hj
    obtain ⟨z, hz, heq⟩ := hF hj
    exact ⟨z, fun e => congrFun heq e, hz⟩
  have hfinite : Q.Finite :=
    Submission.Obl.k4_scalar_initial_true_horizon.finite_of_uniform_finset_card_bound
      Q (16384 * K ^ 3 * H ^ 4 / δ ^ 3)
      (fun F hF => (le_div_iff₀ (pow_pos hδ 3)).mpr (hcount F hF))
  refine ⟨hfinite.toFinset, hcount hfinite.toFinset (fun j hj => hfinite.mem_toFinset.mp hj), ?_⟩
  intro z hz
  exact hfinite.mem_toFinset.mpr ⟨z, hz, rfl⟩

/-- Integrate an original fine-cell cap over a complete contact box. The
additional condition may retain any hidden or velocity bin. -/
theorem contact_box_measure_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (point : Ω → Fin 3 → ℝ) (condition : Ω → Prop)
    {m H K δ C : ℝ} {p : Fin 3 → ℝ}
    (hH : 0 < H) (hH1 : H ≤ 1) (hK : 1 ≤ K) (hδ : 0 < δ) (hδH : δ ≤ H ^ 2)
    (hC : 0 ≤ C) (hm : |m| ≤ 1) (hv : |p 2| ≤ K) (hcenter : |p 0 + m * p 2| ≤ K)
    (hcap : ∀ j : Fin 3 → ℤ,
      μ {ω | (fun e => ⌊point ω e / δ⌋) = j ∧ condition ω} ≤ ENNReal.ofReal (C * δ ^ 3)) :
    μ {ω | point ω ∈ contactOuterBox m p H (8 * K * H) (32 * K ^ 2 * H ^ 2) ∧
      condition ω} ≤ ENNReal.ofReal (16384 * C * K ^ 3 * H ^ 4) := by
  obtain ⟨F, hcount, hcover⟩ := finite_contact_box_codes hH hH1 hK hδ hδH hm hv hcenter
  convert measure_le_of_finite_cell_cover μ
    {ω | point ω ∈ contactOuterBox m p H (8 * K * H) (32 * K ^ 2 * H ^ 2) ∧ condition ω}
    (fun ω e => ⌊point ω e / δ⌋) condition F hC
    (fun ω hω => ⟨hcover (point ω) hω.1, hω.2⟩) hcount (fun j _ => hcap j) using 1
  congr 1
  ring

/-- Complete witnesses in one common contact box count the labels before
restriction to a velocity or parameter group. -/
theorem contact_witness_count {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (point : Ω → Fin 3 → ℝ) (S : Finset ι) (E : ι → Set Ω)
    {m H K δ C θ : ℝ} {p : Fin 3 → ℝ}
    (hH : 0 < H) (hH1 : H ≤ 1) (hK : 1 ≤ K) (hδ : 0 < δ) (hδH : δ ≤ H ^ 2)
    (hC : 0 ≤ C) (hθ : 0 ≤ θ) (hm : |m| ≤ 1) (hv : |p 2| ≤ K)
    (hcenter : |p 0 + m * p 2| ≤ K)
    (hcap : ∀ j : Fin 3 → ℤ,
      μ {ω | (fun e => ⌊point ω e / δ⌋) = j} ≤ ENNReal.ofReal (C * δ ^ 3))
    (hE : ∀ i ∈ S, MeasurableSet (E i))
    (hdisj : (S : Set ι).PairwiseDisjoint E)
    (hsub : ∀ i ∈ S, ∀ ω ∈ E i,
      point ω ∈ contactOuterBox m p H (8 * K * H) (32 * K ^ 2 * H ^ 2))
    (hfloor : ∀ i ∈ S, ENNReal.ofReal (θ * H ^ 4) ≤ μ (E i)) :
    (S.card : ℝ) * θ ≤ 16384 * C * K ^ 3 := by
  have hupper := contact_box_measure_cap μ point (fun _ => True)
    hH hH1 hK hδ hδH hC hm hv hcenter (by simpa only [and_true] using hcap)
  apply witness_count_of_fourth_power_bound μ S E
    {ω | point ω ∈ contactOuterBox m p H (8 * K * H) (32 * K ^ 2 * H ^ 2)}
    hH hθ (mul_nonneg (mul_nonneg (by norm_num) hC) (pow_nonneg (by linarith) 3))
    hE hdisj hsub hfloor
  simpa only [and_true, mul_assoc] using hupper

end Submission.Obl.k4_horizontal_coefficient_count
