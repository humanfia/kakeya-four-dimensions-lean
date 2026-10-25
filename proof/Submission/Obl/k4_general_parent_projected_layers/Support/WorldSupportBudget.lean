/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/WorldSupportBudget.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.WeightedTerminalBudget
import Submission.Obl.k4_general_parent_projected_layers.Support.ProjectedWorlds
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Summing terminal lists by their original four coefficient codes. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

noncomputable section

def worldOfCodes (v z : ℤ) (e : ℤ × ℤ) : Fin 4 → ℤ := ![v, z, e.1, e.2]

theorem weighted_world_support_budget
    (Q : Finset (Fin 4 → ℤ)) (V : Finset ℤ) (I : ℤ → Finset ℤ)
    (G : ℤ → ℤ → Finset (ℤ × ℤ)) (w : ℤ → ℝ) (T : (Fin 4 → ℤ) → ℝ)
    {chi g q Cmajor Ccrop Carea : ℝ}
    (hc : 0 ≤ chi) (hg : 0 ≤ g) (hq : 0 ≤ q)
    (hCmajor : 0 ≤ Cmajor) (hCcrop : 0 ≤ Ccrop) (hCarea : 0 ≤ Carea)
    (hw : ∀ v, 0 ≤ w v) (hT : ∀ u, 0 ≤ T u) (hwsum : ∑ v ∈ V, w v ≤ 1)
    (hcompatible : ∀ u ∈ Q, u 0 ∈ V ∧ u 1 ∈ I (u 0) ∧ (u 2, u 3) ∈ G (u 0) (u 1))
    (hmajor : ∀ v ∈ V, ((I v).card : ℝ) * chi ≤ Cmajor * q)
    (hcrop : ∀ v ∈ V, ∀ z ∈ I v, ((G v z).card : ℝ) ≤ Ccrop)
    (harea : ∀ v ∈ V, ∀ z ∈ I v, ∀ e ∈ G v z, T (worldOfCodes v z e) ≤ Carea * q ^ 2) :
    (∑ u ∈ Q, (chi * g * w (u 0)) * T u) ≤ Cmajor * Ccrop * Carea * q ^ 3 * g := by
  classical
  let D := V.sigma (fun v => (I v).sigma (fun z => G v z))
  let encode (u : Fin 4 → ℤ) : Σ _v : ℤ, Σ _z : ℤ, ℤ × ℤ :=
    ⟨u 0, ⟨u 1, (u 2, u 3)⟩⟩
  let decode (d : Σ _v : ℤ, Σ _z : ℤ, ℤ × ℤ) : Fin 4 → ℤ :=
    worldOfCodes d.1 d.2.1 d.2.2
  have hdecode (u : Fin 4 → ℤ) : decode (encode u) = u := by
    ext i
    fin_cases i <;> rfl
  have hinj : Function.Injective encode := Function.LeftInverse.injective hdecode
  have hmaps : Q.image encode ⊆ D := by
    intro d hd
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hd
    simpa only [D, encode, Finset.mem_sigma] using hcompatible u hu
  have hsum : (∑ u ∈ Q, (chi * g * w (u 0)) * T u) ≤
      ∑ d ∈ D, (chi * g * w d.1) * T (decode d) := by
    apply Finset.sum_le_sum_of_injOn encode hinj.injOn hmaps
    · intro u hu
      simp only [encode, hdecode]
      exact le_rfl
    · intro d hd hnot
      exact mul_nonneg (mul_nonneg (mul_nonneg hc hg) (hw d.1)) (hT _)
  have hsum' : (∑ u ∈ Q, (chi * g * w (u 0)) * T u) ≤
      ∑ v ∈ V, ∑ z ∈ I v, ∑ e ∈ G v z,
        (chi * g * w v) * T (worldOfCodes v z e) := by
    simpa only [D, Finset.sum_sigma, decode] using hsum
  exact hsum'.trans (weighted_projected_support_budget V I G w
    (fun v z e => T (worldOfCodes v z e)) hc hg hq hCmajor hCcrop hCarea
    (fun v _ => hw v) hwsum hmajor hcrop harea)

theorem weighted_union_terminal_card {ι β γ : Type*} [Fintype ι] [DecidableEq γ]
    (Q : Finset β) (F : ι → β → Finset γ) (weight : β → ℝ)
    {sigma : ℝ} (hw : ∀ u ∈ Q, 0 ≤ weight u) :
    (∑ u ∈ Q, weight u * (((Finset.univ.biUnion (fun i => F i u)).card : ℝ) * sigma ^ 2)) ≤
      ∑ i, ∑ u ∈ Q, weight u * ((F i u).card * sigma ^ 2) := by
  classical
  calc
    _ ≤ ∑ u ∈ Q, weight u * ((∑ i, ((F i u).card : ℝ)) * sigma ^ 2) := by
      apply Finset.sum_le_sum
      intro u hu
      apply mul_le_mul_of_nonneg_left _ (hw u hu)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast Finset.card_biUnion_le
    _ = ∑ u ∈ Q, ∑ i, weight u * (((F i u).card : ℝ) * sigma ^ 2) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
    _ = _ := Finset.sum_comm

end

end Submission.Obl.k4_general_parent_projected_layers
