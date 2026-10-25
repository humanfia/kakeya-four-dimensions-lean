import Submission.Obl.k4_scalar_pair_atlas_assembly.Interface
import Submission.Obl.k4_scalar_conditional_crop_worlds.SignFormat
import Submission.Obl.k4_scalar_conditional_crop_worlds.FormatLemmas
set_option autoImplicit false
namespace Submission.Obl.k4_scalar_pair_atlas_assembly
open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
noncomputable section

lemma format_coord_preimage {n m D : ℕ} {B : ℝ} {S : Set (Fin n → ℝ)}
    (hB : 1 ≤ B) (hS : Format n B D S) (f : Fin n → Fin m) :
    Format m B D {z | (fun i => z (f i)) ∈ S} := by
  obtain ⟨k, hk, p, hp, T, hT⟩ := hS
  apply k4_scalar_conditional_crop_worlds.format_of_signRep hB hk
  refine ⟨fun i => rename f (p i), T, fun i =>
    (totalDegree_rename_le f (p i)).trans (hp i).1, ?_⟩
  intro z
  simp only [id_eq, eval_rename]
  have hh := Set.ext_iff.mp hT (fun i => z (f i))
  exact hh.symm

lemma format_selected_union {n D m : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (A : Fin m → Set (Fin n → ℝ)) (hA : ∀ i, Format n B D (A i))
    (select : Fin m → Prop) :
    Format n (m * B) D {z | ∃ i, select i ∧ z ∈ A i} := by
  classical
  let A' : Fin m → Set (Fin n → ℝ) := fun i => if select i then A i else ∅
  have hh (i) : Format n B D (A' i) := by
    dsimp [A']
    split_ifs
    · exact hA i
    · exact k4_scalar_conditional_crop_worlds.Format.empty _ hB _
  have h := k4_scalar_conditional_crop_worlds.Format.iUnion_fin hB m A' hh
  apply k4_scalar_conditional_crop_worlds.Format.congr h
  ext z
  simp [A']

end
end Submission.Obl.k4_scalar_pair_atlas_assembly
