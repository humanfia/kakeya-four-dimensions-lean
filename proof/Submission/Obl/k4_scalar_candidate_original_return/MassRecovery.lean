import Submission.Obl.k4_scalar_candidate_original_return.OriginalRecovery
import Submission.Obl.k4_scalar_candidate_original_return.SelectedAtlas
import Submission.Obl.k4_scalar_normalized_exact_refinement.SparseMass
import Submission.Obl.k4_quadratic_atlas_normalization.MassSelection

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- An analytical original-observer list with polynomial path mass yields a
finite formatted selector with a comparable original union-mass floor. -/
theorem recover_original_union_mass {p : Code} (hp : Exact p) (k : ℕ)
    {m : ℕ} (B : ℕ) (hM : M p ≤ B) (hD : D p ≤ B)
    (hm : (m : ℝ) ≤ N p k ^ B) (γ : Fin m → Fin (W p k))
    (C : Fin m → Set Inc) (hC : ∀ i, MeasurableSet (C i))
    (hCsub : ∀ i, C i ⊆ E p k (γ i))
    (hCformat : ∀ i z, Format 6 (N p k ^ B) B
      {w | ((z, fun e : Fin 5 => w e.castSucc), w 5) ∈ C i})
    (δ : ℝ) (hδ : 0 < δ) (hδfine : δ⁻¹ ≤ N p k ^ B)
    (L : Fin (W p k) → (Base × ℤ) → Finset (Fin m))
    (hLmeas : ∀ a i, MeasurableSet {z | i ∈ L a z})
    (V : ℝ) (hV : 1 ≤ V) (hLcard : ∀ a z, ((L a z).card : ℝ) ≤ V)
    (hlower : ENNReal.ofReal V⁻¹ ≤ ∑ i, ENNReal.ofReal (ω p k (γ i)) *
      mu p k (γ i) {q | q ∈ C i ∧ i ∈ L (γ i) (originalObservation δ q)})
    (herror : (N p k)⁻¹ ≤ (2 * V)⁻¹) :
    ∃ Λ : Fin (W p k) → (Base × ℤ) → Finset (Fin m),
      (∀ a z, ((Λ a z).card : ℝ) ≤ 2 * V) ∧
      (∀ a i, MeasurableSet {z | i ∈ Λ a z}) ∧
      (∀ a i z, Format 6 (N p k ^ (36 * B + 102)) 3
        {w | i ∈ Λ a (originalObservation δ ((z, fun e : Fin 5 => w e.castSucc), w 5))}) ∧
      ENNReal.ofReal ((4 * V ^ 2)⁻¹) ≤
        ∑ a, ENNReal.ofReal (ω p k a) * mu p k a
          {q | ∃ i, γ i = a ∧ q ∈ selectedByLists γ C Λ δ i} := by
  classical
  let D := Nat.ceil V
  have hV0 : 0 < V := lt_of_lt_of_le zero_lt_one hV
  have hceil : (D : ℝ) ≤ 2 * V := by
    have hh := Nat.ceil_lt_add_one hV0.le
    dsimp [D]
    linarith
  have hcard : ∀ a z, (L a z).card ≤ D := by
    intro a z
    exact_mod_cast (hLcard a z).trans (Nat.le_ceil V)
  obtain ⟨table, htable, hmeas, hformat, hsuccess⟩ :=
    recover_formatted_original_lists hp k B hM hD hm γ C hC hCsub hCformat
      δ hδ hδfine L hLmeas hcard
  let ρ := (N p k ^ (11 * B + 30))⁻¹
  let F := originalRecordCodes (3 * N p k ^ B) ρ δ
  let Λ : Fin (W p k) → (Base × ℤ) → Finset (Fin m) :=
    fun a z => table a (observationMeshCode ρ F z)
  have hΛcard : ∀ a z, ((Λ a z).card : ℝ) ≤ 2 * V := by
    intro a z
    exact (Nat.cast_le.mpr (htable a _)).trans hceil
  have hΛmeas : ∀ a i, MeasurableSet {z | i ∈ Λ a z} := hmeas
  have hselected (i : Fin m) : MeasurableSet (selectedByLists γ C Λ δ i) :=
    (hC i).inter ((hΛmeas _ i).preimage (measurable_originalObservation _))
  have hretained : ENNReal.ofReal ((2 * V)⁻¹) ≤
      ∑ i, ENNReal.ofReal (ω p k (γ i)) * mu p k (γ i) (selectedByLists γ C Λ δ i) := by
    have hh := k4_quadratic_atlas_normalization.retain_half_mass _ _ _ V⁻¹
      (by positivity) hlower hsuccess
      (ENNReal.ofReal_le_ofReal (herror.trans_eq (by
        field_simp)))
    simpa only [selectedByLists, div_eq_mul_inv, mul_inv_rev, one_div] using hh
  have hunion := k4_scalar_normalized_exact_refinement.weighted_sparse_list_union_mass
    (mu p k) (fun a => ENNReal.ofReal (ω p k a)) γ
    (selectedByLists γ C Λ δ) hselected
    (fun a q => Λ a (originalObservation δ q)) (ENNReal.ofReal (2 * V))
    (fun a q => by
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hΛcard a _))
    (fun i => by
      apply measure_mono_null (t := ∅)
      · rintro q ⟨hq, hbad⟩
        exact hbad hq.2
      · exact measure_empty)
  refine ⟨Λ, hΛcard, hΛmeas, hformat, ?_⟩
  have hbound := hretained.trans hunion
  have hconst : ENNReal.ofReal ((4 * V ^ 2)⁻¹) =
      ENNReal.ofReal ((2 * V)⁻¹) / ENNReal.ofReal (2 * V) := by
    rw [← ENNReal.ofReal_div_of_pos (by positivity : 0 < 2 * V)]
    congr 1
    field_simp
    ring
  rw [hconst]
  exact (ENNReal.div_le_iff (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))
    ENNReal.ofReal_ne_top).mpr (by simpa only [mul_comm] using hbound)

end

end Submission.Obl.k4_scalar_candidate_original_return
