import Submission.Obl.k4_scalar_candidate_original_return.OriginalSource
import Submission.Obl.k4_scalar_candidate_original_return.FiniteRecovery
import Submission.Obl.k4_scalar_candidate_original_return.EncodingBudget

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4ModelReduction

noncomputable section

/-- Every measurable list on formatted selected original pieces can be replaced
by an actual finite terminal-observer table. The original error is at most 1/N,
its degree is three, and its format exponent is linear in the input budget. -/
theorem recover_formatted_original_lists {p : Code} (hp : Exact p) (k : ℕ)
    {m Dₗ : ℕ} (B : ℕ) (hM : M p ≤ B) (hD : D p ≤ B)
    (hm : (m : ℝ) ≤ N p k ^ B) (γ : Fin m → Fin (W p k))
    (C : Fin m → Set Inc) (hC : ∀ i, MeasurableSet (C i))
    (hCsub : ∀ i, C i ⊆ E p k (γ i))
    (hCformat : ∀ i z, Format 6 (N p k ^ B) B
      {w | ((z, fun e : Fin 5 => w e.castSucc), w 5) ∈ C i})
    (δ : ℝ) (hδ : 0 < δ) (hδfine : δ⁻¹ ≤ N p k ^ B)
    (L : Fin (W p k) → (Base × ℤ) → Finset (Fin m))
    (hLmeas : ∀ a i, MeasurableSet {z | i ∈ L a z})
    (hLcard : ∀ a z, (L a z).card ≤ Dₗ) :
    let ρ := (N p k ^ (11 * B + 30))⁻¹
    let F := originalRecordCodes (3 * N p k ^ B) ρ δ
    ∃ table : Fin (W p k) → Option F → Finset (Fin m),
      (∀ a c, (table a c).card ≤ Dₗ) ∧
      (∀ a i, MeasurableSet {z | i ∈ table a (observationMeshCode ρ F z)}) ∧
      (∀ a i z, Format 6 (N p k ^ (36 * B + 102)) 3
        {w | i ∈ table a (observationMeshCode ρ F
          (originalObservation δ ((z, fun e : Fin 5 => w e.castSucc), w 5)))}) ∧
      (∑ i, ENNReal.ofReal (ω p k (γ i)) * mu p k (γ i)
        {q | q ∈ C i ∧ i ∈ L (γ i) (originalObservation δ q)}) ≤
      (∑ i, ENNReal.ofReal (ω p k (γ i)) * mu p k (γ i)
        {q | q ∈ C i ∧ i ∈ table (γ i) (observationMeshCode ρ F (originalObservation δ q))}) +
        ENNReal.ofReal ((N p k)⁻¹) := by
  classical
  let n := N p k
  have hn : 2 ≤ n := hp.1.1 k
  have hn0 : 0 < n := by linarith
  have hn1 : 1 ≤ n := by linarith
  let U := n ^ B
  have hU : 0 < U := pow_pos hn0 _
  let J := 11 * B + 30
  let ρ := (n ^ J)⁻¹
  have hρ : 0 < ρ := inv_pos.mpr (pow_pos hn0 _)
  let F := originalRecordCodes (3 * U) ρ δ
  let src : (i : Fin m) → SourceCertificate (ν p k (γ i)) (C i)
      (n ^ (2 * B)) (3 * U) (2 * n ^ (2 * B)) (3 * B) :=
    fun i => Classical.choice (original_source_certificate hp k (γ i) B hM hD
      (C i) (hC i) (hCsub i) (hCformat i))
  choose g hg0 hgmass hgcell hgsupport hgerror using
    fun i => (src i).flatten (by positivity : 0 ≤ 3 * U) hρ
  let f : Fin m → (Fin 6 → ℝ) → ℝ := fun i => (src i).density
  have hsource (i : Fin m) :
      ((mu p k (γ i)).restrict (C i)).map fullSourceCoordinates =
        volume.withDensity (fun w => ENNReal.ofReal (f i w)) := by
    change ((((ν p k (γ i)).prod volume).restrict (E p k (γ i))).restrict (C i)).map
      fullSourceCoordinates = _
    rw [Measure.restrict_restrict_of_subset (hCsub i)]
    exact (src i).law
  obtain ⟨table, hcard, hmeas, hformat, hsuccess⟩ := recover_finite_original_scalar_lists
    (ω p k) (k4_scalar_true_atlas_terminal_lists.Exact.weight_nonneg hp k)
    (k4_scalar_true_atlas_terminal_lists.Exact.weight_sum hp k) γ (3 * U) δ ρ hδ hρ
    (fun i => mu p k (γ i)) C f (fun i => (g i).val)
    (fun i => (src i).measurable) (fun i => (g i).property.1)
    (fun i => (src i).integrable) (fun i => (src i).support)
    (fun i => (src i).nonneg) hg0 hsource hgcell Dₗ L hLmeas hLcard
  have hδJ : δ⁻¹ ≤ n ^ J := hδfine.trans (pow_le_pow_right₀ hn1 (by dsimp [J]; omega))
  have hlookup : 6 * (F.card : ℝ) + 1 ≤ n ^ (36 * B + 102) := by
    have hh := original_lookup_format_budget hn hδ B J hδJ
    have hJ : 3 * (B + J) + 12 = 36 * B + 102 := by dsimp [J]; omega
    rw [hJ] at hh
    exact hh
  have he0 : 0 ≤ 16 * n ^ (2 * B) * (2 * n ^ (2 * B)) * (3 * B : ℕ) *
      ρ * (2 * (3 * U)) ^ 5 := by positivity
  have herr : 2 * ∑ i, densityL1Distance volume (g i).val (f i) ≤ ENNReal.ofReal n⁻¹ := by
    let e : ℝ := 16 * n ^ (2 * B) * (2 * n ^ (2 * B)) * (3 * B : ℕ) *
      ρ * (2 * (3 * U)) ^ 5
    have he : 0 ≤ e := he0
    calc
      _ ≤ 2 * ∑ _i : Fin m, ENNReal.ofReal e :=
        mul_le_mul_right (Finset.sum_le_sum (fun i _ => hgerror i)) 2
      _ = ENNReal.ofReal (2 * (m : ℝ) * e) := by
        simp [ENNReal.ofReal_mul, nsmul_eq_mul, mul_assoc]
      _ ≤ ENNReal.ofReal (2 * U * e) := by
        apply ENNReal.ofReal_le_ofReal
        gcongr
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hnum := scalar_recovery_mesh_error hn hU hU B (nat_budget_le_power hn B)
        have hsq : U ^ 2 = n ^ (2 * B) := by
          dsimp [U]
          rw [← pow_mul]
          congr 1
          omega
        have hden : U ^ 8 * U ^ 3 * n ^ 30 = n ^ J := by
          have hh := source_mesh_denominator n B B
          have hJ : 8 * B + 3 * B + 30 = J := by dsimp [J]; omega
          rw [hJ] at hh
          exact hh
        have hterm : 2 * U * e =
            2 * U * (16 * U ^ 2 * (2 * U * U) * (3 * (B : ℝ)) *
              (U ^ 8 * U ^ 3 * n ^ 30)⁻¹ * (2 * (3 * U)) ^ 5) := by
          dsimp [e]
          rw [hsq, hden]
          simp only [ρ, Nat.cast_mul, Nat.cast_ofNat]
          have hmul : U * U = n ^ (2 * B) := by simpa only [pow_two] using hsq
          rw [mul_assoc 2 U U, hmul]
        rw [hterm]
        exact hnum
  refine ⟨table, hcard, hmeas, ?_, ?_⟩
  · intro a i z
    exact k4_scalar_true_atlas_terminal_lists.Format.mono (hformat a i z) hlookup le_rfl
  · exact hsuccess.trans (add_le_add le_rfl herr)

end

end Submission.Obl.k4_scalar_candidate_original_return
