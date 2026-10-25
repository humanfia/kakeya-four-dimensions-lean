-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.FrozenRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.FrozenBridge

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory Set
open scoped ENNReal

/-- The common fine level recorded in the grain configuration. -/
theorem uniform_fine_of_G {ω δ h : ℝ} {n N : ℕ} {x v : Fin n → V}
    {Y Z : Fin n → Set V} {S : Finset (Fin n)} {ρ : ℝ}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hG : G ω δ h n x v Y S Z ρ N y w f) : UF n S Z N f := by
  obtain ⟨a, c, L, z, e, H, γ, m, hgrain⟩ := hG.2.2.2
  exact ⟨m, hgrain.2.2.2.2.2.2.2.2.1⟩

/-- A grain refinement with a pointwise packet count gives the frozen medium
certificate. The mass budget includes both the original cover loss and the
factor-two loss in transferring through the common fine level. -/
theorem medium_certificate_of_grain_refinement
    {σ ω δ h ε ρ b Cm t : ℝ} {n N L Jn : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N} {U : Finset (Fin N)}
    {g : Fin N → Fin Jn} {γ : Fin L → Fin N} {H H' : Fin L → Set V}
    (hC : C δ h n x v Y S Z ρ N y w f) (hUF : UF n S Z N f)
    (ht : 0 ≤ t) (hbudget : O (δ ^ ε) ≤ O (t / 2) * O (δ ^ h))
    (hHm : ∀ j, M (H j)) (hH'm : ∀ j, M (H' j))
    (hH'H : ∀ j, H' j ⊆ H j)
    (hdisj : ∀ j j', j ≠ j' → γ j = γ j' → Disjoint (H j) (H j'))
    (hfib : ∀ k, assignedFiber γ H k = {p | ∃ i ∈ S, f i = k ∧ p ∈ Z i})
    (hretain : O t * ∑ j, μ (H j) ≤ ∑ j, μ (H' j))
    (hsupport : ∀ j, γ j ∉ U → H' j = ∅)
    (hcount : ∀ p j,
      q L {l | γ l ∈ U ∧ g (γ l) = j ∧ p ∈ H' l} ≤
        Cm * δ ^ (-ε) * (ρ / b) ^ (-ω - σ)) :
    ∃ W : Fin n → Set V, MR σ ω δ ε ρ b Cm n N Jn Y Z W S U f g := by
  classical
  have hZsupport : ∀ i, i ∉ S → Z i = ∅ := fun i => (hC.1 i).2.2
  obtain ⟨m, hm, hlevel⟩ := fine_level_of_UF hZsupport hUF
  have hfib' : ∀ k, assignedFiber γ H k = assignedFiber f Z k := by
    intro k
    rw [assignedFiber_eq_supported f hZsupport k]
    exact hfib k
  obtain ⟨W, hW, hmass, hWfib⟩ := grain_refinement_transfer f γ Z H H' hm ht
    (fun i => (hC.1 i).1) hHm hH'm hH'H hdisj hfib' hlevel hretain
  have hWS : ∀ i, i ∉ S → W i = ∅ := by
    intro i hi
    exact Set.eq_empty_iff_forall_notMem.mpr fun p hp => by
      have hz := (hW i).2 hp
      simpa only [hZsupport i hi, Set.mem_empty_iff_false] using hz
  have hWU : ∀ i, f i ∉ U → W i = ∅ := by
    intro i hi
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hf : p ∈ assignedFiber f W (f i) := ⟨i, rfl, hp⟩
    rw [hWfib] at hf
    obtain ⟨j, hj, hpj⟩ := hf
    have hjU : γ j ∉ U := by simpa only [hj] using hi
    simpa only [hsupport j hjU, Set.mem_empty_iff_false] using hpj
  have hZsum : ∑ i ∈ S, μ (Z i) = ∑ i, μ (Z i) := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro i _ hi
    simp [hZsupport i hi]
  have hH'disj : ∀ i j, i ≠ j → γ i = γ j → Disjoint (H' i) (H' j) :=
    fun i j hij hγ => (hdisj i j hij hγ).mono (hH'H i) (hH'H j)
  refine ⟨W, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hW i).1, (hW i).2, fun hi => hi.elim (hWS i) (hWU i)⟩
  · calc
      O (δ ^ ε) * ∑ i, μ (Y i) ≤ (O (t / 2) * O (δ ^ h)) * ∑ i, μ (Y i) :=
        mul_le_mul' hbudget le_rfl
      _ = O (t / 2) * (O (δ ^ h) * ∑ i, μ (Y i)) := mul_assoc _ _ _
      _ ≤ O (t / 2) * ∑ i ∈ S, μ (Z i) := mul_le_mul' le_rfl hC.2.1
      _ = O (t / 2) * ∑ i, μ (Z i) := by rw [hZsum]
      _ ≤ ∑ i, μ (W i) := hmass
  · intro p j
    have hsets : {k : Fin N | k ∈ U ∧ g k = j ∧ ∃ i ∈ S, f i = k ∧ p ∈ W i} =
        {k : Fin N | (k ∈ U ∧ g k = j) ∧ p ∈ assignedFiber γ H' k} := by
      ext k
      simp only [mem_setOf_eq]
      rw [← hWfib k, assignedFiber_eq_supported f hWS k]
      simp only [mem_setOf_eq, and_assoc]
    change ({k : Fin N | k ∈ U ∧ g k = j ∧ ∃ i ∈ S, f i = k ∧ p ∈ W i}.ncard : ℝ) ≤ _
    rw [hsets, active_fiber_ncard γ H' hH'disj]
    simpa only [q, and_assoc] using hcount p j

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
