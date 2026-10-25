/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarFinalization/FiniteBinChoice.lean at 34bf057964440b5ed25e8d148b45315a2683e87d.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit4d8af73c,
Submission/Obl/k4_scalar_mesh_projection/FiniteBinChoice.lean.
Generic prerequisites retain their own accepted-source credits in Pruning.lean.
-/

import Mathlib

namespace Submission.Lib.K4ScalarCoreTools.Finalization

open Set MeasureTheory
open scoped ENNReal

theorem exists_finite_list_mass_choice {I B : Type*}
    (L : I → Finset B) (hne : ∀ i, (L i).Nonempty) (w : I → B → ℝ≥0∞) :
    ∃ choice : I → B, ∀ i, choice i ∈ L i ∧
      (∑ b ∈ L i, w i b) ≤ ((L i).card : ℝ≥0∞) * w i (choice i) := by
  classical
  have hmax (i : I) : ∃ b ∈ L i, ∀ b' ∈ L i, w i b' ≤ w i b :=
    Finset.exists_max_image (L i) (w i) (hne i)
  choose choice hmem hmax using hmax
  refine ⟨choice, fun i => ⟨hmem i, ?_⟩⟩
  calc
    _ ≤ ∑ _b ∈ L i, w i (choice i) := Finset.sum_le_sum fun b hb => hmax i b hb
    _ = _ := by simp [nsmul_eq_mul]

theorem measure_eq_sum_observation_fibers {Ω I : Type*}
    [MeasurableSpace Ω] [Fintype I] (μ : Measure Ω)
    (obs : Ω → I) (hobs : ∀ i, MeasurableSet {x | obs x = i})
    (S : Set Ω) : μ S = ∑ i, μ (S ∩ {x | obs x = i}) := by
  classical
  have h := sum_measure_preimage_singleton (μ := μ.restrict S) (f := obs) Finset.univ
    (fun i _ => hobs i)
  simp only [Finset.coe_univ, preimage_univ, Measure.restrict_apply_univ] at h
  have hi (i : I) : (μ.restrict S) (obs ⁻¹' {i}) = μ (S ∩ {x | obs x = i}) := by
    have hm : MeasurableSet (obs ⁻¹' {i}) := by
      convert hobs i using 1
      ext x
      simp
    rw [Measure.restrict_apply hm]
    congr 1
    ext x
    simp [and_comm]
  simpa only [hi] using h.symm

/-- A bin is fixed separately at each observation. Its loss is the local
list size, with the original measure of the full discovery set. -/
theorem exists_original_observation_bin_choice {Ω I B : Type*}
    [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (E : Set Ω) (hE : MeasurableSet E)
    (obs : Ω → I) (hobs : ∀ i, MeasurableSet {x | obs x = i})
    (label : Ω → B) (hlabel : ∀ b, MeasurableSet {x | label x = b})
    (L : I → Finset B) (hne : ∀ i, (L i).Nonempty)
    (hknown : ∀ x ∈ E, label x ∈ L (obs x))
    (K : ℝ≥0∞) (hcard : ∀ i, ((L i).card : ℝ≥0∞) ≤ K) :
    ∃ choice : I → B, (∀ i, choice i ∈ L i) ∧
      MeasurableSet {x | x ∈ E ∧ label x = choice (obs x)} ∧
      μ E ≤ K * μ {x | x ∈ E ∧ label x = choice (obs x)} := by
  classical
  let S : I → Set Ω := fun i => E ∩ {x | obs x = i}
  let G : I → B → Set Ω := fun i b => S i ∩ {x | label x = b}
  obtain ⟨choice, hc⟩ := exists_finite_list_mass_choice L hne (fun i b => μ (G i b))
  have hcover (i : I) : S i ⊆ ⋃ b ∈ L i, G i b := by
    intro x hx
    have hmem : label x ∈ L i := by
      have h := hknown x hx.1
      have hxi : obs x = i := hx.2
      rwa [hxi] at h
    exact mem_iUnion.mpr ⟨label x, mem_iUnion.mpr ⟨hmem, hx, rfl⟩⟩
  have hrow (i : I) : μ (S i) ≤ K * μ (G i (choice i)) := by
    calc
      _ ≤ μ (⋃ b ∈ L i, G i b) := measure_mono (hcover i)
      _ ≤ ∑ b ∈ L i, μ (G i b) := measure_biUnion_finset_le _ _
      _ ≤ ((L i).card : ℝ≥0∞) * μ (G i (choice i)) := (hc i).2
      _ ≤ K * μ (G i (choice i)) := mul_le_mul' (hcard i) le_rfl
  let T : Set Ω := {x | x ∈ E ∧ label x = choice (obs x)}
  have hTunion : T = ⋃ i, G i (choice i) := by
    ext x
    constructor
    · intro hx
      exact mem_iUnion.mpr ⟨obs x, ⟨hx.1, rfl⟩, hx.2⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      have hxi : obs x = i := hi.1.2
      have hxl : label x = choice i := hi.2
      exact ⟨hi.1.1, by simpa only [hxi] using hxl⟩
  have hTm : MeasurableSet T := by
    rw [hTunion]
    exact MeasurableSet.iUnion fun i => (hE.inter (hobs i)).inter (hlabel (choice i))
  refine ⟨choice, fun i => (hc i).1, hTm, ?_⟩
  rw [measure_eq_sum_observation_fibers μ obs hobs E]
  change (∑ i, μ (S i)) ≤ K * μ T
  calc
    _ ≤ ∑ i, K * μ (G i (choice i)) := Finset.sum_le_sum fun i _ => hrow i
    _ = K * ∑ i, μ (G i (choice i)) := (Finset.mul_sum ..).symm
    _ = K * μ T := by
      rw [measure_eq_sum_observation_fibers μ obs hobs T]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      ext x
      simp only [G, S, T, mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨⟨hxE, hxobs⟩, hxlab⟩
        exact ⟨⟨hxE, by simpa only [hxobs] using hxlab⟩, hxobs⟩
      · rintro ⟨⟨hxE, hxlab⟩, hxobs⟩
        exact ⟨⟨hxE, hxobs⟩, by simpa only [hxobs] using hxlab⟩

/-- Several observation-dependent tests are fixed successively on the
same original incidence law. The cost is one local list factor per
test, independently of the number of observation cells. -/
theorem exists_original_observation_bin_choices {Ω I B : Type*}
    [MeasurableSpace Ω] [Fintype I] (μ : Measure Ω) (K : ℝ≥0∞) (n : ℕ) :
    ∀ (E : Set Ω), MeasurableSet E →
    ∀ (obs : Fin n → Ω → I), (∀ j i, MeasurableSet {x | obs j x = i}) →
    ∀ (label : Fin n → Ω → B), (∀ j b, MeasurableSet {x | label j x = b}) →
    ∀ (L : Fin n → I → Finset B), (∀ j i, (L j i).Nonempty) →
    (∀ j, ∀ x ∈ E, label j x ∈ L j (obs j x)) →
    (∀ j i, ((L j i).card : ℝ≥0∞) ≤ K) →
    ∃ choice : Fin n → I → B, (∀ j i, choice j i ∈ L j i) ∧
      MeasurableSet {x | x ∈ E ∧ ∀ j, label j x = choice j (obs j x)} ∧
      μ E ≤ K^n * μ {x | x ∈ E ∧ ∀ j, label j x = choice j (obs j x)} := by
  classical
  induction n with
  | zero =>
    intro E hE obs hobs label hlabel L hne hknown hcard
    refine ⟨(fun j => Fin.elim0 j), (fun j => Fin.elim0 j), ?_, ?_⟩
    · convert hE using 1
      ext x
      simp only [mem_ofPred_eq, Fin.forall_fin_zero, and_true]
    · simp only [pow_zero, one_mul]
      apply le_of_eq
      congr 1
      ext x
      simp only [mem_ofPred_eq, Fin.forall_fin_zero, and_true]
  | succ n ih =>
    intro E hE obs hobs label hlabel L hne hknown hcard
    obtain ⟨first, hfirst, hfirstm, hmass⟩ := ih E hE
      (fun j => obs j.castSucc) (fun j => hobs j.castSucc)
      (fun j => label j.castSucc) (fun j => hlabel j.castSucc)
      (fun j => L j.castSucc) (fun j => hne j.castSucc)
      (fun j => hknown j.castSucc) (fun j => hcard j.castSucc)
    let E₀ := {x | x ∈ E ∧ ∀ j : Fin n, label j.castSucc x = first j (obs j.castSucc x)}
    obtain ⟨last, hlast, hlastm, hmasslast⟩ := exists_original_observation_bin_choice
      μ E₀ hfirstm (obs (Fin.last n)) (hobs (Fin.last n))
      (label (Fin.last n)) (hlabel (Fin.last n)) (L (Fin.last n)) (hne (Fin.last n))
      (fun x hx => hknown (Fin.last n) x hx.1) K (hcard (Fin.last n))
    let choice : Fin (n+1) → I → B := Fin.snoc first last
    have hchoice : ∀ j i, choice j i ∈ L j i := by
      intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa only [choice, Fin.snoc_last] using hlast
      · simpa only [choice, Fin.snoc_castSucc] using hfirst j
    have heq : {x | x ∈ E ∧ ∀ j, label j x = choice j (obs j x)} =
        {x | x ∈ E₀ ∧ label (Fin.last n) x = last (obs (Fin.last n) x)} := by
      ext x
      simp only [mem_ofPred_eq, E₀, Fin.forall_iff_castSucc, choice,
        Fin.snoc_castSucc, Fin.snoc_last]
      tauto
    refine ⟨choice, hchoice, by simpa only [heq] using hlastm, ?_⟩
    rw [heq, pow_succ]
    exact hmass.trans (by
      calc
        K^n * μ E₀ ≤ K^n * (K * μ {x | x ∈ E₀ ∧
            label (Fin.last n) x = last (obs (Fin.last n) x)}) :=
          mul_le_mul' le_rfl hmasslast
        _ = _ := by ring)

end Submission.Lib.K4ScalarCoreTools.Finalization
