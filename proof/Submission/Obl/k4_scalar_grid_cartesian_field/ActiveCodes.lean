import Submission.Lib.K4SourceCellSelection

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory

/-- The actual positive-mass codes of the unchanged measure. -/
def activeCodes {Ω J : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (code : Ω → J) : Set J :=
  {q | μ {p | code p = q} ≠ 0}

/-- Later submeasures can only delete actual original active codes. -/
theorem activeCodes_mono {Ω J : Type*} [MeasurableSpace Ω] {μ ρ : Measure Ω}
    (hμ : μ ≤ ρ) (code : Ω → J) : activeCodes μ code ⊆ activeCodes ρ code := by
  intro q hq hz
  exact hq (le_antisymm ((hμ _).trans_eq hz) bot_le)

/-- Finite support counts survive every later restriction. -/
theorem active_count_mono {Ω J : Type*} [MeasurableSpace Ω] {μ ρ : Measure Ω}
    (hμ : μ ≤ ρ) (code : Ω → J) (hfinite : (activeCodes ρ code).Finite) :
    (activeCodes μ code).Finite ∧
      ((activeCodes μ code).ncard : ℝ) ≤ ((activeCodes ρ code).ncard : ℝ) := by
  have hs := activeCodes_mono hμ code
  exact ⟨hfinite.subset hs, by exact_mod_cast Set.ncard_le_ncard hs hfinite⟩

/-- Countably many null code cells can be removed together, without a pointwise support assumption. -/
theorem ae_active_code {Ω J : Type*} [MeasurableSpace Ω] [Countable J]
    (μ : Measure Ω) (code : Ω → J) : ∀ᵐ p ∂μ, code p ∈ activeCodes μ code := by
  classical
  rw [ae_iff]
  let Bad := {q : J // μ {p | code p = q} = 0}
  have hnull : μ (⋃ q : Bad, {p | code p = q.val}) = 0 :=
    measure_iUnion_null fun q => q.property
  apply measure_mono_null ?_ hnull
  intro p hp
  have hp' : μ {p' | code p' = code p} = 0 := by
    simpa only [activeCodes, mem_ofPred_eq, not_not] using hp
  exact mem_iUnion.mpr ⟨⟨code p, hp'⟩, rfl⟩

/-- An a.e. finite table covers every positive original code and bounds its actual support count. -/
theorem active_codes_finite_of_finite_support {Ω J : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (code : Ω → J) (F : Finset J) (hF : ∀ᵐ p ∂μ, code p ∈ F) :
    (activeCodes μ code).Finite ∧ (activeCodes μ code).ncard ≤ F.card := by
  classical
  have hsub : activeCodes μ code ⊆ (F : Set J) := by
    intro q hq
    have hmass : μ {p | code p = q ∧ (() : Unit) = ()} ≠ 0 := by simpa [activeCodes] using hq
    exact Submission.Lib.K4SourceCellSelection.cell_label_mem_of_nonzero_mass μ code
      (fun _ => ()) (fun _ => F) hF q () hmass
  refine ⟨F.finite_toSet.subset hsub, ?_⟩
  simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub F.finite_toSet

/-- Hereditary original cell counts survive arbitrary later submeasures and finite coarse localization. -/
theorem hereditary_active_code_count {Ω J J₀ : Type*} [MeasurableSpace Ω]
    (ρ μ : Measure Ω) (hμ : μ ≤ ρ) (fine : Ω → J) (coarse : Ω → J₀)
    (Q : Finset J₀) (hQ : ∀ᵐ p ∂μ, coarse p ∈ Q)
    (hfinite : ∀ q₀, {q | ρ {p | fine p = q ∧ coarse p = q₀} ≠ 0}.Finite)
    {R : ℝ}
    (hcount : ∀ q₀ ∈ Q, ({q | ρ {p | fine p = q ∧ coarse p = q₀} ≠ 0}.ncard : ℝ) ≤ R) :
    (activeCodes μ fine).Finite ∧
      ((activeCodes μ fine).ncard : ℝ) ≤ (Q.card : ℝ) * R := by
  classical
  let L : J₀ → Finset J := fun q₀ => (hfinite q₀).toFinset
  let F := Q.biUnion L
  have hcover : activeCodes μ fine ⊆ (F : Set J) := by
    intro q hq
    by_contra hout
    have hzero : ∀ q₀ ∈ Q, μ {p | fine p = q ∧ coarse p = q₀} = 0 := by
      intro q₀ hq₀
      have hρ : ρ {p | fine p = q ∧ coarse p = q₀} = 0 := by
        by_contra hn
        apply hout
        exact Finset.mem_biUnion.mpr ⟨q₀, hq₀, by simpa [L] using hn⟩
      apply le_antisymm ?_ bot_le
      exact (hμ _).trans_eq hρ
    have hsub : {p | fine p = q} ⊆ {p | coarse p ∉ Q} ∪
        ⋃ q₀ ∈ Q, {p | fine p = q ∧ coarse p = q₀} := by
      intro p hp
      by_cases hc : coarse p ∈ Q
      · exact Or.inr (mem_biUnion hc ⟨hp, rfl⟩)
      · exact Or.inl hc
    have hz : μ {p | fine p = q} = 0 := by
      apply le_antisymm ?_ bot_le
      calc
        _ ≤ μ ({p | coarse p ∉ Q} ∪ ⋃ q₀ ∈ Q, {p | fine p = q ∧ coarse p = q₀}) := measure_mono hsub
        _ ≤ μ {p | coarse p ∉ Q} +
            ∑ q₀ ∈ Q, μ {p | fine p = q ∧ coarse p = q₀} :=
          (measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _))
        _ = 0 := by rw [ae_iff] at hQ; simp only [hQ, Finset.sum_eq_zero hzero, add_zero]
    exact hq hz
  have hfin : (activeCodes μ fine).Finite := F.finite_toSet.subset hcover
  refine ⟨hfin, ?_⟩
  calc
    _ ≤ (F.card : ℝ) := by
      exact_mod_cast (show (activeCodes μ fine).ncard ≤ F.card by
        simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hcover F.finite_toSet)
    _ ≤ ∑ q₀ ∈ Q, ((L q₀).card : ℝ) := by
      exact_mod_cast (show F.card ≤ ∑ q₀ ∈ Q, (L q₀).card from Finset.card_biUnion_le)
    _ ≤ ∑ _q₀ ∈ Q, R := by
      apply Finset.sum_le_sum
      intro q₀ hq₀
      simpa only [L, ← Set.ncard_eq_toFinset_card _ (hfinite q₀)] using hcount q₀ hq₀
    _ = (Q.card : ℝ) * R := by simp

/-- Finite local decoders transfer active-code counts to any later observation. -/
theorem active_code_count_of_ae_decoder {Ω J K : Type*}
    [MeasurableSpace Ω] [Countable J]
    (μ : Measure Ω) (fine : Ω → J) (target : Ω → K)
    (hfinite : (activeCodes μ fine).Finite) (decode : J → Finset K)
    (hdecode : ∀ᵐ p ∂μ, target p ∈ decode (fine p)) {R : ℝ}
    (hcard : ∀ q ∈ activeCodes μ fine, ((decode q).card : ℝ) ≤ R) :
    (activeCodes μ target).Finite ∧
      ((activeCodes μ target).ncard : ℝ) ≤ R * ((activeCodes μ fine).ncard : ℝ) := by
  classical
  let Q := hfinite.toFinset
  let C := Q.biUnion decode
  have hsrc : ∀ᵐ p ∂μ, target p ∈ C := by
    filter_upwards [ae_active_code μ fine, hdecode] with p hp hpt
    exact Finset.mem_biUnion.mpr ⟨fine p, hfinite.mem_toFinset.mpr hp, hpt⟩
  obtain ⟨hfin, hnum⟩ := active_codes_finite_of_finite_support μ target C hsrc
  refine ⟨hfin, ?_⟩
  calc
    _ ≤ (C.card : ℝ) := by exact_mod_cast hnum
    _ ≤ ∑ q ∈ Q, ((decode q).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ Q, R := Finset.sum_le_sum fun q hq => hcard q (hfinite.mem_toFinset.mp hq)
    _ = R * ((activeCodes μ fine).ncard : ℝ) := by
      rw [Set.ncard_eq_toFinset_card _ hfinite]
      simp [Q, mul_comm]

end Submission.Obl.k4_scalar_grid_cartesian_field
