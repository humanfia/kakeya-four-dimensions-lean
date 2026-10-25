/-
Adapted from: here:o107 (session x0735), original-reference cap and
two-scale record helpers in Submission/Obl/k4_finite_narrowness_path_improvement/.
Accepted history-floor and mesh-cover proofs are imported.
-/
import Submission.Lib.K4FinalLawSelection

/-! Transfer fixed history/palette numerators to native mesh caps using
localization and the original reference law. This only needs discrete
cell caps of that law; every original palette factor is retained. -/

namespace Submission.Lib.K4ReferenceMeshPreparation

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4FinalLawSelection

/-- Disjoint original reference histories whose options contain a native
state fit in its padded region. Their unchanged weights therefore cost at
most the original reference mass of that region. -/
theorem history_state_weight_le_of_localization
    {Ω ι Q : Type*} [MeasurableSpace Ω] [Fintype ι]
    (ν : Measure Ω) (H : ι → Set Ω) (hH : ∀ i, MeasurableSet (H i))
    (hdisj : Pairwise (fun i j => AEDisjoint ν (H i) (H j)))
    (options : ι → Finset Q) (w : ι → ℝ≥0∞) (hw : ∀ i, w i ≤ ν (H i))
    (padding : Q → Set Ω)
    (hlocal : ∀ i q, q ∈ options i → H i ≤ᵐ[ν] padding q) (q : Q) :
    historyStateWeight options w q ≤ ν (padding q) := by
  classical
  let I := Finset.univ.filter (fun i => q ∈ options i)
  have hsum : ν (⋃ i ∈ I, H i) = ∑ i ∈ I, ν (H i) := by
    apply measure_biUnion_finset₀
    · intro i hi j hj hij
      exact hdisj hij
    · intro i hi
      exact (hH i).nullMeasurableSet
  have htrace : ∀ᵐ p ∂ν, ∀ i, q ∈ options i → p ∈ H i → p ∈ padding q := by
    apply ae_all_iff.mpr
    intro i
    by_cases hi : q ∈ options i
    · exact (hlocal i q hi).mono fun p hp _ => hp
    · exact Filter.Eventually.of_forall fun p hq => (hi hq).elim
  have hsub : (⋃ i ∈ I, H i) ≤ᵐ[ν] padding q := by
    filter_upwards [htrace] with p hp
    intro hpI
    simp only [mem_iUnion] at hpI
    obtain ⟨i,hi,hpi⟩ := hpI
    exact hp i (Finset.mem_filter.mp hi).2 hpi
  calc
    historyStateWeight options w q = ∑ i ∈ I, w i := by
      simp only [historyStateWeight,I,Finset.sum_filter]
    _ ≤ ∑ i ∈ I, ν (H i) := Finset.sum_le_sum (fun i hi => hw i)
    _ = ν (⋃ i ∈ I, H i) := hsum.symm
    _ ≤ ν (padding q) := measure_mono_ae hsub

/-- Fixed original history/palette ceilings and original reference
localization give a joint native-state ceiling against the SAME palette.
The retained incidence law is never normalized. -/
theorem localized_reference_palette_cap
    {Ω ι Q V : Type*} [MeasurableSpace Ω] [MeasurableSpace V] [Fintype ι]
    (ν μ : Measure Ω) (π : Measure V) (control : Ω → V) (state : Ω → Q)
    (H : ι → Set Ω) (hH : ∀ i, MeasurableSet (H i))
    (hdisj : Pairwise (fun i j => AEDisjoint ν (H i) (H j)))
    (options : ι → Finset Q) (w : ι → ℝ≥0∞) (hw : ∀ i, w i ≤ ν (H i))
    (padding : Q → Set Ω)
    (hlocal : ∀ i q, q ∈ options i → H i ≤ᵐ[ν] padding q)
    (C : ℝ≥0∞)
    (hcover : ∀ᵐ p ∂μ, ∃ i, p ∈ H i)
    (hoptions : ∀ i, ∀ᵐ p ∂μ, p ∈ H i → state p ∈ options i)
    (hcap : ∀ i (A : Set V), MeasurableSet A →
      μ {p | p ∈ H i ∧ control p ∈ A} ≤ C*w i*π A) :
    ∀ q (A : Set V), MeasurableSet A →
      μ {p | state p = q ∧ control p ∈ A} ≤ C*ν (padding q)*π A := by
  intro q A hA
  exact (native_state_palette_cap μ π control state H options w C hcover hoptions hcap q A hA).trans
    (mul_le_mul' (mul_le_mul' le_rfl
      (history_state_weight_le_of_localization ν H hH hdisj options w hw padding hlocal q)) le_rfl)

/-- The localized reference region may be only a bounded menu of mesh
cells. Original discrete pure caps suffice for the joint ceiling; a
continuous conditional density ceiling is not required. -/
theorem localized_reference_mesh_palette_cap
    {Ω ι Q R V : Type*} [MeasurableSpace Ω] [MeasurableSpace V] [Fintype ι]
    (ν μ : Measure Ω) (π : Measure V) (control : Ω → V) (state : Ω → Q)
    (H : ι → Set Ω) (hH : ∀ i, MeasurableSet (H i))
    (hdisj : Pairwise (fun i j => AEDisjoint ν (H i) (H j)))
    (options : ι → Finset Q) (w : ι → ℝ≥0∞) (hw : ∀ i, w i ≤ ν (H i))
    (cell : Ω → R) (paddingCells : Q → Finset R) (M : ℕ)
    (hcard : ∀ q, (paddingCells q).card ≤ M)
    (hlocal : ∀ i q, q ∈ options i → H i ≤ᵐ[ν] {p | cell p ∈ paddingCells q})
    (B : ℝ≥0∞) (hpure : ∀ r, ν {p | cell p = r} ≤ B)
    (C : ℝ≥0∞)
    (hcover : ∀ᵐ p ∂μ, ∃ i, p ∈ H i)
    (hoptions : ∀ i, ∀ᵐ p ∂μ, p ∈ H i → state p ∈ options i)
    (hcap : ∀ i (A : Set V), MeasurableSet A →
      μ {p | p ∈ H i ∧ control p ∈ A} ≤ C*w i*π A) :
    ∀ q (A : Set V), MeasurableSet A →
      μ {p | state p = q ∧ control p ∈ A} ≤ C*(M : ℝ≥0∞)*B*π A := by
  classical
  let padding := fun q => {p | cell p ∈ paddingCells q}
  have hpad (q : Q) : ν (padding q) ≤ (M : ℝ≥0∞)*B := by
    have hset : padding q = ⋃ r ∈ paddingCells q, {p | cell p = r} := by
      ext p
      simp only [padding,mem_ofPred_eq,mem_iUnion]
      constructor
      · intro hp
        exact ⟨cell p,hp,rfl⟩
      · rintro ⟨r,hr,hpr⟩
        rwa [hpr]
    rw [hset]
    calc
      _ ≤ ∑ r ∈ paddingCells q, ν {p | cell p = r} := measure_biUnion_finset_le _ _
      _ ≤ ∑ _r ∈ paddingCells q, B := Finset.sum_le_sum (fun r hr => hpure r)
      _ = ((paddingCells q).card : ℝ≥0∞)*B := by simp
      _ ≤ (M : ℝ≥0∞)*B := mul_le_mul' (by exact_mod_cast hcard q) le_rfl
  intro q A hA
  calc
    _ ≤ C*ν (padding q)*π A :=
      localized_reference_palette_cap ν μ π control state H hH hdisj options w hw padding
        hlocal C hcover hoptions hcap q A hA
    _ ≤ C*((M : ℝ≥0∞)*B)*π A := mul_le_mul' (mul_le_mul' le_rfl (hpad q)) le_rfl
    _ = _ := by ring

/-- A single original event (for example one velocity bin) suffices. The
factor `β` is carried through the original restriction without any
positivity, density or normalization condition on that event. -/
theorem localized_reference_mesh_event_cap
    {Ω ι Q R : Type*} [MeasurableSpace Ω] [Fintype ι]
    (ν μ : Measure Ω) (state : Ω → Q) (hstate : ∀ q, MeasurableSet {p | state p = q})
    (H : ι → Set Ω) (hH : ∀ i, MeasurableSet (H i))
    (hdisj : Pairwise (fun i j => AEDisjoint ν (H i) (H j)))
    (options : ι → Finset Q) (w : ι → ℝ≥0∞) (hw : ∀ i, w i ≤ ν (H i))
    (cell : Ω → R) (paddingCells : Q → Finset R) (M : ℕ)
    (hcard : ∀ q, (paddingCells q).card ≤ M)
    (hlocal : ∀ i q, q ∈ options i → H i ≤ᵐ[ν] {p | cell p ∈ paddingCells q})
    (B : ℝ≥0∞) (hpure : ∀ r, ν {p | cell p = r} ≤ B)
    (C β : ℝ≥0∞) (A : Set Ω)
    (hcover : ∀ᵐ p ∂μ, ∃ i, p ∈ H i)
    (hoptions : ∀ i, ∀ᵐ p ∂μ, p ∈ H i → state p ∈ options i)
    (hcap : ∀ i, μ (H i ∩ A) ≤ C*w i*β) :
    ∀ q, μ ({p | state p = q} ∩ A) ≤ C*(M : ℝ≥0∞)*B*β := by
  let π : Measure ℝ := β • Measure.dirac (0 : ℝ)
  have hc (i : ι) (S : Set ℝ) (hS : MeasurableSet S) :
      (μ.restrict A) {p | p ∈ H i ∧ (0 : ℝ) ∈ S} ≤ C*w i*π S := by
    by_cases h0 : (0 : ℝ) ∈ S
    · have heq : {p | p ∈ H i ∧ (0 : ℝ) ∈ S} = H i := by ext p; simp [h0]
      rw [heq,Measure.restrict_apply (hH i)]
      simpa [π,Measure.smul_apply,hS,h0] using hcap i
    · simp [h0]
  intro q
  have hh := localized_reference_mesh_palette_cap ν (μ.restrict A) π (fun _ => (0 : ℝ)) state
    H hH hdisj options w hw cell paddingCells M hcard hlocal B hpure C
    (ae_restrict_of_ae hcover) (fun i => ae_restrict_of_ae (hoptions i)) hc q univ MeasurableSet.univ
  simpa only [mem_univ,and_true,Measure.restrict_apply (hstate q),π,Measure.smul_apply,
    measure_univ,smul_eq_mul,mul_one] using hh

end

end Submission.Lib.K4ReferenceMeshPreparation
