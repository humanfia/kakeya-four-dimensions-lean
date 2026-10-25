/-
Adapted from: here:o107 (session x0735), original-reference cap and
two-scale record helpers in Submission/Obl/k4_finite_narrowness_path_improvement/.
Accepted history-floor and mesh-cover proofs are imported.
-/
import Submission.Lib.K4ReferenceMeshPreparation.Menus

/-! One common restriction turns inherited history weights into caps
against the full original refined records. The restriction is chosen
before any member of an arbitrary family of test events is queried. -/

namespace Submission.Lib.K4ReferenceMeshPreparation

noncomputable section

open MeasureTheory Set MvPolynomial
open scoped ENNReal
open Submission.Lib.K4FinalLawSelection

/-- Restore all refined-record floors at once. Every original event
numerator then has a bound using the unchanged reference record mass.
The test family can contain all real velocity meshes simultaneously. -/
theorem exists_record_reference_restriction
    {Ω ι Λ : Type*} [MeasurableSpace Ω] [Fintype ι]
    (ν μ : Measure Ω) (hμ : μ ≤ ν)
    (H : ι → Set Ω) (hH : ∀ i, MeasurableSet (H i))
    (w : ι → ℝ≥0∞) (C δ : ℝ) (hδ : 0 < δ)
    (test : Λ → Set Ω) (β : Λ → ℝ≥0∞)
    (hnum : ∀ i t, μ (H i ∩ test t) ≤ ENNReal.ofReal C*w i*β t) :
    ∃ G : Set Ω, MeasurableSet G ∧
      μ Gᶜ ≤ ENNReal.ofReal δ*∑ i, w i ∧
      ∀ i t, (μ.restrict G) (H i ∩ test t) ≤
        ENNReal.ofReal (C/δ)*ν (H i)*β t := by
  classical
  obtain ⟨G,hG,hloss,hfloor⟩ := simultaneous_reference_floors Finset.univ H hH
    (fun i => ENNReal.ofReal δ*w i) μ
  refine ⟨G,hG,?_,?_⟩
  · simpa only [Finset.mul_sum] using hloss
  · intro i t
    rcases hfloor i (Finset.mem_univ i) with hz | hf
    · calc
        _ ≤ (μ.restrict G) (H i) := measure_mono inter_subset_left
        _ = 0 := hz
        _ ≤ _ := zero_le
    · have hw : w i ≤ (ENNReal.ofReal δ)⁻¹*ν (H i) := by
        calc
          w i = (ENNReal.ofReal δ)⁻¹*(ENNReal.ofReal δ*w i) := by
            rw [← mul_assoc,ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hδ).ne'
              ENNReal.ofReal_ne_top,one_mul]
          _ ≤ (ENNReal.ofReal δ)⁻¹*(μ.restrict G) (H i) := mul_le_mul' le_rfl hf
          _ ≤ _ := mul_le_mul' le_rfl ((Measure.restrict_le_self.trans hμ) _)
      calc
        _ ≤ μ (H i ∩ test t) := Measure.restrict_le_self _
        _ ≤ ENNReal.ofReal C*w i*β t := hnum i t
        _ ≤ ENNReal.ofReal C*((ENNReal.ofReal δ)⁻¹*ν (H i))*β t :=
          mul_le_mul' (mul_le_mul' le_rfl hw) le_rfl
        _ = _ := by rw [ENNReal.ofReal_div_of_pos hδ,div_eq_mul_inv]; ac_rfl

/-- Localized original graph/history records, inherited palette
numerators and one reference-floor pruning give every native E2 field.
The same measurable set serves every real mesh exponent and bin. -/
theorem native_caps_after_record_reference_pruning
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (N K C d S R L δ : ℝ) (hN : 1 < N) (hK : 0 ≤ K) (hC : 1 ≤ C)
    (hL : 0 ≤ L) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (ν μ : Measure Ω) (hμ : μ ≤ ν) (π : Measure ℝ)
    (x : Ω → Fin 4 → ℝ) (hx : Measurable x) (P : MvPolynomial (Fin 4) ℝ)
    (velocity : Ω → ℝ)
    (H : ι → Set Ω) (hH : ∀ i, MeasurableSet (H i))
    (hdisj : Pairwise (fun i j => AEDisjoint ν (H i) (H j)))
    (w : ι → ℝ≥0∞) (hcover : ∀ᵐ p ∂μ, ∃ i, p ∈ H i)
    (hdiam : ∀ i p, p ∈ H i → ∀ p', p' ∈ H i →
      (∀ j : Fin 3, |x p j.castSucc-x p' j.castSucc| ≤ L*N^(-R)) ∧
        |eval (x p) P-eval (x p') P| ≤ L*N^(-R))
    (hpure : ∀ r s, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R →
      ∀ q, ν {p | nativeSignalCell N r s x P p = q} ≤ ENNReal.ofReal (K*N^(-3*r-d*s)))
    (hpalette : ∀ v, R⁻¹ ≤ v → v ≤ R → ∀ z : ℤ,
      π {t | ⌊t/N^(-v)⌋ = z} ≤ ENNReal.ofReal (K*N^(-S*v)))
    (hrecord : ∀ v, R⁻¹ ≤ v → v ≤ R → ∀ i z,
      μ (H i ∩ {p | ⌊velocity p/N^(-v)⌋ = z}) ≤
        ENNReal.ofReal C*w i*π {t | ⌊t/N^(-v)⌋ = z}) :
    ∃ G : Set Ω, MeasurableSet G ∧
      μ Gᶜ ≤ ENNReal.ofReal δ*∑ i, w i ∧
      NativeCellCaps N ((C/δ)*(Nat.ceil ((4*L+6)^4) : ℝ)*K) d S R
        (μ.restrict G) π x P velocity := by
  let V := {v : ℝ // R⁻¹ ≤ v ∧ v ≤ R}
  let test : V × ℤ → Set Ω := fun t => {p | ⌊velocity p/N^(-t.1.1)⌋ = t.2}
  let β : V × ℤ → ℝ≥0∞ := fun t => π {a | ⌊a/N^(-t.1.1)⌋ = t.2}
  obtain ⟨G,hG,hloss,hcap⟩ := exists_record_reference_restriction ν μ hμ H hH w C δ hδ test β
    (fun i t => hrecord t.1.1 t.1.2.1 t.1.2.2 i t.2)
  have hCδ : 1 ≤ C/δ := (le_div_iff₀ hδ).mpr (by simpa using hδ1.trans hC)
  refine ⟨G,hG,hloss,?_⟩
  apply native_cell_caps_of_record_diameters N K (C/δ) d S R L hN hK hCδ hL
    ν (μ.restrict G) (Measure.restrict_le_self.trans hμ) π x hx P velocity H hH hdisj
    (fun i => ν (H i)) (fun _ => le_rfl)
    (hcover.filter_mono (ae_mono Measure.restrict_le_self)) hdiam hpure hpalette
  intro v hvl hvh i z
  exact hcap i (⟨v,hvl,hvh⟩,z)

end

end Submission.Lib.K4ReferenceMeshPreparation
