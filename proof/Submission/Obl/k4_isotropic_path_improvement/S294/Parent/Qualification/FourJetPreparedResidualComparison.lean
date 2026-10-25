-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FourJetPreparedResidualComparison, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FourJetPreparedResidualComparison.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit a194894209bc49bb7eab8e89d27e5205146250d6,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FourJetPreparedResidualComparison.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FourJetOriginalResidualPreparation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FourJetCanonicalResidualOscillation

/-! # Direct canonical-world residual preparation from four original jets

Adapted from this LOT tree, o265, x0943 at 5207eac7,
Broad/Qualification/FrozenOriginalResidualPreparation.lean. Its original
source is o106, x0352 at 1e57792e. The original coefficients and graph
are arbitrary and need not be those of the old packet test.
-/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Set MeasureTheory
open scoped BigOperators
noncomputable section

/-- Construct residual tables, entry floors and the residual comparison
in all canonical worlds, with an unchanged original reference law.
The comparison constant has no inverse coefficient-world radius. -/
theorem original_prepared_residual_comparison_of_jets {Λ I : Type*} {V : ℕ → Type*}
    [MeasurableSpace Λ] [MeasurableSpace I] [MeasurableSingletonClass I]
    [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)] [∀ i, Countable (V i)]
    (μ reference : Measure (Λ × ℝ)) [IsFiniteMeasure μ]
    (hμreference : μ ≤ reference) (E : Set (Λ × ℝ)) (hE : MeasurableSet E)
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (G : (Fin 4 → ℤ) → Fin 3 → ℝ) (F : (Fin 7 → ℤ) → ℝ → Fin 2 → ℝ)
    (hFm : ∀ q, Measurable (F q))
    (b ρ H K η error : ℝ) (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hH : 0 ≤ H) (hK : 1 ≤ K) (hη : 0 ≤ η)
    (ht : ∀ z∈E, z.2∈Icc (0 : ℝ) 1)
    (hjets : ∀ z∈E, |c z.1 1| ≤ H ∧ |c z.1 2| ≤ H ∧ |c z.1 4| ≤ H ∧ |c z.1 6| ≤ H)
    (hstateFinite : (originalFineState c b '' E).Finite)
    (hworldFinite : ((fun z : Λ × ℝ => parameterCode ρ (c z.1)) '' E).Finite)
    (hF : ∀ z∈E, ‖F (parameterCode ρ (c z.1)) z.2‖ ≤ K)
    (hrow : ∀ z∈E, ∀ z'∈E, parameterCode ρ (c z.1)=parameterCode ρ (c z'.1) →
      ‖F (parameterCode ρ (c z.1)) z.2-F (parameterCode ρ (c z'.1)) z'.2‖ ≤ K*(|z.2-z'.2|+ρ))
    (hfit : ∀ z∈E, ∀ i : Fin 2,
      |G (originalFineState c b z) i.succ-F (parameterCode ρ (c z.1)) z.2 i| ≤ η)
    (hgraph : ∀ z∈E,
      |c z.1 1+2*c z.1 2*z.2-G (originalFineState c b z) 0-
        (fun i : Fin 2 => G (originalFineState c b z) i.succ) ⬝ᵥ zv (c z.1)| ≤ error)
    (L : ℕ) (hL : 1 ≤ L) (s : ℕ → ℝ) (A ζ : ℝ) (hA : 1 ≤ A)
    (hs0 : s 0=1) (hs : ∀ i, 0 < s i)
    (hratio : ∀ i, i+1<L → s i ≤ A*s (i+1)) (hfloor : s (L-1) ≤ ζ)
    (hsmall : ∀ i<L, (2+3*(H+1))*b ≤ ρ*s i)
    (hρs : ∀ i<L, ρ ≤ s i)
    (hosc : ∀ i<L, (2*(error+2*η*ρ)+2*(H+1)*b)/ρ ≤ s i)
    (coarse : (Fin 7 → ℤ) → I)
    (blocks : (Fin 4 → ℤ) × I → Finset (Fin 7 → ℤ)) (P : ℕ)
    (hP : ∀ q, (blocks q).card ≤ P)
    (hblocks : ∀ z∈E, parameterCode ρ (c z.1) ∈
      blocks (originalFineState c b z,coarse (parameterCode ρ (c z.1))))
    (velocity : (i : ℕ) → Λ → V i) (hv : ∀ i, Measurable (velocity i))
    (π : (i : ℕ) → Measure (V i)) [∀ i, IsProbabilityMeasure (π i)]
    (coarseV : (i : ℕ) → V i → I) (hcv : ∀ i, Measurable (coarseV i))
    (hcoarse : ∀ i<L, ∀ z∈E,
      coarseV i (velocity i z.1)=coarse (parameterCode ρ (c z.1)))
    (C : ℝ) (hC : 0 ≤ C) (cut B : ℕ → ℝ)
    (hcut : ∀ i<L, 0 < cut i) (hB : ∀ i<L, 0 ≤ B i)
    (hcap : ∀ i<L, ∀ w (D : Set (V i)), MeasurableSet D →
      reference {z | originalFineState c b z=w ∧ velocity i z.1∈D} ≤
        ENNReal.ofReal C * reference ((originalFineState c b) ⁻¹' {w}) * (π i) D)
    (finePalettes : (i : ℕ) → (((Fin 7 → ℤ) × (Fin 4 → ℤ)) × V i) → Finset (Fin 7 → ℤ))
    (hFineCard : ∀ i<L, ∀ q, ((finePalettes i q).card : ℝ) ≤ B i)
    (hFineKnown : ∀ i<L, ∀ z∈E, parameterCode (ρ*s i) (c z.1) ∈
      finePalettes i ((parameterCode ρ (c z.1),canonicalZoomCell c ρ (s i) z),velocity i z.1)) :
    ∃ S : Set (Λ × ℝ), MeasurableSet S ∧ S ⊆ E ∧
      μ E ≤ (∏ i∈Finset.range L,
        ((4 : ENNReal)^4*(⌈3*(B i*(22*K^2+5))*(C/cut i)⌉₊+1 : ℕ))) * μ S +
          (∑ i : Fin L, ENNReal.ofReal (cut i.val)*(P*256 : ℕ))*reference univ ∧
      ∀ z∈S, ∀ z'∈S, parameterCode ρ (c z.1)=parameterCode ρ (c z'.1) →
        |originalResidualValue (fun y => canonicalZoomCoefficients c ρ y.1)
          (fun y => F (parameterCode ρ (c y.1)) y.2) Prod.snd z-
          originalResidualValue (fun y => canonicalZoomCoefficients c ρ y.1)
            (fun y => F (parameterCode ρ (c y.1)) y.2) Prod.snd z'| ≤
              2*(A+5*K^2)*(‖zpos (canonicalZoomCoefficients c ρ z.1) z.2-
                zpos (canonicalZoomCoefficients c ρ z'.1) z'.2‖+ζ) := by
  classical
  have hrowm := measurable_original_world_time_row (fun l => parameterCode ρ (c l))
    ((measurable_parameterCode ρ).comp hc) F hFm
  have hex (i : Fin L) := canonical_residual_tables_of_original_parameter_palettes E
    c F (velocity i.val) ρ (s i.val) K (B i.val) hρ (hs i.val) (hρs i.val i.isLt)
    hK ht hF hrow (finePalettes i.val) (hFineCard i.val i.isLt) (hFineKnown i.val i.isLt)
  choose tables htableCard htableKnown using hex
  let table : (i : ℕ) → (((Fin 7 → ℤ) × (Fin 4 → ℤ)) × V i) → Finset ℤ := fun i =>
    if hi : i<L then tables ⟨i,hi⟩ else fun _ => ∅
  have htableSize (i : ℕ) (hi : i<L) (q) : ((table i q).card : ℝ) ≤ B i*(22*K^2+5) := by
    simpa only [table,dite_eq_left hi] using htableCard ⟨i,hi⟩ q
  have htableMem (i : ℕ) (hi : i<L) (z : Λ × ℝ) (hz : z∈E) :
      ⌊originalResidualValue (fun y => canonicalZoomCoefficients c ρ y.1)
        (fun y => F (parameterCode ρ (c y.1)) y.2) Prod.snd z / s i⌋ ∈
          table i ((parameterCode ρ (c z.1),canonicalZoomCell c ρ (s i) z),velocity i z.1) := by
    simpa only [table,dite_eq_left hi] using htableKnown ⟨i,hi⟩ z hz
  apply original_residual_preparation_of_jets μ reference hμreference E hE c hc
    _ hrowm b ρ H K hb hρ hρ1 hH hK ht hjets hstateFinite hworldFinite hF
    L hL s A ζ hA hs0 hs hratio hfloor hsmall coarse blocks P hP hblocks
    (fun i z => velocity i z.1) (fun i => (hv i).comp measurable_fst) π coarseV hcv hcoarse
    C hC cut (fun i => B i*(22*K^2+5)) hcut
    (fun i hi => mul_nonneg (hB i hi) (by positivity)) hcap table htableSize htableMem
  intro i hi z hz z' hz' hstate hworld
  exact (canonical_residual_oscillation_of_jets c E G F b ρ H η error hb hρ hρ1 hH hη
    (fun y hy => (hjets y hy).2.1) hfit hgraph z hz z' hz' hstate hworld).trans (hosc i hi)

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
