-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.QualificationParameters, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.IncidenceWorldQualification

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- The concrete uniform qualification conclusion at fixed analytic
parameters. Its incidence preparation still precedes every later source. -/
def NativeQualificationAt (d : ℝ) (M : ℕ) (ε cζ α Q₀ : ℝ) : Prop :=
      ∀ N c_h : ℝ, 0 < N → 0 < c_h → Q₀ ≤ N^c_h →
      ∀ (Λ : Type) [MeasurableSpace Λ] (ν : Measure Λ) [IsProbabilityMeasure ν]
        (c : Λ → Fin 7 → ℝ), Measurable c →
      ∀ E Eref : Set (Λ × ℝ), MeasurableSet E → MeasurableSet Eref → E⊆Eref →
        (∀ z∈Eref, z.2∈Icc (0:ℝ) 1) →
      ∀ ρ ζ cut C amplitude Kcap Kss Krc Kres : ℝ,
        0 < ρ → 0 < ζ → ζ ≤ 1 → ρ ≤ ζ → 0 < cut →
        0 ≤ C → 0 ≤ amplitude → 0 < Kcap → 625*C/cut ≤ Kcap →
        8*Kcap^2 ≤ N^(c_h*α) → Kss ≤ N^(c_h*α) →
        0 ≤ Krc → Krc ≤ N^(c_h*α) → Kres ≤ N^(c_h*α) →
      (∀ n : ℕ, n ≤ parameterLevel ζ →
        ((fun z : Λ × ℝ => originalZoomBlock c ρ (dyadicParameterWidth n) z.1) '' E).Finite) →
      ∀ π : Measure (Fin 2 → ℝ),
      (∀ q : ℝ, ζ ≤ q → q ≤ 1 → ∀ world cell β,
        ((ν.prod volume).restrict E) {z | parameterCode ρ (c z.1)=world ∧
          canonicalZoomCell c ρ (dyadicParameterWidth (parameterLevel q)) z=cell ∧
          parameterCode (ρ*dyadicParameterWidth (parameterLevel q)) (zv (c z.1))=β} ≤
        ENNReal.ofReal (C*dyadicParameterWidth (parameterLevel q)*
          (ρ*dyadicParameterWidth (parameterLevel q))^((2:ℝ)+d)*amplitude)*
          π {v | parameterCode (ρ*dyadicParameterWidth (parameterLevel q)) v=β}) →
      ∃ R : Set (Λ × ℝ), MeasurableSet R ∧ R⊆E ∧
        (ν.prod volume) (E\R) ≤ ((parameterLevel ζ+1:ℕ):ENNReal)*
          ENNReal.ofReal (cut*zoomBlockVisitConstant) ∧
        ∀ S : Set (Λ × ℝ), MeasurableSet S → S⊆R →
        ∀ F : (Fin 7 → ℤ) → ℝ → Fin 2 → ℝ,
          OriginalWorldControl ν c S F ρ ζ d (N^(c_h*α)) Kcap Kss Krc Kres amplitude π →
        ∀ T : ℕ,
          N^(-c_h)/(N^(c_h*α)) ≤ ((2:ℝ)^T)⁻¹ →
          ((2:ℝ)^T)⁻¹ ≤ (N^(c_h*α))*N^(-c_h) → ζ ≤ ((2:ℝ)^T)⁻¹^cζ →
        ∀ (ι : Type) [MeasurableSpace ι] (lab : Λ × ℝ → ι)
          (G : Λ × ℝ → Fin 3 → ℝ),
          Measurable lab → MeasurableSet {q : ι × ι | q.1=q.2} → Measurable G →
        ∀ B graphError rowError : ℝ, 0 ≤ B →
          (∀ z∈S, |c z.1 1| ≤ B ∧ |c z.1 2| ≤ B ∧ |c z.1 4| ≤ B ∧ |c z.1 6| ≤ B) →
          (∀ z∈S, |c z.1 1+2*c z.1 2*z.2-
            (G z 0+G z 1*c z.1 4+G z 2*c z.1 6)| ≤ graphError) →
          (∀ z∈S, ∀ i : Fin 2,
            |G z i.succ-F (parameterCode ρ (c z.1)) z.2 i| ≤ rowError) →
          (∀ z∈S, ∀ v, (z.1,v)∈S → v∈dyadicBlock T z.2 → lab (z.1,v)=lab z) →
        ∀ (mesh err' dur' : ℝ) (bound : ℤ), 0 < mesh →
          3*B+(1+2*B)*N^(c_h*ε) ≤ mesh*(bound-1) →
          graphError+(1+2*B)*(rowError+((2:ℝ)^T)⁻¹^((M:ℝ)+1/8))+
            (M+1)*mesh ≤ err' → dur' ≤ ((2:ℝ)^T)⁻¹*N^(-(c_h*ε)) →
          (ν.prod volume)
            (S\{z | NativeGridQualified Eref lab G M T mesh bound err' dur' z}) <
              ENNReal.ofReal (2*N^(-(c_h*α)))

private def qualificationFamily (d : ℝ) (M : ℕ)
    (h : 0 ≤ d ∧ d < 1 ∧ 2 ≤ M) :
    {cζ : ℝ // 0 < cζ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ α : ℝ, 0 < α ∧ ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ NativeQualificationAt d M ε cζ α Q₀} := by
  have hex : ∃ cζ : ℝ, 0 < cζ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ α : ℝ, 0 < α ∧ ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ NativeQualificationAt d M ε cζ α Q₀ :=
    prepare_native_qualification_from_current_velocity_caps d h.1 h.2.1 M h.2.2
  exact ⟨Classical.choose hex,Classical.choose_spec hex⟩

/-- The cutoff chosen by the checked higher-jet proof. This function
has no data or scale-window argument. -/
def nativeQualificationCutoff (d : ℝ) (M : ℕ) : ℝ :=
  if h : 0 ≤ d ∧ d < 1 ∧ 2 ≤ M then (qualificationFamily d M h).val else 1

/-- Its admissible coefficient and density exponent, chosen before data. -/
def nativeQualificationExponent (d : ℝ) (M : ℕ) (ε : ℝ) : ℝ :=
  if h : (0 ≤ d ∧ d < 1 ∧ 2 ≤ M) ∧ 0 < ε then
    Classical.choose ((qualificationFamily d M h.1).property.2 ε h.2)
  else 1

/-- The corresponding analytic-base threshold. -/
def nativeQualificationThreshold (d : ℝ) (M : ℕ) (ε : ℝ) : ℝ :=
  if h : (0 ≤ d ∧ d < 1 ∧ 2 ≤ M) ∧ 0 < ε then
    Classical.choose (Classical.choose_spec
      ((qualificationFamily d M h.1).property.2 ε h.2)).2
  else 1

/-- A positive scale-depth factor available to every pre-data window. -/
def nativeQualificationDepth (d : ℝ) (M : ℕ) : ℝ :=
  max 1 (nativeQualificationCutoff d M)

/-- A positive budget factor at most one, available to all earlier
choices of breadth, entropy, path tolerance and row constants. -/
def nativeQualificationBudget (d : ℝ) (M : ℕ) (ε : ℝ) : ℝ :=
  min 1 (nativeQualificationExponent d M ε)

theorem nativeQualificationCutoff_pos (d : ℝ) (M : ℕ) :
    0 < nativeQualificationCutoff d M := by
  unfold nativeQualificationCutoff
  split_ifs with h
  · exact (qualificationFamily d M h).property.1
  · exact zero_lt_one

theorem nativeQualificationExponent_pos (d : ℝ) (M : ℕ) (ε : ℝ) :
    0 < nativeQualificationExponent d M ε := by
  unfold nativeQualificationExponent
  split_ifs with h
  · exact (Classical.choose_spec ((qualificationFamily d M h.1).property.2 ε h.2)).1
  · exact zero_lt_one

theorem one_le_nativeQualificationDepth (d : ℝ) (M : ℕ) :
    1 ≤ nativeQualificationDepth d M := le_max_left _ _

theorem nativeQualificationCutoff_le_depth (d : ℝ) (M : ℕ) :
    nativeQualificationCutoff d M ≤ nativeQualificationDepth d M := le_max_right _ _

theorem nativeQualificationBudget_pos (d : ℝ) (M : ℕ) (ε : ℝ) :
    0 < nativeQualificationBudget d M ε :=
  lt_min zero_lt_one (nativeQualificationExponent_pos d M ε)

theorem nativeQualificationBudget_le_one (d : ℝ) (M : ℕ) (ε : ℝ) :
    nativeQualificationBudget d M ε ≤ 1 := min_le_left _ _

theorem nativeQualificationBudget_le_exponent (d : ℝ) (M : ℕ) (ε : ℝ) :
    nativeQualificationBudget d M ε ≤ nativeQualificationExponent d M ε := min_le_right _ _

/-- These are the actual parameters of the incidence preparation
and native qualification theorem, including the same full original prior. -/
theorem nativeQualificationParameters_spec (d : ℝ) (M : ℕ) (ε : ℝ)
    (hd : 0 ≤ d) (hd1 : d < 1) (hM : 2 ≤ M) (hε : 0 < ε) :
    1 ≤ nativeQualificationThreshold d M ε ∧
      NativeQualificationAt d M ε (nativeQualificationCutoff d M)
        (nativeQualificationExponent d M ε) (nativeQualificationThreshold d M ε) := by
  have h : 0 ≤ d ∧ d < 1 ∧ 2 ≤ M := ⟨hd,hd1,hM⟩
  have he : (0 ≤ d ∧ d < 1 ∧ 2 ≤ M) ∧ 0 < ε := ⟨h,hε⟩
  simp only [nativeQualificationThreshold,nativeQualificationCutoff,nativeQualificationExponent,
    dite_eq_left h,dite_eq_left he]
  exact Classical.choose_spec (Classical.choose_spec
    ((qualificationFamily d M h).property.2 ε hε)).2

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
