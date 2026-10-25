-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.DerivativeListsFromIncidences, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.DerivativeListsFromParameterPalettes
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PreparedIncidenceParameterPalettes

/-! Construct all ordinary-cell scalar derivative lists by one actual
entry pruning. The original full coefficient-bin floors and current
canonical-cell caps supply the palettes internally. -/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- Full original coefficient floors and current incidence caps imply
the derivative lists at all tested resolutions. No scalar derivative
list, original snapshot cap or parameter menu is supplied. -/
theorem prepare_derivative_lists_from_incidences {Λ I : Type*}
    [MeasurableSpace Λ] [Fintype I]
    (μ : Measure (Λ × ℝ)) (ν : Measure Λ)
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (E : Set (Λ × ℝ)) (hE : MeasurableSet E)
    (ht : ∀ z∈E, z.2∈Icc (0:ℝ) 1)
    (H : ℕ) (hcoeff : ∀ z∈E, ∀ j, |c z.1 j| ≤ H)
    (level : I → ℕ) (amplitude K C cut : I → ℝ)
    (hamp : ∀ i, 0 < amplitude i) (hK : ∀ i, 0 < K i)
    (hC : ∀ i, 0 ≤ C i) (hcut : ∀ i, 0 < cut i)
    (weight : I → (Fin 2 → ℤ) → ENNReal) (hweight : ∀ i v, weight i v ≠ ∞)
    (hfloor : ∀ i z, z∈E →
      ENNReal.ofReal ((dyadicParameterWidth (level i))^2*amplitude i/K i)*
        weight i (parameterCode (dyadicParameterWidth (level i)) (zv (c z.1))) ≤
      ν {l | parameterCode (dyadicParameterWidth (level i)) (c l)=
        parameterCode (dyadicParameterWidth (level i)) (c z.1)})
    (hcap : ∀ i world cell v,
      (μ.restrict E) {z | parameterCode 1 (c z.1)=world ∧
        canonicalZoomCell c 1 (dyadicParameterWidth (level i)) z=cell ∧
        parameterCode (dyadicParameterWidth (level i)) (zv (c z.1))=v} ≤
      ENNReal.ofReal (C i*dyadicParameterWidth (level i)*
        (dyadicParameterWidth (level i))^2*amplitude i)*weight i v) :
    ∃ R : Set (Λ × ℝ), MeasurableSet R ∧ R⊆E ∧
      μ (E\R) ≤ (∑ i, ENNReal.ofReal (cut i*zoomBlockVisitConstant))*ν univ ∧
      ∃ lists : I → ((Fin 4 → ℤ) × (Fin 2 → ℤ)) → Finset ℤ,
        (∀ i key, ((lists i key).card : ℝ) ≤
          (2*(H:ℝ)+3)^7*(6*(H:ℝ)+12)^4*(C i*K i/cut i)*
            (2*(⌈2*(H:ℝ)+5⌉:ℝ)+1)) ∧
        ∀ i z, z∈R →
          ⌊(c z.1 1+2*c z.1 2*z.2)/dyadicParameterWidth (level i)⌋∈
            lists i (originalFineState c (dyadicParameterWidth (level i)) z,
              parameterCode (dyadicParameterWidth (level i)) (zv (c z.1))) := by
  have hs1 (i : I) : dyadicParameterWidth (level i) ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  obtain ⟨R,hR,hRE,hloss,palettes,hpalettes,hknown⟩ :=
    prepare_incidence_parameter_palettes μ ν c hc E hE ht (fun _ => 1)
      amplitude K C cut level (fun _ => by norm_num) hamp hK hC hcut (by
        intro i
        simpa only [one_mul] using original_parameter_worlds_finite E c
          (dyadicParameterWidth (level i)) (H:ℝ) (dyadicParameterWidth_pos _) hcoeff)
      weight hweight (by simpa only [one_mul] using hfloor)
      (by simpa only [one_mul] using hcap)
  have hex (i : I) := exists_canonical_unit_world_menus R c
    (dyadicParameterWidth_pos (level i)) (Nat.cast_nonneg H)
    (fun z hz => hcoeff z (hRE hz)) (fun z hz => ht z (hRE hz))
  choose menus hmenu hmenuKnown using hex
  have hparams (i : I) (z : Λ × ℝ) (hz : z∈R) :
      parameterCode (dyadicParameterWidth (level i)) (c z.1)∈
        palettes i ((parameterCode 1 (c z.1),
          canonicalZoomCell c 1 (dyadicParameterWidth (level i)) z),
            parameterCode (dyadicParameterWidth (level i)) (zv (c z.1))) := by
    simpa only [one_mul] using hknown i z hz
  have hlist (i : I) := derivative_lists_of_canonical_parameter_palettes R c
    (dyadicParameterWidth_pos (level i)) (hs1 i) (Nat.cast_nonneg H)
    (by positivity : 0 ≤ (6*(H:ℝ)+12)^4)
    (div_nonneg (mul_nonneg (hC i) (hK i).le) (hcut i).le)
    (fun z hz => ht z (hRE hz)) (fun z hz => hcoeff z (hRE hz) 2)
    (boundedUnitWorlds H)
    (fun z hz => parameterCode_one_mem_boundedUnitWorlds H (c z.1) (hcoeff z (hRE hz)))
    (menus i) (hmenu i) (hmenuKnown i) (palettes i) (hpalettes i) (hparams i)
  choose lists hcard hderivative using hlist
  refine ⟨R,hR,hRE,hloss,lists,?_,hderivative⟩
  intro i key
  simpa only [boundedUnitWorlds_card] using hcard i key

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
