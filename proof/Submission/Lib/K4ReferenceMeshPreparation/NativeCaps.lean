/-
Adapted from: here:o107 (session x0735), original-reference cap and
two-scale record helpers in Submission/Obl/k4_finite_narrowness_path_improvement/.
Accepted history-floor and mesh-cover proofs are imported.
-/
import Submission.Lib.K4ReferenceMeshPreparation.OriginalCaps
import Submission.Lib.K4ReferenceMeshPreparation.Types

/-! Assemble finite native E2 from original pure mesh caps and fixed
history/palette numerators. Reference histories are localized only to
bounded menus of native mesh cells, preserving the original palette. -/

namespace Submission.Lib.K4ReferenceMeshPreparation

noncomputable section

open MeasureTheory Set MvPolynomial
open scoped ENNReal

abbrev NativeSignalCell := (Fin 3 → ℤ) × ℤ

def nativeSignalCell {Ω : Type*} (N r s : ℝ) (x : Ω → Fin 4 → ℝ)
    (P : MvPolynomial (Fin 4) ℝ) (p : Ω) : NativeSignalCell :=
  (Submission.Lib.K4AffineMeshCaps.baseMesh (N^(-r)) (fun i : Fin 3 => x p i.castSucc),
    ⌊eval (x p) P / N^(-s)⌋)

theorem measurable_nativeSignalCell {Ω : Type*} [MeasurableSpace Ω]
    (N r s : ℝ) (x : Ω → Fin 4 → ℝ) (hx : Measurable x) (P : MvPolynomial (Fin 4) ℝ) :
    Measurable (nativeSignalCell N r s x P) := by
  have hEval := P.continuous_eval.measurable.comp hx
  change Measurable (fun p => ((fun i : Fin 3 => ⌊x p i.castSucc / N^(-r)⌋),
    ⌊eval (x p) P / N^(-s)⌋))
  fun_prop

/-- Original pure cells plus localized original reference records yield
all three native E2 fields on the retained incidence law. The extra cost
is the history multiplier times the padding-cell count. -/
theorem native_cell_caps_of_localized_records
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (N K C d S R : ℝ) (hN : 0 < N) (hK : 0 ≤ K) (hC : 1 ≤ C)
    (M : ℕ) (hM : 1 ≤ M)
    (ν μ : Measure Ω) (hμ : μ ≤ ν) (π : Measure ℝ)
    (x : Ω → Fin 4 → ℝ) (hx : Measurable x) (P : MvPolynomial (Fin 4) ℝ)
    (velocity : Ω → ℝ)
    (H : ι → Set Ω) (hH : ∀ i, MeasurableSet (H i))
    (hdisj : Pairwise (fun i j => AEDisjoint ν (H i) (H j)))
    (w : ι → ℝ≥0∞) (hw : ∀ i, w i ≤ ν (H i))
    (options : ℝ → ℝ → ι → Finset NativeSignalCell)
    (padding : ℝ → ℝ → NativeSignalCell → Finset NativeSignalCell)
    (hcover : ∀ᵐ p ∂μ, ∃ i, p ∈ H i)
    (hoptions : ∀ r s, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R →
      ∀ i, ∀ᵐ p ∂μ, p ∈ H i → nativeSignalCell N r s x P p ∈ options r s i)
    (hlocal : ∀ r s, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R →
      ∀ i q, q ∈ options r s i → H i ≤ᵐ[ν] {p | nativeSignalCell N r s x P p ∈ padding r s q})
    (hcard : ∀ r s, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R →
      ∀ q, (padding r s q).card ≤ M)
    (hpure : ∀ r s, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R →
      ∀ q, ν {p | nativeSignalCell N r s x P p = q} ≤ ENNReal.ofReal (K*N^(-3*r-d*s)))
    (hpalette : ∀ v, R⁻¹ ≤ v → v ≤ R → ∀ z : ℤ,
      π {t | ⌊t/N^(-v)⌋ = z} ≤ ENNReal.ofReal (K*N^(-S*v)))
    (hrecord : ∀ v, R⁻¹ ≤ v → v ≤ R → ∀ i z,
      μ (H i ∩ {p | ⌊velocity p/N^(-v)⌋ = z}) ≤
        ENNReal.ofReal C*w i*π {t | ⌊t/N^(-v)⌋ = z}) :
    NativeCellCaps N (C*(M : ℝ)*K) d S R μ π x P velocity := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hC0 : 0 ≤ C := by linarith
  have hCM : 1 ≤ C*(M : ℝ) :=
    hC.trans (le_mul_of_one_le_right hC0 hM1)
  have hKL : K ≤ C*(M : ℝ)*K := by
    calc K = 1*K := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hCM hK
  have hscale (u : ℝ) : ENNReal.ofReal (K*N^u) ≤ ENNReal.ofReal (C*(M : ℝ)*K*N^u) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hKL (Real.rpow_nonneg hN.le _))
  have hcoeff (u : ℝ) : ENNReal.ofReal C*(M : ℝ≥0∞)*ENNReal.ofReal (K*N^u) =
      ENNReal.ofReal (C*(M : ℝ)*K*N^u) := by
    rw [← ENNReal.ofReal_natCast M,← ENNReal.ofReal_mul hC0,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ C*(M : ℝ))]
    congr 1 <;> ring
  intro r s v hrl hrh hs0 hsh hvl hvh
  refine ⟨fun z => (hpalette v hvl hvh z).trans (hscale _),?_,?_⟩
  · intro q a
    have hp := hpure r s hrl hrh hs0 hsh (q,a)
    have href : ν {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N^(-r))
          (fun i : Fin 3 => x p i.castSucc) = q ∧ ⌊eval (x p) P/N^(-s)⌋ = a} ≤
        ENNReal.ofReal (K*N^(-3*r-d*s)) := by
      simpa only [nativeSignalCell,Prod.mk.injEq] using hp
    exact ((hμ _).trans href).trans (hscale _)
  · intro q a z
    have hstate (q' : NativeSignalCell) :
        MeasurableSet {p | nativeSignalCell N r s x P p = q'} :=
      measurableSet_eq_fun (measurable_nativeSignalCell N r s x hx P) measurable_const
    have hcap := localized_reference_mesh_event_cap ν μ (nativeSignalCell N r s x P) hstate
      H hH hdisj (options r s) w hw (nativeSignalCell N r s x P) (padding r s) M
      (hcard r s hrl hrh hs0 hsh) (hlocal r s hrl hrh hs0 hsh)
      (ENNReal.ofReal (K*N^(-3*r-d*s))) (hpure r s hrl hrh hs0 hsh)
      (ENNReal.ofReal C) (π {t | ⌊t/N^(-v)⌋ = z}) {p | ⌊velocity p/N^(-v)⌋ = z}
      hcover (hoptions r s hrl hrh hs0 hsh) (fun i => hrecord v hvl hvh i z) (q,a)
    have hset : {p | nativeSignalCell N r s x P p = (q,a)} ∩
        {p | ⌊velocity p/N^(-v)⌋ = z} =
        {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N^(-r))
            (fun i : Fin 3 => x p i.castSucc) = q ∧ ⌊eval (x p) P/N^(-s)⌋ = a ∧
          ⌊velocity p/N^(-v)⌋ = z} := by
      ext p
      simp only [mem_inter_iff,mem_ofPred_eq,nativeSignalCell,Prod.mk.injEq,and_assoc]
    rw [hset] at hcap
    simpa only [hcoeff] using hcap

end

end Submission.Lib.K4ReferenceMeshPreparation
