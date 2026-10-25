import Submission.Obl.k4_physical_parent_potential_candidates.SharpDirectionalBounds
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.DenseJet.Transfer

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory MvPolynomial PhysicalPotentialData
open Submission.Lib.K4PotentialPlaneMenus Submission.Lib.K4CubicTests

noncomputable section

namespace PotentialJets

/-- Real polynomial evaluation on the Euclidean base is smooth. -/
theorem contDiff_eval (P : MvPolynomial (Fin 3) ℝ) :
    ContDiff ℝ ⊤ (fun y : P3 => eval (fun i => y i) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa only [eval_C] using (contDiff_const : ContDiff ℝ ⊤ (fun _:P3 => a))
  | add P Q hP hQ => simpa only [eval_add] using hP.add hQ
  | mul_X P i hP =>
    simpa only [eval_mul, eval_X] using hP.mul (by fun_prop : ContDiff ℝ ⊤ (fun y:P3 => y i))

/-- The formal directional polynomial jet is the actual diagonal multilinear
jet, at the same point and in the same original clock units. -/
theorem iteratedFDeriv_eq_formal (P : MvPolynomial (Fin 3) ℝ) (x p : P3) (n : ℕ) :
    iteratedFDeriv ℝ n (fun y : P3 => eval (fun i => y i) P) x (fun _ => p) =
      eval (fun i => x i) ((polynomialDirectionalDerivative (fun i => p i))^[n] P) := by
  rw [← Analytic.DenseJet.Transfer.iteratedDeriv_line_eq isOpen_univ
    ((contDiff_eval P).of_le le_top).contDiffOn (mem_univ x) p n]
  change iteratedDeriv n (fun t : ℝ => eval (fun i => x i+t*p i) P) 0 = _
  simpa only [zero_mul, add_zero] using PotentialThirdJets.iteratedDeriv_eval_affine P
    (fun i => x i) (fun i => p i) n 0

end PotentialJets

namespace PhysicalSource

/-- A single constant, fixed before every source parameter, controls the
actual pure jets on the entire original old time block. -/
theorem exists_uniform_sharp_actual_time_jet_bound (q : ℕ) (hq : 2 ≤ q) (r : ℕ) (hr : 3 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ {T j : ℕ} {ν : Measure Ln}
      {B a ζ d : ℝ} {c u : P2} {P0 : Po} {A : Set Ln} {F H : Set Ev}
      (source : PhysicalSource q ν B a ζ d T j c u P0 A F H),
      ∀ (_hP0 : P0.totalDegree ≤ 2), ∀ l ∈ source.lineSet,
      ∀ t ∈ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹) (((j:ℝ)+1)*((2:ℝ)^T)⁻¹),
        |iteratedFDeriv ℝ r (fun y : P3 => eval (fun i => y i) source.Pot)
          (packetBase T j c u (l,t))
          (fun _ => Submission.Lib.K4OriginalCellSampling.Sampling.lift (v l))| ≤ C*a*ζ := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_sharp_pure_line_jet_bound q hq r hr
  refine ⟨C,hC,?_⟩
  intro T j ν B a ζ d c u P0 A F H source hP0 l hl t ht
  let h : ℝ := ((2:ℝ)^T)⁻¹
  have hh : 0 < h := by dsimp [h]; positivity
  let s : ℝ := (t-(j:ℝ)*h)/h
  have hs : s ∈ Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith [ht.1]) hh.le
    · apply (div_le_one hh).2
      change t-(j:ℝ)*h ≤ h
      have ht2 : t ≤ ((j:ℝ)+1)*h := ht.2
      linarith
  have he : (j:ℝ)*h+h*s=t := by dsimp [s]; field_simp; ring
  have hb := hbound source hP0 l hl s hs
  change |eval (fun i => packetBase T j c u (l,(j:ℝ)*h+h*s) i) _|/a ≤ _ at hb
  rw [he] at hb
  rw [PotentialJets.iteratedFDeriv_eq_formal]
  have hb' := (div_le_iff₀ source.a_pos).mp hb
  calc _ ≤ C*ζ*a := hb'
    _ = C*a*ζ := by ring

variable {q T j : ℕ} {ν : Measure Ln}
  {B a ζ d : ℝ} {c u : P2} {P0 : Po} {A : Set Ln} {F H : Set Ev}
  (source : PhysicalSource q ν B a ζ d T j c u P0 A F H)

/-- Sharp pure potential tests in actual multilinear derivative notation.
The bound is in the original signal units `a`, with no clock-to-thickness
ratio lost in passing from the polynomial derivative convention. -/
theorem exists_sharp_actual_line_jet_bound (hq : 2 ≤ q) (r : ℕ) (hr : 3 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hP0 : P0.totalDegree ≤ 2),
      ∀ l ∈ source.lineSet, ∀ s ∈ Icc (0:ℝ) 1,
        |iteratedFDeriv ℝ r (fun y : P3 => eval (fun i => y i) source.Pot)
          (packetBase T j c u (l,(j:ℝ)*((2:ℝ)^T)⁻¹+((2:ℝ)^T)⁻¹*s))
          (fun _ => Submission.Lib.K4OriginalCellSampling.Sampling.lift (v l))| ≤ C*a*ζ := by
  obtain ⟨C,hC,hb⟩ := source.exists_sharp_pure_line_jet_bound hq r hr
  refine ⟨C,hC,?_⟩
  intro hP0 l hl s hs
  rw [PotentialJets.iteratedFDeriv_eq_formal]
  have hh := (div_le_iff₀ source.a_pos).mp (hb hP0 l hl s hs)
  calc
    _ ≤ C*ζ*a := hh
    _ = C*a*ζ := by ring

/-- The same sharp actual tests, indexed by ordinary physical time on the
entire old block, including every event used for state sampling. -/
theorem exists_sharp_actual_time_jet_bound (hq : 2 ≤ q) (r : ℕ) (hr : 3 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hP0 : P0.totalDegree ≤ 2),
      ∀ l ∈ source.lineSet, ∀ t ∈ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹) (((j:ℝ)+1)*((2:ℝ)^T)⁻¹),
        |iteratedFDeriv ℝ r (fun y : P3 => eval (fun i => y i) source.Pot)
          (packetBase T j c u (l,t))
          (fun _ => Submission.Lib.K4OriginalCellSampling.Sampling.lift (v l))| ≤ C*a*ζ := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_sharp_actual_time_jet_bound q hq r hr
  exact ⟨C,hC,hbound source⟩

end PhysicalSource

end

end Submission.Obl.k4_physical_parent_potential_candidates
