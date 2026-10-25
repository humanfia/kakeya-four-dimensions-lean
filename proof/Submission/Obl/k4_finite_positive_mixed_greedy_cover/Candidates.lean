import Submission.Obl.k4_finite_positive_mixed_greedy_cover.StripFormat
import Submission.Obl.k4_quadratic_finite_greedy_cover.DerivativeLoss
import Submission.Obl.k4_quadratic_finite_greedy_cover.PrioritySets

namespace Submission.Obl.k4_finite_positive_mixed_greedy_cover

open MeasureTheory Set
open scoped ENNReal
noncomputable section

abbrev Trajectory := ℕ × (Fin 6 → ℝ)
abbrev Incidence := Trajectory × ℝ

structure Test (C : ℕ) where
  parent : Fin C
  gain : ℝ
  time : Bool
  poly : MvPolynomial (Fin 4) ℝ
  normal : Fin 2 → ℝ
  bias : ℝ

structure Piece (C : ℕ) extends Test C where
  trajectories : Set Trajectory

abbrev pieceParent {C : ℕ} (a : Piece C) : Fin C := a.toTest.parent

def block {C : ℕ} (T : ℕ → ℕ) (lev j : Fin C → ℕ) (b : Fin C) : Set ℝ :=
  Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b)) (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b))

def allowance {C : ℕ} (Nk L ρ ε : ℝ) (a : Test C) : ℝ := Nk ^ (ρ * a.gain * L + ε)

def relativeFloor {C : ℕ} (Nk L d₁ ρ ε : ℝ) (a : Test C) : ℝ :=
  Nk ^ (-((if a.time then d₁ + ρ else ρ) * a.gain * L) - ε)

def envelope {W C : ℕ} (Nk L ρ ε : ℝ) (B : Fin W → ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (lev j : Fin C → ℕ) (γ : Fin C → Fin W)
    (u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (A : Fin C → Set Trajectory) (a : Test C) : Set Trajectory :=
  if a.time then
    Submission.Obl.k4_quadratic_finite_greedy_cover.eligibleTrajectories (A a.parent) a.poly
      (allowance Nk L ρ ε a * δ Nk (r (lev a.parent) + a.gain * L))
      (allowance Nk L ρ ε a * B (γ a.parent))
      (allowance Nk L ρ ε a * B (γ a.parent) ^ 2 / δ Nk (r (lev a.parent) + a.gain * L))
      (B (γ a.parent) / allowance Nk L ρ ε a)
      ((j a.parent : ℝ) / (2 : ℝ) ^ T (lev a.parent))
      (((j a.parent : ℝ) + 1) / (2 : ℝ) ^ T (lev a.parent))
  else {l | l ∈ A a.parent ∧ InStrip (T (lev a.parent)) (u a.parent) (Q a.parent)
    a.normal a.bias (allowance Nk L ρ ε a * Nk ^ (-a.gain * L)) l}

def derivativeTest {W C : ℕ} (Nk L ρ ε : ℝ) (B : Fin W → ℝ)
    (γ : Fin C → Fin W) (a : Test C) (p : Incidence) : Prop :=
  if a.time then B (γ a.parent) / allowance Nk L ρ ε a ≤
    |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) a.poly)| else True

def witness {W C : ℕ} (Nk L ρ ε : ℝ) (B : Fin W → ℝ)
    (T : ℕ → ℕ) (lev j : Fin C → ℕ) (γ : Fin C → Fin W)
    (H : Fin W → Set Incidence) (a : Piece C) : Set Incidence :=
  {p | p ∈ H (γ a.parent) ∧ p.1 ∈ a.trajectories ∧ p.2 ∈ block T lev j a.parent ∧
    derivativeTest Nk L ρ ε B γ a.toTest p}

def TestGood {W C : ℕ} (Nk L : ℝ) (Mc : ℕ) (gain : ℝ)
    (ν : Fin W → Measure Trajectory) (r : ℕ → ℝ) (lev : Fin C → ℕ)
    (γ : Fin C → Fin W) (A : Fin C → Set Trajectory) (a : Test C) : Prop :=
  gain ≤ a.gain ∧ a.gain ≤ 1 / 8 ∧ r (lev a.parent) + 2 * a.gain * L ≤ L ∧
    0 < ν (γ a.parent) (A a.parent) ∧
    if a.time then a.poly.totalDegree ≤ 2 ∧ ∀ e, |a.poly.coeff e| ≤ Nk ^ Mc
    else (∑ e, (a.normal e) ^ 2) = 1 ∧ |a.bias| ≤ Nk ^ Mc

/-- Envelope eligibility retains the exact whole-block fit and a derivative
witness somewhere, or the exact normalized old-frame strip. -/
theorem envelope_subset {W C : ℕ} (Nk L ρ ε : ℝ) (B : Fin W → ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (lev j : Fin C → ℕ) (γ : Fin C → Fin W)
    (u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (A : Fin C → Set Trajectory) (a : Test C) :
    envelope Nk L ρ ε B r T lev j γ u Q A a ⊆ A a.parent := by
  unfold envelope
  split <;> exact fun l hl => hl.1

theorem envelope_measurable {W C : ℕ} (Nk L ρ ε : ℝ) (B : Fin W → ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (lev j : Fin C → ℕ) (γ : Fin C → Fin W)
    (u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (A : Fin C → Set Trajectory) (a : Test C)
    (hA : MeasurableSet (A a.parent)) (hR : a.time = true → a.poly.totalDegree ≤ 2) :
    MeasurableSet (envelope Nk L ρ ε B r T lev j γ u Q A a) := by
  unfold envelope
  split_ifs with ht
  · apply Submission.Obl.k4_quadratic_finite_greedy_cover.eligibleTrajectories_measurable
    · exact hA
    · exact hR ht
    · apply div_le_div_of_nonneg_right (by linarith) (by positivity)
  · exact hA.inter (strip_measurable _ _ _ _ _ _)

theorem envelope_format {W C : ℕ} (Nk L ρ ε : ℝ) (B : Fin W → ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (lev j : Fin C → ℕ) (γ : Fin C → Fin W)
    (u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (A : Fin C → Set Trajectory) (a : Test C) (H : ℝ) (D q : ℕ)
    (hA : fmt 6 H D {w | (q,w) ∈ A a.parent})
    (hR : a.time = true → a.poly.totalDegree ≤ 2) :
    fmt 6 (H + 96) (max D 4) {w | (q,w) ∈ envelope Nk L ρ ε B r T lev j γ u Q A a} := by
  unfold envelope
  split_ifs with ht
  · apply Submission.Obl.k4_quadratic_finite_greedy_cover.eligibleTrajectories_format
    · exact hR ht
    · apply div_le_div_of_nonneg_right (by linarith) (by positivity)
    · exact hA
  · have hh := Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.inter hA
      (strip_format (T (lev a.parent)) (u a.parent) (Q a.parent) a.normal a.bias
        (allowance Nk L ρ ε a * Nk ^ (-a.gain * L)) q)
    exact Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono hh (by linarith)
      (max_le_max le_rfl (by norm_num))

theorem witness_measurable {W C : ℕ} (Nk L ρ ε : ℝ) (B : Fin W → ℝ)
    (T : ℕ → ℕ) (lev j : Fin C → ℕ) (γ : Fin C → Fin W)
    (H : Fin W → Set Incidence) (a : Piece C)
    (hH : MeasurableSet (H (γ a.parent))) (hA : MeasurableSet a.trajectories) :
    MeasurableSet (witness Nk L ρ ε B T lev j γ H a) := by
  have hd : MeasurableSet {p | derivativeTest Nk L ρ ε B γ a.toTest p} := by
    unfold derivativeTest
    split_ifs
    · exact measurableSet_le measurable_const
        (((MvPolynomial.continuous_eval _).comp
          Submission.Obl.k4_quadratic_finite_greedy_cover.continuous_trajectory_point).abs.measurable)
    · exact MeasurableSet.univ
  exact hH.inter ((hA.preimage measurable_fst).inter
    ((measurableSet_Icc.preimage measurable_snd).inter hd))

/-- Removing earlier full trajectory cylinders retains the discovery witness. -/
theorem candidate_piece {W C Mc : ℕ} (Nk L d₁ ρ gain ε : ℝ)
    (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (lev j : Fin C → ℕ) (γ : Fin C → Fin W)
    (u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (A : Fin C → Set Trajectory) (H : Fin W → Set Incidence)
    (hc : cand Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j u Q A H) :
    ∃ a : Test C, TestGood Nk L Mc gain ν r lev γ A a ∧
      ENNReal.ofReal (relativeFloor Nk L d₁ ρ ε a / (2 : ℝ) ^ T (lev a.parent)) *
        ν (γ a.parent) (A a.parent) ≤
      (ν (γ a.parent)).prod volume
        (witness Nk L ρ ε B T lev j γ H ⟨a, envelope Nk L ρ ε B r T lev j γ u Q A a⟩) := by
  obtain ⟨b,h,hg,hh,hr,hpos,hcand⟩ := hc
  rcases hcand with ⟨R,hR,hcoeff,hfloor⟩ | ⟨a,z,ha,hz,hfloor⟩
  · let test : Test C := ⟨b,h,true,R,0,0⟩
    refine ⟨test, ⟨hg,hh,hr,hpos,hR,hcoeff⟩, hfloor.trans (measure_mono ?_)⟩
    intro p hp
    rcases hp with ⟨hH,hA,hI,hfit,hlow⟩
    refine ⟨hH, ?_, hI, hlow⟩
    refine ⟨hA, ?_, ?_, ?_, ⟨p.2,hI,hlow⟩⟩
    · exact fun t ht => (hfit t ht).1
    · exact fun t ht => (hfit t ht).2.1
    · exact fun t ht => (hfit t ht).2.2
  · let test : Test C := ⟨b,h,false,0,a,z⟩
    refine ⟨test, ⟨hg,hh,hr,hpos,ha,hz⟩, ?_⟩
    have hx : relativeFloor Nk L d₁ ρ ε test = Nk ^ (-ρ*h*L-ε) := by
      dsimp [relativeFloor, test]
      congr 1
      ring
    rw [hx]
    apply hfloor.trans
    apply measure_mono
    rintro p ⟨hH,hA,hI,hstrip⟩
    exact ⟨hH, ⟨hA,hstrip⟩, hI, trivial⟩

end
end Submission.Obl.k4_finite_positive_mixed_greedy_cover
