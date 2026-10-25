-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/ParentPotentialPullback.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.ParentSignalGroups
import Submission.Obl.k4_physical_parent_potential_candidates.PhysicalPotentialPacket
import Submission.Lib.K4OriginalGeometricReference.BasePotentialPullback

/-!
# The source potential in original base coordinates

The physical potential source uses an unsheared old block coordinate. The restoration
backend evaluates its base polynomial at the original three base coordinates. This affine
pullback identifies the two evaluations exactly and preserves the degree.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Broad

open MvPolynomial Set
open Submission.Obl.k4_physical_parent_potential_candidates.Analytic
open Submission.Lib.K4OriginalGeometricReference.Analytic

noncomputable section

/-- The origin of the unsheared source base coordinates. -/
def parentBaseOrigin (T j : ℕ) (c u : P2) : Fin 3 → ℝ :=
  let t₀ := (j : ℝ) * ((2 : ℝ) ^ T)⁻¹
  ![t₀, c 0 + t₀ * u 0, c 1 + t₀ * u 1]

/-- Translation used to pull a source potential back to the original base. -/
def parentBaseShift (T j : ℕ) (c u : P2) : Fin 3 → ℝ :=
  fun i => -((2 : ℝ) ^ T) * parentBaseOrigin T j c u i

/-- Scaling used to pull a source potential back to the original base. -/
def parentBaseMatrix (T : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ((2 : ℝ) ^ T) • 1

/-- A normalized source potential, expressed as a polynomial of the original base. -/
def parentPotentialPullback (T j : ℕ) (c u : P2)
    (Pot : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  basePotentialPullback
    (affineBaseCoordinates (parentBaseShift T j c u) (parentBaseMatrix T)) 1 Pot

lemma parentBase_coordinates (T j : ℕ) (c u : P2) (p : Ev) (i : Fin 3) :
    parentBaseShift T j c u i +
        ∑ k : Fin 3, parentBaseMatrix T i k * xp p.1 p.2 k.castSucc =
      PhysicalPotentialData.packetBase T j c u p i := by
  simp only [parentBaseShift, parentBaseMatrix, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  fin_cases i <;>
    simp [parentBaseOrigin, PhysicalPotentialData.packetBase, xp, div_eq_mul_inv] <;> ring

/-- The source and backend see the same potential value at every original incidence. -/
theorem eval_parentPotentialPullback (T j : ℕ) (c u : P2)
    (Pot : MvPolynomial (Fin 3) ℝ) (p : Ev) :
    eval (fun i : Fin 3 => xp p.1 p.2 i.castSucc) (parentPotentialPullback T j c u Pot) =
      eval (fun i : Fin 3 => PhysicalPotentialData.packetBase T j c u p i) Pot := by
  rw [parentPotentialPullback, basePotentialPullback_eval, one_mul]
  apply congrArg (fun z : Fin 3 → ℝ => eval z Pot)
  funext i
  rw [affineBaseCoordinates_eval]
  exact parentBase_coordinates T j c u p i

theorem totalDegree_parentPotentialPullback (T j : ℕ) (c u : P2)
    (Pot : MvPolynomial (Fin 3) ℝ) :
    (parentPotentialPullback T j c u Pot).totalDegree ≤ Pot.totalDegree :=
  basePotentialPullback_degree _ (affineBaseCoordinates_degree _ _) _ _

/-- Express the literal source own-intercept fit in the backend's original base variables. -/
theorem parent_own_intercept_fit_iff (T j : ℕ) (c u : P2) (R0 : Po)
    (Pot : MvPolynomial (Fin 3) ℝ) (l : Ln) (t ε : ℝ) :
    |(eval (xp l t) R0 -
        eval (fun i => PhysicalPotentialData.packetBase T j c u (l, t) i) Pot) -
      (eval (xp l ((j : ℝ) * ((2 : ℝ) ^ T)⁻¹)) R0 -
        eval (fun i => PhysicalPotentialData.packetBase T j c u
          (l, (j : ℝ) * ((2 : ℝ) ^ T)⁻¹) i) Pot)| ≤ ε ↔
    |eval (xp l t) R0 -
        eval (fun i : Fin 3 => xp l t i.castSucc) (parentPotentialPullback T j c u Pot) -
      (eval (xp l ((j : ℝ) * ((2 : ℝ) ^ T)⁻¹)) R0 -
        eval (fun i : Fin 3 => xp l ((j : ℝ) * ((2 : ℝ) ^ T)⁻¹) i.castSucc)
          (parentPotentialPullback T j c u Pot))| ≤ ε := by
  rw [eval_parentPotentialPullback T j c u Pot (l, t),
    eval_parentPotentialPullback T j c u Pot (l, (j : ℝ) * ((2 : ℝ) ^ T)⁻¹)]

/-- The original line's intercept, defined at the left endpoint of its old block. -/
def parentIntercept (T j : ℕ) (c u : P2) (R0 : Po)
    (Pot : MvPolynomial (Fin 3) ℝ) (l : Ln) : ℝ :=
  let t₀ := (j : ℝ) * ((2 : ℝ) ^ T)⁻¹
  eval (xp l t₀) R0 -
    eval (fun i => PhysicalPotentialData.packetBase T j c u (l, t₀) i) Pot

/-- The exact normalized source fits produce physical group points for the independent
old certificate. This includes the affine polynomial pullback needed by the backend. -/
theorem physicalGroupPoint_of_normalized_parent_potential (q : ℕ) :
    ∃ Cx : ℝ, 1 ≤ Cx ∧
    ∀ {Nk : ℝ} {Mp Dp : ℕ} {κ : ℝ} {T j : ℕ} {rr Bv : ℝ}
      {Evs : Set Ev} {c u : P2} {Qm : Matrix (Fin 2) (Fin 2) ℝ}
      {Rb : Po} {A : Set Ln} {F : Set Ev} {ex : Prop},
      ch Nk Mp Dp κ T (j : ℝ) rr Bv Evs c u Qm Rb A F ex → 1 ≤ κ → 0 < Bv →
    ∀ (R0 : Po) (Pot : MvPolynomial (Fin 3) ℝ), R0.totalDegree ≤ 2 →
      Pot.totalDegree ≤ q →
    ∀ (l : Ln) (K c₀ εfit ω σ te : ℝ), κ ≤ K → 0 ≤ εfit →
      (∀ t ∈ Icc ((j : ℝ) * ((2 : ℝ) ^ T)⁻¹)
          (((j : ℝ) + 1) * ((2 : ℝ) ^ T)⁻¹),
        |(eval (xp l t) R0 -
            eval (fun i => PhysicalPotentialData.packetBase T j c u (l, t) i) Pot) -
          parentIntercept T j c u R0 Pot l| ≤ εfit) →
      (∀ t ∈ Icc ((j : ℝ) / (2 : ℝ) ^ T) (((j : ℝ) + 1) / (2 : ℝ) ^ T),
        |eval (xp l t) (pderiv 3 R0)| ≤ K * Bv) →
      |parentIntercept T j c u R0 Pot l - c₀| ≤ ω → σ ^ 2 = 1 → (l, te) ∈ F →
      Bv / K ≤ σ * eval (xp l te) (pderiv 3 R0) →
    ∀ t, |t - te| ≤ ((2 : ℝ) ^ T)⁻¹ / (4 * K ^ 2) →
      PhysicalGroupPoint Bv⁻¹ (R0 - C c₀) Rb (parentPotentialPullback T j c u Pot)
        (Cx * εfit + ω) (2 * K) σ (Cx * (κ * δ Nk rr)) (graphPoint l t) := by
  obtain ⟨Cx, hCx, hgroup⟩ := physicalGroupPoint_of_parent_chart (max 2 q)
  refine ⟨Cx, hCx, ?_⟩
  intro Nk Mp Dp κ T j rr Bv Evs c u Qm Rb A F ex hch hκ hB R0 Pot hR0 hPot
    l K c₀ εfit ω σ te hκK hε hfit hparent hwin hσ hF hreg t ht
  have hdeg : (R0 - liftBase (parentPotentialPullback T j c u Pot)).totalDegree ≤ max 2 q :=
    (totalDegree_sub _ _).trans (max_le (hR0.trans (le_max_left _ _))
      ((totalDegree_liftBase_le _).trans ((totalDegree_parentPotentialPullback _ _ _ _ _).trans
        (hPot.trans (le_max_right _ _)))))
  apply hgroup hch hκ hB R0 (parentPotentialPullback T j c u Pot) hR0 hdeg l K
    (parentIntercept T j c u R0 Pot l) c₀ εfit ω σ te hκK hε ?_ hparent hwin hσ hF hreg t ht
  intro s hs
  have hs' : s ∈ Icc ((j : ℝ) * ((2 : ℝ) ^ T)⁻¹)
      (((j : ℝ) + 1) * ((2 : ℝ) ^ T)⁻¹) := by
    simpa only [div_eq_mul_inv] using hs
  have hf := (parent_own_intercept_fit_iff T j c u R0 Pot l s εfit).mp (hfit s hs')
  rw [eval_parentPotentialPullback T j c u Pot (l, (j : ℝ) * ((2 : ℝ) ^ T)⁻¹)] at hf
  exact hf

end

end Submission.Obl.k4_physical_parent_potential_candidates.Broad
