-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SeparatedFurstenberg.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.SmallPowers
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.FrostmanExtraction

/-!
# Removing the point-separation assumption from the Furstenberg estimate

The Frostman extraction loses only the absolute factor 1440. Shrinking the
Frostman exponent by two absorbs this factor at a sufficiently small scale.
All bushes are restricted to the selected points; their directional bounds
are retained without changing the scale or the output exponent.

Ported from session x0444 (o141, commit 89688bb).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

local notation "FPlane" => EuclideanSpace ℝ (Fin 2)

/-- The frozen Furstenberg bush estimate at one scale, with the additional
assumption that its points are separated. -/
def SeparatedFurstenbergAt (r σ ε₀ η : ℝ) : Prop :=
  ∀ (P : Set FPlane) (D : Set (FPlane × FPlane)), P.Finite → P.Nonempty → D.Finite →
    (∀ p ∈ P, ‖p‖ ≤ 4) →
    (∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → r ≤ dist p p') →
    (∀ (x : FPlane) (ρ : ℝ), r ≤ ρ →
      ((P ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ r ^ (-η) * ρ * P.ncard) →
    (∀ q ∈ D, q.1 ∈ P ∧ ‖q.2‖ = 1) →
    (∀ p ∈ P, r ^ (η - σ) ≤ ({e | (p, e) ∈ D}.ncard : ℝ)) →
    (∀ p e e', (p, e) ∈ D → (p, e') ∈ D → e ≠ e' → r ≤ dist e e') →
    (∀ p ∈ P, ∀ u : FPlane, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      ({e | (p, e) ∈ D ∧ dist e u ≤ ρ}.ncard : ℝ) ≤ r ^ (-η) * (ρ / r) ^ σ) →
    ∃ J ⊆ D, (∀ q ∈ J, ∀ q' ∈ J, q ≠ q' → (r ≤ dist q.2 q'.2 ∧ r ≤ dist q.2 (-q'.2)) ∨
        r ≤ |inner ℝ (q.1 - q'.1) q.2|) ∧
      r ^ (-(2 * σ) - ε₀) ≤ (J.ncard : ℝ)

/-- The separated-point version implies the literal Furstenberg child of o141. -/
theorem furstenberg_of_separated
    (h : ∀ ε : ℝ, 0 < ε → ∃ ε₀ η r₀ : ℝ, 0 < ε₀ ∧ 0 < η ∧ 0 < r₀ ∧
      ∀ r σ : ℝ, 0 < r → r ≤ r₀ → 1 / 4 ≤ σ → σ ≤ 1 - ε →
        SeparatedFurstenbergAt r σ ε₀ η) :
    ∀ ε : ℝ, 0 < ε → ∃ ε₀ η r₀ : ℝ, 0 < ε₀ ∧ 0 < η ∧ 0 < r₀ ∧
      ∀ r σ : ℝ, 0 < r → r ≤ r₀ → 1 / 4 ≤ σ → σ ≤ 1 - ε →
      ∀ (P : Set FPlane) (D : Set (FPlane × FPlane)), P.Finite → P.Nonempty → D.Finite →
      (∀ p ∈ P, ‖p‖ ≤ 4) →
      (∀ (x : FPlane) (ρ : ℝ), r ≤ ρ →
        ((P ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ r ^ (-η) * ρ * P.ncard) →
      (∀ q ∈ D, q.1 ∈ P ∧ ‖q.2‖ = 1) →
      (∀ p ∈ P, r ^ (η - σ) ≤ ({e | (p, e) ∈ D}.ncard : ℝ)) →
      (∀ p e e', (p, e) ∈ D → (p, e') ∈ D → e ≠ e' → r ≤ dist e e') →
      (∀ p ∈ P, ∀ u : FPlane, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
        ({e | (p, e) ∈ D ∧ dist e u ≤ ρ}.ncard : ℝ) ≤ r ^ (-η) * (ρ / r) ^ σ) →
      ∃ J ⊆ D, (∀ q ∈ J, ∀ q' ∈ J, q ≠ q' →
        (r ≤ dist q.2 q'.2 ∧ r ≤ dist q.2 (-q'.2)) ∨
          r ≤ |inner ℝ (q.1 - q'.1) q.2|) ∧
        r ^ (-(2 * σ) - ε₀) ≤ (J.ncard : ℝ) := by
  intro ε hε
  obtain ⟨ε₀, ηA, rA, hε₀, hηA, hrA, hA⟩ := h ε hε
  let η := ηA / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηle : η ≤ ηA := by dsimp [η]; linarith
  obtain ⟨rC, hrC, hsmall⟩ :=
    WangZahlLot.Obl.wz_slab_local_linearity.exists_small_monomial
      (a := -η) (b := -ηA) (C := 1440) (by dsimp [η]; linarith) (by norm_num)
  refine ⟨ε₀, η, min 1 (min rA rC), hε₀, hη, by positivity, ?_⟩
  intro r σ hr hr0 hσ0 hσ1 P D hP hPne hD hPnorm hFr hDmem hbush hsep hKT
  have hr1 : r ≤ 1 := hr0.trans (min_le_left _ _)
  have hrrA : r ≤ rA := (hr0.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hrrC : r ≤ rC := (hr0.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hC1 : 1 ≤ r ^ (-η) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge hr hr1 (show -η ≤ (0 : ℝ) by linarith)
  have hCmono : r ^ (-η) ≤ r ^ (-ηA) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  have hconstant : 1440 * r ^ (-η) ≤ r ^ (-ηA) := hsmall r hr hrrC
  obtain ⟨Q, hQP, hQ, hQne, _, hQsep, hQFr⟩ :=
    planar_frostman_separated_subset hr hr1 hC1 hP hPne hFr
  let DQ := {q ∈ D | q.1 ∈ Q}
  have hDQ : DQ ⊆ D := fun _ hq => hq.1
  have hrow (p : FPlane) (hp : p ∈ Q) : {e | (p, e) ∈ DQ} = {e | (p, e) ∈ D} := by
    ext e
    simp only [DQ, Set.mem_ofPred_eq, hp, and_true]
  have hrowball (p : FPlane) (hp : p ∈ Q) (u : FPlane) (ρ : ℝ) :
      {e | (p, e) ∈ DQ ∧ dist e u ≤ ρ} = {e | (p, e) ∈ D ∧ dist e u ≤ ρ} := by
    ext e
    simp only [DQ, Set.mem_ofPred_eq, hp, and_true]
  have hQFr' : ∀ (x : FPlane) (ρ : ℝ), r ≤ ρ →
      ((Q ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ r ^ (-ηA) * ρ * Q.ncard := by
    intro x ρ hρ
    apply (hQFr x ρ hρ).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hconstant (hr.le.trans hρ)) (Nat.cast_nonneg _)
  obtain ⟨J, hJQ, hJsep, hJcount⟩ := hA r σ hr hrrA hσ0 hσ1 Q DQ hQ hQne
    (hD.subset hDQ) (fun p hp => hPnorm p (hQP hp)) hQsep hQFr'
    (fun q hq => ⟨hq.2, (hDmem q hq.1).2⟩)
    (fun p hp => by
      rw [hrow p hp]
      exact (Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith : η - σ ≤ ηA - σ)).trans
        (hbush p (hQP hp)))
    (fun p e e' he he' hne => hsep p e e' he.1 he'.1 hne)
    (fun p hp u hu ρ hρ => by
      rw [hrowball p hp]
      exact (hKT p (hQP hp) u hu ρ hρ).trans
        (mul_le_mul_of_nonneg_right hCmono (Real.rpow_nonneg ((div_pos (hr.trans_le hρ) hr).le) _)))
  exact ⟨J, hJQ.trans hDQ, hJsep, hJcount⟩

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
