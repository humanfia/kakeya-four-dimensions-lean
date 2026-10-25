-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.FromKatzTao.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.FromFixedExponents
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.KatzTaoExtraction

/-!
# The standard discretized point-set input suffices

The input in this file uses separated points with at least `r ^ (η - 1)`
elements and an absolute Katz--Tao bound `r ^ (-η) * (ρ / r)`. The original
normalized Frostman hypotheses imply this form by dyadic extraction.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

def KatzTaoFurstenbergAt (r σ ε₀ η : ℝ) : Prop :=
  ∀ (P : Set Plane) (D : Set (Plane × Plane)), P.Finite → P.Nonempty → D.Finite →
    (∀ p ∈ P, ‖p‖ ≤ 4) →
    (∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → r ≤ dist p p') →
    r ^ (η - 1) ≤ (P.ncard : ℝ) →
    (∀ (x : Plane) (ρ : ℝ), r ≤ ρ →
      ((P ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ r ^ (-η) * (ρ / r)) →
    (∀ q ∈ D, q.1 ∈ P ∧ ‖q.2‖ = 1) →
    (∀ p ∈ P, r ^ (η - σ) ≤ ({e | (p, e) ∈ D}.ncard : ℝ)) →
    (∀ p e e', (p, e) ∈ D → (p, e') ∈ D → e ≠ e' → r ≤ dist e e') →
    (∀ p ∈ P, ∀ u : Plane, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      ({e | (p, e) ∈ D ∧ dist e u ≤ ρ}.ncard : ℝ) ≤ r ^ (-η) * (ρ / r) ^ σ) →
    ∃ J ⊆ D, (∀ q ∈ J, ∀ q' ∈ J, q ≠ q' →
      (r ≤ dist q.2 q'.2 ∧ r ≤ dist q.2 (-q'.2)) ∨
        r ≤ |inner ℝ (q.1 - q'.1) q.2|) ∧
      r ^ (-(2 * σ) - ε₀) ≤ (J.ncard : ℝ)

/-- Fixed-exponent analytic input in the usual absolute point-count convention. -/
def FixedKatzTaoCore : Prop :=
  ∀ s : ℝ, 1 / 2 ≤ s → s < 1 → ∃ ε₀ η r₀ : ℝ,
    0 < ε₀ ∧ 0 < η ∧ 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ → KatzTaoFurstenbergAt r s ε₀ η

lemma fixed_separated_of_katz_tao {s : ℝ}
    (h : ∃ ε₀ η r₀ : ℝ, 0 < ε₀ ∧ 0 < η ∧ 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ → KatzTaoFurstenbergAt r s ε₀ η) :
    ∃ ε₀ η r₀ : ℝ, 0 < ε₀ ∧ 0 < η ∧ 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ → SeparatedFurstenbergAt r s ε₀ η := by
  obtain ⟨A, hA, hExtract⟩ := bounded_frostman_katz_tao_extraction
  obtain ⟨ε₀, η₀, R, hε₀, hη₀, hR, hcore⟩ := h
  let η := η₀ / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηle : η ≤ η₀ := by dsimp [η]; linarith
  obtain ⟨R₁, hR₁, hsmall⟩ :=
    WangZahlLot.Obl.wz_slab_local_linearity.exists_small_rpow
      (a := η) (B := 1 / 40) hη (by norm_num)
  obtain ⟨R₂, hR₂, hconst⟩ :=
    WangZahlLot.Obl.wz_slab_local_linearity.exists_small_monomial
      (a := 0) (b := -η₀) (C := A) (by linarith) (by linarith)
  refine ⟨ε₀, η, min (1 / 2) (min R (min R₁ R₂)), hε₀, hη, by positivity, ?_⟩
  intro r hr hrs P D hPf hPne hDf hPnorm hPsep hFr hDmem hlarge hsep hKT
  have hrhalf : r ≤ 1 / 2 := hrs.trans (min_le_left _ _)
  have hrone : r ≤ 1 := by linarith
  have hrR : r ≤ R := (hrs.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hrR₁ : r ≤ R₁ :=
    ((hrs.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hrR₂ : r ≤ R₂ :=
    ((hrs.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hC : 1 ≤ r ^ (-η) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge hr hrone (show -η ≤ (0 : ℝ) by linarith)
  have hCmono : r ^ (-η) ≤ r ^ (-η₀) :=
    Real.rpow_le_rpow_of_exponent_ge hr hrone (by linarith)
  have hAmono : A ≤ r ^ (-η₀) := by
    simpa only [Real.rpow_zero, mul_one] using hconst r hr hrR₂
  obtain ⟨Q, hQP, hQ, hQne, hQmass, _, hQsep, _, hQcount⟩ :=
    hExtract r (r ^ (-η)) P hr hrhalf hC hPf hPne hPnorm hFr
  have hmass : r ^ (η₀ - 1) ≤ (Q.ncard : ℝ) := by
    apply le_trans _ hQmass
    rw [le_div_iff₀ (by positivity : 0 < 40 * r ^ (-η) * r)]
    have hid : r ^ (η₀ - 1) * (40 * r ^ (-η) * r) = 40 * r ^ η := by
      calc r ^ (η₀ - 1) * (40 * r ^ (-η) * r)
          = 40 * (r ^ (η₀ - 1) * r ^ (-η) * r ^ (1 : ℝ)) := by
            rw [Real.rpow_one]; ring
        _ = 40 * r ^ ((η₀ - 1) + (-η) + 1) := by
            rw [← Real.rpow_add hr, ← Real.rpow_add hr]
        _ = 40 * r ^ η := by
            congr 1
            congr 1
            dsimp [η]
            ring
    rw [hid]
    linarith [hsmall r hr hrR₁]
  let DQ := {q ∈ D | q.1 ∈ Q}
  have hDQ : DQ ⊆ D := fun _ hq => hq.1
  have hrow (p : Plane) (hp : p ∈ Q) : {e | (p, e) ∈ DQ} = {e | (p, e) ∈ D} := by
    ext e
    simp only [DQ, Set.mem_ofPred_eq, hp, and_true]
  have hrowball (p : Plane) (hp : p ∈ Q) (u : Plane) (ρ : ℝ) :
      {e | (p, e) ∈ DQ ∧ dist e u ≤ ρ} = {e | (p, e) ∈ D ∧ dist e u ≤ ρ} := by
    ext e
    simp only [DQ, Set.mem_ofPred_eq, hp, and_true]
  obtain ⟨J, hJQ, hJsep, hJcard⟩ := hcore r hr hrR Q DQ hQ hQne (hDf.subset hDQ)
    (fun p hp => hPnorm p (hQP hp)) hQsep hmass
    (fun x ρ hρ => (hQcount x ρ hρ).trans
      (mul_le_mul_of_nonneg_right hAmono (div_nonneg (hr.le.trans hρ) hr.le)))
    (fun q hq => ⟨hq.2, (hDmem q hq.1).2⟩)
    (fun p hp => by
      rw [hrow p hp]
      exact (Real.rpow_le_rpow_of_exponent_ge hr hrone
        (show η - s ≤ η₀ - s by linarith)).trans (hlarge p (hQP hp)))
    (fun p e e' he he' hne => hsep p e e' he.1 he'.1 hne)
    (fun p hp u hu ρ hρ => by
      rw [hrowball p hp]
      exact (hKT p (hQP hp) u hu ρ hρ).trans
        (mul_le_mul_of_nonneg_right hCmono
          (Real.rpow_nonneg (div_nonneg (hr.le.trans hρ) hr.le) _)))
  exact ⟨J, hJQ.trans hDQ, hJsep, hJcard⟩

theorem fixed_high_of_katz_tao (h : FixedKatzTaoCore) : FixedHighRangeSeparatedCore :=
  fun s hs hsone => fixed_separated_of_katz_tao (h s hs hsone)

/-- The literal frozen statement from fixed-exponent Katz--Tao estimates. -/
theorem furstenberg_of_fixed_katz_tao (h : FixedKatzTaoCore) : ∀ ε : ℝ, 0 < ε → ∃ ε₀ η r₀ : ℝ, 0 < ε₀ ∧ 0 < η ∧ 0 < r₀ ∧ ∀ r σ : ℝ, 0 < r → r ≤ r₀ → 1 / 4 ≤ σ → σ ≤ 1 - ε → ∀ (P : Set (EuclideanSpace ℝ (Fin 2))) (D : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), P.Finite → P.Nonempty → D.Finite → (∀ p ∈ P, ‖p‖ ≤ 4) → (∀ (x : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), r ≤ ρ → ((P ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ r ^ (-η) * ρ * P.ncard) → (∀ q ∈ D, q.1 ∈ P ∧ ‖q.2‖ = 1) → (∀ p ∈ P, r ^ (η - σ) ≤ ({e | (p, e) ∈ D}.ncard : ℝ)) → (∀ p e e', (p, e) ∈ D → (p, e') ∈ D → e ≠ e' → r ≤ dist e e') → (∀ p ∈ P, ∀ u : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ → ({e | (p, e) ∈ D ∧ dist e u ≤ ρ}.ncard : ℝ) ≤ r ^ (-η) * (ρ / r) ^ σ) → ∃ J ⊆ D, (∀ q ∈ J, ∀ q' ∈ J, q ≠ q' → (r ≤ dist q.2 q'.2 ∧ r ≤ dist q.2 (-q'.2)) ∨ r ≤ |inner ℝ (q.1 - q'.1) q.2|) ∧ r ^ (-(2 * σ) - ε₀) ≤ (J.ncard : ℝ) :=
  furstenberg_of_fixed_high (fixed_high_of_katz_tao h)

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
