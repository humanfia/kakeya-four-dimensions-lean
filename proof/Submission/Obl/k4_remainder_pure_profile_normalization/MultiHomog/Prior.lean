/-
Adapted from this LOT tree, o147, session x0502, commit 373d234,
Submission/Obl/k4_local_remainder_horizon_transfer/Homogenize/Prior.lean
(that session's own code).
-/
import Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog.Lines


/-!
# Encoded priors

A prior which is a finite sum of multiples of Lebesgue measure on indexed pieces keeps
this form when pushed forward by the encoding of a world, and a weighted mixture of such
priors over the worlds is again of this form, indexed by `Fin (∑ γ, m γ)`.

-/

namespace Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog

open MeasureTheory Set
open scoped ENNReal

theorem map_finset_sum' {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [Fintype ι]
    (μ : ι → Measure α) {f : α → β} (hf : Measurable f) :
    (∑ i, μ i).map f = ∑ i, (μ i).map f := by
  rw [← Measure.sum_fintype, Measure.map_sum hf.aemeasurable, Measure.sum_fintype]

theorem measurable_pair_left (i : ℕ) : Measurable (fun x : Fin 6 → ℝ => (i, x)) :=
  measurable_const.prodMk measurable_id

/-- The encoding of one Lebesgue piece. -/
theorem map_encLine_piece {W : ℕ} (γ : Fin W) {a b θ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hθ : θ ≠ 0) (o : ℝ) (i : ℕ) (A : Set (Fin 6 → ℝ)) :
    (Measure.map (fun x => (i, x)) (volume.restrict A)).map (encLine W γ a b θ o) =
      ENNReal.ofReal |(a * b * θ) ^ 2|⁻¹ •
        Measure.map (fun x => (encIdx W γ i, x))
          (volume.restrict {x | decCoeff a b θ o x ∈ A}) := by
  rw [Measure.map_map (measurable_encLine W γ a b θ o) (measurable_pair_left i)]
  have hcomp : encLine W γ a b θ o ∘ (fun x => (i, x)) =
      (fun x => (encIdx W γ i, x)) ∘ encEquiv ha hb hθ o := by
    funext x; rfl
  rw [hcomp, ← Measure.map_map (measurable_pair_left _) (encEquiv ha hb hθ o).measurable]
  have hres : (volume.restrict A).map (encEquiv ha hb hθ o) =
      ((volume : Measure (Fin 6 → ℝ)).map (encEquiv ha hb hθ o)).restrict
        {x | decCoeff a b θ o x ∈ A} := by
    rw [MeasurableEquiv.restrict_map]
    congr 2
    ext x
    simp [decCoeff_encCoeff ha hb hθ]
  rw [hres]
  have hvol : (volume : Measure (Fin 6 → ℝ)).map (encEquiv ha hb hθ o) =
      ENNReal.ofReal |(a * b * θ) ^ 2|⁻¹ • volume := map_encCoeff_volume ha hb hθ o
  rw [hvol, Measure.restrict_smul, Measure.map_smul]
  exact (measurable_pair_left _).aemeasurable

/-- The encoding of a piecewise Lebesgue prior. -/
theorem map_encLine_prior {W : ℕ} (γ : Fin W) {a b θ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hθ : θ ≠ 0) (o : ℝ) {m : ℕ} (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j) (i : Fin m → ℕ)
    (A : Fin m → Set (Fin 6 → ℝ)) :
    (∑ j, ENNReal.ofReal (c j) • Measure.map (fun x => (i j, x)) (volume.restrict (A j))).map
        (encLine W γ a b θ o) =
      ∑ j, ENNReal.ofReal (c j * |(a * b * θ) ^ 2|⁻¹) •
        Measure.map (fun x => (encIdx W γ (i j), x))
          (volume.restrict {x | decCoeff a b θ o x ∈ A j}) := by
  rw [map_finset_sum' _ (measurable_encLine W γ a b θ o)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Measure.map_smul, map_encLine_piece γ ha hb hθ o, smul_smul,
    ENNReal.ofReal_mul (hc j)]
  exact (measurable_encLine W γ a b θ o).aemeasurable

/-- A weighted mixture of piecewise Lebesgue priors, reindexed by one `Fin`. -/
theorem mixture_reindex {W : ℕ} (m : Fin W → ℕ) (w : Fin W → ℝ) (hw : ∀ γ, 0 ≤ w γ)
    (c : (γ : Fin W) → Fin (m γ) → ℝ) (i : (γ : Fin W) → Fin (m γ) → ℕ)
    (A : (γ : Fin W) → Fin (m γ) → Set (Fin 6 → ℝ)) :
    ∑ γ, ENNReal.ofReal (w γ) • ∑ j, ENNReal.ofReal (c γ j) •
        Measure.map (fun x => (i γ j, x)) (volume.restrict (A γ j)) =
      ∑ J : Fin (∑ γ, m γ),
        ENNReal.ofReal (w (finSigmaFinEquiv.symm J).1 *
            c (finSigmaFinEquiv.symm J).1 (finSigmaFinEquiv.symm J).2) •
          Measure.map (fun x => (i (finSigmaFinEquiv.symm J).1 (finSigmaFinEquiv.symm J).2, x))
            (volume.restrict (A (finSigmaFinEquiv.symm J).1 (finSigmaFinEquiv.symm J).2)) := by
  set F : ((γ : Fin W) × Fin (m γ)) → Measure Trajectory := fun σ =>
    ENNReal.ofReal (w σ.1 * c σ.1 σ.2) •
      Measure.map (fun x => (i σ.1 σ.2, x)) (volume.restrict (A σ.1 σ.2)) with hF
  have h1 : ∑ J : Fin (∑ γ, m γ), F (finSigmaFinEquiv.symm J) = ∑ σ, F σ :=
    Equiv.sum_comp finSigmaFinEquiv.symm F
  have h2 : ∑ σ, F σ = ∑ γ, ENNReal.ofReal (w γ) • ∑ j, ENNReal.ofReal (c γ j) •
      Measure.map (fun x => (i γ j, x)) (volume.restrict (A γ j)) := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hF]
    rw [smul_smul, ENNReal.ofReal_mul (hw γ)]
  rw [← h2, ← h1]

end Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog
