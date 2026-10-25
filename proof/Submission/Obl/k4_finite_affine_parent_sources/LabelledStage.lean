-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.ActiveLabels
import Submission.Obl.k4_finite_affine_parent_sources.RelativeBlocks

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set

noncomputable section

/-- Attach the active TRUE old labels to a native incidence model. The
full original assignments are used for both A and B. -/
def withActiveLabels
    (base : EStage Trajectory) {W : ℕ} (p : PathData W)
    (H : Fin W → Set Incidence) (depth : ℝ → ℕ) (T : ℝ → ℕ)
    (j : (s : ℝ) → Fin (p.activeCount H (depth s)) → Fin (2 ^ T s))
    (c : (s : ℝ) → Fin (p.activeCount H (depth s)) → Fin 5 → ℝ)
    (F : (s : ℝ) → Fin (p.activeCount H (depth s)) → MvPolynomial (Fin 4) ℝ) :
    EStage Trajectory :=
  { base with
    T := T
    nl := fun s => p.activeCount H (depth s)
    j := j
    A := fun s i => p.assigned (p.activeLabel H (depth s) i)
    B := fun s i => p.assigned (p.activeLabel H (depth s) i)
    c := c
    F := F }

/-- Adding true labels does not change the pointwise or pure/joint native
hypotheses, which concern the fixed laws and native coordinates. -/
theorem withActiveLabels_eh1_eh2
    (base : EStage Trajectory) {W : ℕ} (p : PathData W)
    (H : Fin W → Set Incidence) (depth : ℝ → ℕ) (T : ℝ → ℕ)
    (j : (s : ℝ) → Fin (p.activeCount H (depth s)) → Fin (2 ^ T s))
    (c : (s : ℝ) → Fin (p.activeCount H (depth s)) → Fin 5 → ℝ)
    (F : (s : ℝ) → Fin (p.activeCount H (depth s)) → MvPolynomial (Fin 4) ℝ)
    (d S R : ℝ) :
    (EH1 (withActiveLabels base p H depth T j c F) ↔ EH1 base) ∧
      (EH2 d S (withActiveLabels base p H depth T j c F) R ↔ EH2 d S base R) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- True-label nesting in the frozen model follows from actual old
ancestry and ONE common affine parent-time normalization. -/
theorem withActiveLabels_eh4
    {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sgrid : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sgrid δ₀ Mp Dp σ)
    (base : EStage Trajectory) (H : Fin W → Set Incidence)
    (depth : ℝ → ℕ) (hdepth : Monotone depth) (T : ℝ → ℕ)
    (j : (s : ℝ) → Fin (p.activeCount H (depth s)) → Fin (2 ^ T s))
    (c : (s : ℝ) → Fin (p.activeCount H (depth s)) → Fin 5 → ℝ)
    (F : (s : ℝ) → Fin (p.activeCount H (depth s)) → MvPolynomial (Fin 4) ℝ)
    (t₀ q : ℝ) (hq : q ≠ 0)
    (hblocks : ∀ s i t,
      t ∈ Icc ((p.bin (p.activeLabel H (depth s) i) : ℝ) / (2 : ℝ) ^ p.T (depth s))
          (((p.bin (p.activeLabel H (depth s) i) : ℝ) + 1) / (2 : ℝ) ^ p.T (depth s)) ↔
        (t - t₀) / q ∈ IS (T s) (j s i)) (U R : ℝ) :
    EH4 U (withActiveLabels base p H depth T j c F) R := by
  intro s t _ hst _ i
  obtain ⟨a, hA, hI⟩ := hp.active_labels_nested H (hdepth hst.le) i
  refine ⟨a, hA, ?_⟩
  exact normalized_time_subset t₀ q hq _ _ _ _ (hblocks t i) (hblocks s a) hI

end

end Submission.Obl.k4_finite_affine_parent_sources
