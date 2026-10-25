-- From o024 session x0067, commit 9dab30f2086d5fbe6f0edb2475a9e1c856bdab0e.
import Mathlib

namespace Submission.Obl.k4_oss_projection_flattening

open Set MeasureTheory
open scoped ENNReal

/-- The interval nonconcentration bound restricted to scales from `δ` to one. -/
def ScaleFrostman (δ C s : ℝ) (μ : Measure ℝ) : Prop :=
  ∀ x u : ℝ, δ ≤ u → u ≤ 1 → μ (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (C * u ^ s)

/-- The collision probability at scale `δ`. -/
noncomputable def collisionProbability (δ : ℝ) (μ : Measure ℝ) : ℝ≥0∞ :=
  (μ.prod μ) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}

theorem measurableSet_collision (δ : ℝ) :
    MeasurableSet {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} :=
  (measurable_fst.sub measurable_snd).abs measurableSet_Iic

/-- An interval cap bounds the collision probability by the same cap. -/
theorem collision_le_interval_cap (δ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M : ℝ≥0∞) (hcap : ∀ x, μ (Icc (x - δ) (x + δ)) ≤ M) :
    collisionProbability δ μ ≤ M := by
  unfold collisionProbability
  rw [Measure.prod_apply (measurableSet_collision δ)]
  have hfiber (x : ℝ) :
      Prod.mk x ⁻¹' {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} = Icc (x - δ) (x + δ) := by
    ext y
    simp only [mem_preimage, mem_ofPred_eq, mem_Icc, abs_le]
    constructor <;> rintro ⟨hlo, hhi⟩ <;> constructor <;> linarith
  simp_rw [hfiber]
  calc
    _ ≤ ∫⁻ _x : ℝ, M ∂μ := lintegral_mono hcap
    _ = M := by simp

theorem ScaleFrostman.collision_le {δ C s : ℝ} {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hF : ScaleFrostman δ C s μ) (hδ1 : δ ≤ 1) :
    collisionProbability δ μ ≤ ENNReal.ofReal (C * δ ^ s) :=
  collision_le_interval_cap δ μ _ (fun x => hF x δ le_rfl hδ1)

/-- A Frostman exponent larger than the allowed collision dimension rules out nonflatness. -/
theorem no_nonflat_of_exponent_gap {s γ ε δ : ℝ} {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hδ : 0 < δ) (hδ1 : δ < 1)
    (hgap : 1 - γ < s - ε) (hF : ScaleFrostman δ (δ ^ (-ε)) s μ)
    (hnonflat : ENNReal.ofReal (δ ^ (1 - γ)) ≤ collisionProbability δ μ) : False := by
  have hupper := hF.collision_le hδ1.le
  have hpow : δ ^ (-ε) * δ ^ s = δ ^ (s - ε) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  rw [hpow] at hupper
  have hstrict : δ ^ (s - ε) < δ ^ (1 - γ) :=
    Real.rpow_lt_rpow_of_exponent_gt hδ hδ1 hgap
  exact (not_lt_of_ge (hnonflat.trans hupper))
    ((ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hδ _)).mpr hstrict)

end Submission.Obl.k4_oss_projection_flattening
