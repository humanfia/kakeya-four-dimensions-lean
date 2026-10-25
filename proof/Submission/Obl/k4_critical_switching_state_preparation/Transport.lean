import Submission.Obl.k4_critical_switching_state_preparation.SwitchingModel
import Submission.Obl.k4_raw_earlier_witness_normalization.MeasureNormalize

namespace Submission.Obl.k4_critical_switching_state_preparation

open Set MeasureTheory
open scoped ENNReal
open Submission.Obl.k4_raw_earlier_witness_normalization

noncomputable section

/-- Restrict once and normalize once: every intercept bin retains its original
mass in the same units as the full original parent prior. -/
theorem normalizedMap_bin_transport {α : Type*} [MeasurableSpace α]
    (ρ lam : Measure (α × ℝ)) (source : Set (α × ℝ))
    (f : α × ℝ → α × ℝ) (hf : Measurable f) (hfst : ∀ p, (f p).1 = p.1)
    (bin : α → ℤ) (hbin : Measurable bin)
    (hlam : lam ≤ ρ.restrict source) (hm0 : 0 < lam univ) (hmt : lam univ < ⊤)
    {m : ℝ≥0∞} (hm : m ≤ lam univ) :
    ∀ j : ℤ, m * normalizedMap lam f {p | bin p.1 = j} ≤
      ρ (source ∩ {p | bin p.1 = j}) := by
  intro j
  have hB : MeasurableSet {p : α × ℝ | bin p.1 = j} :=
    measurableSet_eq_fun (hbin.comp measurable_fst) measurable_const
  have hpre : f ⁻¹' {p : α × ℝ | bin p.1 = j} = {p | bin p.1 = j} := by
    ext p
    simp only [mem_preimage, mem_setOf_eq, hfst]
  calc
    _ ≤ lam univ * normalizedMap lam f {p | bin p.1 = j} := mul_le_mul' hm le_rfl
    _ = lam {p | bin p.1 = j} := by
      rw [normalizedMap, Measure.smul_apply, smul_eq_mul, Measure.map_apply hf hB,
        hpre, ← mul_assoc, ENNReal.mul_inv_cancel hm0.ne' hmt.ne, one_mul]
    _ ≤ (ρ.restrict source) {p | bin p.1 = j} := hlam _
    _ = _ := by rw [Measure.restrict_apply hB, inter_comm]

/-- The surviving total mass transports each event of a dominated probability
back to the same original, unnormalized event mass. -/
theorem mass_transport_of_scaled_domination {Ω : Type*} [MeasurableSpace Ω]
    (σ μ : Measure Ω) {M m : ℝ≥0∞} (hM0 : M ≠ 0) (hMt : M ≠ ⊤)
    (hm : m ≤ M) (hdom : σ ≤ M⁻¹ • μ) (B : Set Ω) : m * σ B ≤ μ B := by
  calc
    _ ≤ M * σ B := mul_le_mul' hm le_rfl
    _ ≤ M * (M⁻¹ • μ) B := mul_le_mul' le_rfl (hdom B)
    _ = _ := by
      rw [Measure.smul_apply, smul_eq_mul, ← mul_assoc,
        ENNReal.mul_inv_cancel hM0 hMt, one_mul]

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- Change time only; the original trajectory and its exact intercept bin are retained. -/
def normalizeTime (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) (p : α × ℝ) : α × ℝ :=
  (p.1, (p.2 - cfg.blockLeft k s i) / cfg.timeLength k s)

theorem measurable_normalizeTime (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) :
    Measurable (cfg.normalizeTime k s i) := by
  unfold normalizeTime
  fun_prop

theorem normalizeTime_fst (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) (p : α × ℝ) :
    (cfg.normalizeTime k s i p).1 = p.1 := rfl

theorem normalizeTime_roundtrip (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) (p : α × ℝ) :
    cfg.blockLeft k s i + cfg.timeLength k s * (cfg.normalizeTime k s i p).2 = p.2 := by
  dsimp [normalizeTime]
  field_simp [(cfg.timeLength_pos k s).ne']
  ring

theorem centeredLine_normalizeTime (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) (p : α × ℝ) :
    cfg.centeredLine k s i p.1 (cfg.normalizeTime k s i p).2 = cfg.framedPoint k s i p := by
  unfold centeredLine
  rw [cfg.normalizeTime_roundtrip]

theorem normalizeTime_mem_unit (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) {p : α × ℝ}
    (hp : p.2 ∈ I (cfg.T k s) (cfg.j k s i)) :
    (cfg.normalizeTime k s i p).2 ∈ Icc (0 : ℝ) 1 := by
  rw [cfg.block_interval] at hp
  change (p.2 - cfg.blockLeft k s i) / cfg.timeLength k s ∈ Icc (0 : ℝ) 1
  exact ⟨div_nonneg (sub_nonneg.mpr hp.1) (cfg.timeLength_pos k s).le,
    (div_le_one (cfg.timeLength_pos k s)).mpr (by linarith [hp.2])⟩

/-- The inverse time change, used to keep good events measurable on arbitrary trajectory spaces. -/
def physicalTime (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) (p : α × ℝ) : α × ℝ :=
  (p.1, cfg.blockLeft k s i + cfg.timeLength k s * p.2)

theorem measurable_physicalTime (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) :
    Measurable (cfg.physicalTime k s i) := by
  unfold physicalTime
  fun_prop

theorem physicalTime_normalizeTime (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) (p : α × ℝ) :
    cfg.physicalTime k s i (cfg.normalizeTime k s i p) = p := by
  apply Prod.ext
  · rfl
  · exact cfg.normalizeTime_roundtrip k s i p

theorem normalizeTime_physicalTime (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) (p : α × ℝ) :
    cfg.normalizeTime k s i (cfg.physicalTime k s i p) = p := by
  apply Prod.ext
  · rfl
  · dsimp [normalizeTime, physicalTime]
    field_simp [(cfg.timeLength_pos k s).ne']
    ring

/-- Affine time normalization is a measurable equivalence preserving the original trajectory. -/
def timeEquiv (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) : (α × ℝ) ≃ᵐ (α × ℝ) where
  toFun := cfg.normalizeTime k s i
  invFun := cfg.physicalTime k s i
  left_inv := cfg.physicalTime_normalizeTime k s i
  right_inv := cfg.normalizeTime_physicalTime k s i
  measurable_toFun := cfg.measurable_normalizeTime k s i
  measurable_invFun := cfg.measurable_physicalTime k s i

end Data

end

end Submission.Obl.k4_critical_switching_state_preparation
