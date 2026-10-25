import Submission.Obl.k4_critical_switching_state_preparation.Transport
import Submission.Obl.k4_critical_switching_state_preparation.CriticalSource

namespace Submission.Obl.k4_critical_switching_state_preparation

open Set MeasureTheory Inherited

noncomputable section

open scoped ENNReal

/-- Injective natural-number coding preserves conditional state ceilings. -/
theorem palette_cap_of_encode {Ω Q : Type*} [MeasurableSpace Ω] [Encodable Q]
    (μ : Measure Ω) (key : Ω → Q) (Z : Ω → ℤ) (P : ℤ → ℝ≥0∞) (C : ℝ≥0∞)
    (hcap : ∀ u j, μ {p | key p = u ∧ Z p = j} ≤ C * μ {p | key p = u} * P j) :
    ∀ (q : ℕ) (j : ℤ), μ {p | Encodable.encode (key p) = q ∧ Z p = j} ≤
      C * μ {p | Encodable.encode (key p) = q} * P j := by
  intro q j
  by_cases hq : ∃ u : Q, Encodable.encode u = q
  · obtain ⟨u, rfl⟩ := hq
    simpa only [Encodable.encode_inj] using hcap u j
  · have heq : {p | Encodable.encode (key p) = q ∧ Z p = j} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hq ⟨key p, hp.1⟩
    rw [heq, measure_empty]
    exact bot_le

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The exact original pair code evaluated at normalized time. -/
def normalizedPair (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ)
    (a ω : ℝ) (p : α × ℝ) : ℤ × (Fin 3 → ℤ) :=
  cfg.sourcePair k s i L a ω (cfg.physicalTime k s i p)

theorem measurable_normalizedPair (h : cfg.Valid) (k : ℕ) (s : ℝ)
    (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) (a ω : ℝ) :
    Measurable (cfg.normalizedPair k s i L a ω) :=
  (measurable_sourcePair h k s i L a ω).comp (cfg.measurable_physicalTime k s i)

theorem normalizedPair_key (k : ℕ) (s v : ℝ) (i : Fin (cfg.n k s))
    (L : Fin 4 → ℝ) (ω : ℝ) (p : α × ℝ) :
    cfg.normalizedPair k s i L (cfg.N k ^ (-s - v)) ω p =
      (cfg.midpointBin k s v i L p.1,
        fun e => ⌊cfg.centeredLine k s i p.1 p.2 e / ω⌋) := rfl

/-- A countable fine state records precisely the original intercept bin and
normalized base cell. The natural-number coding loses no information. -/
def fineState (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ)
    (ω : ℝ) (p : α × ℝ) : ℕ :=
  Encodable.encode (cfg.sourcePair k s i L (cfg.N k ^ (-s - s / 16)) ω
    (cfg.physicalTime k s i p))

theorem measurable_fineState (h : cfg.Valid) (k : ℕ) (s : ℝ)
    (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) (ω : ℝ) :
    Measurable (cfg.fineState k s i L ω) := by
  exact (measurable_of_countable Encodable.encode).comp
    ((measurable_sourcePair h k s i L _ ω).comp (cfg.measurable_physicalTime k s i))

theorem fineState_key (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s))
    (L : Fin 4 → ℝ) (ω : ℝ) (p : α × ℝ) :
    cfg.fineState k s i L ω p = Encodable.encode
      (cfg.midpointBin k s (s / 16) i L p.1,
        fun e => ⌊cfg.centeredLine k s i p.1 p.2 e / ω⌋) := by
  rw [fineState, physicalTime, sourcePair_normalized_time]

/-- Equal states preserve the exact original intercept bin and give the
required coordinate diameter at the fine switching mesh. -/
theorem fineState_diameter (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s))
    (L : Fin 4 → ℝ) {ω : ℝ} (hω : 0 < ω) {p q : α × ℝ}
    (heq : cfg.fineState k s i L ω p = cfg.fineState k s i L ω q) :
    cfg.midpointBin k s (s / 16) i L p.1 = cfg.midpointBin k s (s / 16) i L q.1 ∧
      ∀ e, |cfg.centeredLine k s i p.1 p.2 e - cfg.centeredLine k s i q.1 q.2 e| ≤ ω := by
  rw [fineState_key, fineState_key] at heq
  have hk := Encodable.encode_injective heq
  refine ⟨congrArg Prod.fst hk, ?_⟩
  have hcell : cfg.centeredLine k s i p.1 p.2 ∈
      contactGridCell ω (fun e => ⌊cfg.centeredLine k s i q.1 q.2 e / ω⌋) :=
    fun e => congrFun (congrArg Prod.snd hk) e
  exact contactGridCell_coordinate_gap hω hcell (fun _ => rfl)

end Data

end

end Submission.Obl.k4_critical_switching_state_preparation
