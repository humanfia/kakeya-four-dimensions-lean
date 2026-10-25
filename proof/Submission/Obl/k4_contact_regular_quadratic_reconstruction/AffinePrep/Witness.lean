import Submission.Obl.k4_contact_regular_quadratic_reconstruction.Model

/-!
# The shifted witness set: measurability, null exceptions, and time trimming
-/

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep

open MeasureTheory Set MvPolynomial Filter
open Submission.Obl.k4_critical_switching_state_preparation.Data

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- The witness set of `Model.ShiftedCandidate`. -/
def shiftedWitness (cfg : Model α) (k : ℕ) (s v ε : ℝ) (i : Fin (cfg.n k s))
    (L : Fin 4 → ℝ) (G : MvPolynomial (Fin 4) ℝ) : Set (α × ℝ) :=
  {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ I (cfg.T k s) (cfg.j k s i) ∧
      (∀ t ∈ I (cfg.T k s) (cfg.j k s i),
        |cfg.shiftedPoint k L p.1 t 3| ≤ 1 ∧
        |eval (cfg.shiftedPoint k L p.1 t) G| ≤ cfg.N k ^ ε * cfg.N k ^ (-s - v) ∧
        |eval (cfg.shiftedPoint k L p.1 t) (pderiv (3 : Fin 4) G)| ≤ cfg.N k ^ ε ∧
        |eval (cfg.shiftedPoint k L p.1 t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) G))| ≤
          cfg.N k ^ ε / cfg.N k ^ (-s - v)) ∧
      cfg.N k ^ (-ε) ≤ |eval (cfg.shiftedPoint k L p.1 p.2) (pderiv (3 : Fin 4) G)|}

theorem shiftedCandidate_iff (cfg : Model α) (k : ℕ) (s v ε R : ℝ) (i : Fin (cfg.n k s)) :
    cfg.ShiftedCandidate k s v ε R i ↔
      ∃ (L : Fin 4 → ℝ) (G : MvPolynomial (Fin 4) ℝ), G.totalDegree ≤ 2 ∧
        (∀ e, |G.coeff e| ≤ cfg.N k ^ R) ∧
        ENNReal.ofReal (cfg.N k ^ (-cfg.d * v - ε) / (2 : ℝ) ^ cfg.T k s) *
          cfg.ν k (cfg.A k s i) ≤ cfg.ρ k (shiftedWitness cfg k s v ε i L G) :=
  Iff.rfl

/-- The shifted point as a function of the line coefficients. -/
def shiftedPt (L : Fin 4 → ℝ) (β : Fin 6 → ℝ) (t : ℝ) : Fin 4 → ℝ :=
  ![t, β 0 + t * β 3, β 1 + t * β 4,
    β 2 + t * β 5 - (L 0 + L 1 * t + L 2 * (β 0 + t * β 3) + L 3 * (β 1 + t * β 4))]

theorem shiftedPoint_eq (cfg : Model α) (k : ℕ) (L : Fin 4 → ℝ) (l : α) (t : ℝ) :
    cfg.shiftedPoint k L l t = shiftedPt L (cfg.b k l) t := by
  funext m
  fin_cases m <;> simp [Model.shiftedPoint, shiftedPt, x]

theorem continuous_shiftedPt (L : Fin 4 → ℝ) :
    Continuous (fun x : (Fin 6 → ℝ) × ℝ => shiftedPt L x.1 x.2) := by
  unfold shiftedPt
  fun_prop

theorem continuous_shiftedPt_t (L : Fin 4 → ℝ) (t : ℝ) :
    Continuous (fun β : Fin 6 → ℝ => shiftedPt L β t) := by
  unfold shiftedPt
  fun_prop

theorem shiftedPt_three (L : Fin 4 → ℝ) (β : Fin 6 → ℝ) (t : ℝ) :
    shiftedPt L β t 3 =
      β 2 + t * β 5 - (L 0 + L 1 * t + L 2 * (β 0 + t * β 3) + L 3 * (β 1 + t * β 4)) := rfl

theorem continuous_eval_shiftedPt (L : Fin 4 → ℝ) (Q : MvPolynomial (Fin 4) ℝ) :
    Continuous (fun x : (Fin 6 → ℝ) × ℝ => eval (shiftedPt L x.1 x.2) Q) :=
  (MvPolynomial.continuous_eval Q).comp (continuous_shiftedPt L)

/-- The full-block condition is closed in the line coefficients. -/
theorem isClosed_fullBlock (L : Fin 4 → ℝ) (G : MvPolynomial (Fin 4) ℝ) (J : Set ℝ)
    (c₁ c₂ c₃ c₄ : ℝ) :
    IsClosed {β : Fin 6 → ℝ | ∀ t ∈ J,
      |shiftedPt L β t 3| ≤ c₁ ∧ |eval (shiftedPt L β t) G| ≤ c₂ ∧
      |eval (shiftedPt L β t) (pderiv (3 : Fin 4) G)| ≤ c₃ ∧
      |eval (shiftedPt L β t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) G))| ≤ c₄} := by
  have hc : ∀ (t : ℝ) (Q : MvPolynomial (Fin 4) ℝ),
      Continuous fun β : Fin 6 → ℝ => eval (shiftedPt L β t) Q :=
    fun t Q => (MvPolynomial.continuous_eval Q).comp (continuous_shiftedPt_t L t)
  have h3 : ∀ t : ℝ, Continuous fun β : Fin 6 → ℝ => shiftedPt L β t 3 := by
    intro t
    simp only [shiftedPt_three]
    fun_prop
  have hpt : ∀ t : ℝ, IsClosed {β : Fin 6 → ℝ |
      |shiftedPt L β t 3| ≤ c₁ ∧ |eval (shiftedPt L β t) G| ≤ c₂ ∧
      |eval (shiftedPt L β t) (pderiv (3 : Fin 4) G)| ≤ c₃ ∧
      |eval (shiftedPt L β t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) G))| ≤ c₄} := by
    intro t
    exact (isClosed_le (continuous_abs.comp (h3 t)) continuous_const).inter
      ((isClosed_le (continuous_abs.comp (hc t G)) continuous_const).inter
        ((isClosed_le (continuous_abs.comp (hc t _)) continuous_const).inter
          (isClosed_le (continuous_abs.comp (hc t _)) continuous_const)))
  have e : {β : Fin 6 → ℝ | ∀ t ∈ J,
      |shiftedPt L β t 3| ≤ c₁ ∧ |eval (shiftedPt L β t) G| ≤ c₂ ∧
      |eval (shiftedPt L β t) (pderiv (3 : Fin 4) G)| ≤ c₃ ∧
      |eval (shiftedPt L β t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) G))| ≤ c₄} =
      ⋂ t ∈ J, {β : Fin 6 → ℝ |
      |shiftedPt L β t 3| ≤ c₁ ∧ |eval (shiftedPt L β t) G| ≤ c₂ ∧
      |eval (shiftedPt L β t) (pderiv (3 : Fin 4) G)| ≤ c₃ ∧
      |eval (shiftedPt L β t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) G))| ≤ c₄} := by
    ext β
    simp only [mem_setOf_eq, mem_iInter]
  rw [e]
  exact isClosed_biInter fun t _ => hpt t

theorem measurableSet_shiftedWitness (cfg : Model α) (k : ℕ) (s v ε : ℝ)
    (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) (G : MvPolynomial (Fin 4) ℝ)
    (hb : Measurable (cfg.b k)) (hB : MeasurableSet (cfg.B k s i)) :
    MeasurableSet (shiftedWitness cfg k s v ε i L G) := by
  have hbp : Measurable fun p : α × ℝ => cfg.b k p.1 := hb.comp measurable_fst
  have hjoint : Measurable fun p : α × ℝ => ((cfg.b k p.1, p.2) : (Fin 6 → ℝ) × ℝ) :=
    hbp.prodMk measurable_snd
  have h3 : MeasurableSet {p : α × ℝ | ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
        |cfg.shiftedPoint k L p.1 t 3| ≤ 1 ∧
        |eval (cfg.shiftedPoint k L p.1 t) G| ≤ cfg.N k ^ ε * cfg.N k ^ (-s - v) ∧
        |eval (cfg.shiftedPoint k L p.1 t) (pderiv (3 : Fin 4) G)| ≤ cfg.N k ^ ε ∧
        |eval (cfg.shiftedPoint k L p.1 t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) G))| ≤
          cfg.N k ^ ε / cfg.N k ^ (-s - v)} := by
    have e : {p : α × ℝ | ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
        |cfg.shiftedPoint k L p.1 t 3| ≤ 1 ∧
        |eval (cfg.shiftedPoint k L p.1 t) G| ≤ cfg.N k ^ ε * cfg.N k ^ (-s - v) ∧
        |eval (cfg.shiftedPoint k L p.1 t) (pderiv (3 : Fin 4) G)| ≤ cfg.N k ^ ε ∧
        |eval (cfg.shiftedPoint k L p.1 t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) G))| ≤
          cfg.N k ^ ε / cfg.N k ^ (-s - v)} =
        (fun p : α × ℝ => cfg.b k p.1) ⁻¹' {β : Fin 6 → ℝ | ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
          |shiftedPt L β t 3| ≤ 1 ∧
          |eval (shiftedPt L β t) G| ≤ cfg.N k ^ ε * cfg.N k ^ (-s - v) ∧
          |eval (shiftedPt L β t) (pderiv (3 : Fin 4) G)| ≤ cfg.N k ^ ε ∧
          |eval (shiftedPt L β t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) G))| ≤
            cfg.N k ^ ε / cfg.N k ^ (-s - v)} := by
      ext p
      simp only [mem_setOf_eq, mem_preimage, shiftedPoint_eq]
    rw [e]
    exact hbp (isClosed_fullBlock L G _ _ _ _ _).measurableSet
  have h4 : MeasurableSet {p : α × ℝ |
      cfg.N k ^ (-ε) ≤ |eval (cfg.shiftedPoint k L p.1 p.2) (pderiv (3 : Fin 4) G)|} := by
    have e : {p : α × ℝ |
        cfg.N k ^ (-ε) ≤ |eval (cfg.shiftedPoint k L p.1 p.2) (pderiv (3 : Fin 4) G)|} =
        {p : α × ℝ |
          cfg.N k ^ (-ε) ≤ |eval (shiftedPt L (cfg.b k p.1) p.2) (pderiv (3 : Fin 4) G)|} := by
      ext p
      simp only [mem_setOf_eq, shiftedPoint_eq]
    rw [e]
    have hc : Continuous fun x : (Fin 6 → ℝ) × ℝ =>
        |eval (shiftedPt L x.1 x.2) (pderiv (3 : Fin 4) G)| :=
      continuous_abs.comp (continuous_eval_shiftedPt L (pderiv (3 : Fin 4) G))
    have hm := hc.measurable.comp hjoint
    exact measurableSet_le measurable_const hm
  have h1 : MeasurableSet {p : α × ℝ | p.1 ∈ cfg.B k s i} := measurable_fst hB
  have h2 : MeasurableSet {p : α × ℝ | p.2 ∈ I (cfg.T k s) (cfg.j k s i)} :=
    measurable_snd measurableSet_Icc
  have hall := h1.inter (h2.inter (h3.inter h4))
  exact hall

/-- The incidences with bounded horizontal coefficients and the contact equation. -/
def goodSet (cfg : Model α) (k : ℕ) : Set (α × ℝ) :=
  {p | |cfg.b k p.1 0| + |cfg.b k p.1 1| + |cfg.b k p.1 3| + |cfg.b k p.1 4| ≤ cfg.K k ∧
    |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀)}

theorem measurableSet_goodSet (cfg : Model α) (k : ℕ) (hb : Measurable (cfg.b k)) :
    MeasurableSet (goodSet cfg k) := by
  have hbp : Measurable fun p : α × ℝ => cfg.b k p.1 := hb.comp measurable_fst
  have hc : ∀ m : Fin 6, Measurable fun p : α × ℝ => cfg.b k p.1 m :=
    fun m => (measurable_pi_apply m).comp hbp
  have hab : ∀ m : Fin 6, Measurable fun p : α × ℝ => |cfg.b k p.1 m| :=
    fun m => continuous_abs.measurable.comp (hc m)
  refine MeasurableSet.inter ?_ ?_
  · exact measurableSet_le ((((hab 0).add (hab 1)).add (hab 3)).add (hab 4)) measurable_const
  · exact measurableSet_le (continuous_abs.measurable.comp ((hc 4).add (hc 0))) measurable_const

theorem ae_goodSet {cfg : Model α} (h : cfg.Valid) (k : ℕ) : ∀ᵐ p ∂cfg.μ k, p ∈ goodSet cfg k := by
  obtain ⟨_, hν, _, hdom, _, _, _, _, hbnd, _⟩ := h.basic k
  have : IsProbabilityMeasure (cfg.ν k) := hν
  have h1 : ∀ᵐ p ∂cfg.μ k, |cfg.b k p.1 0| + |cfg.b k p.1 1| + |cfg.b k p.1 3| +
      |cfg.b k p.1 4| ≤ cfg.K k :=
    (ae_mono hdom) (Measure.ae_smul_measure (Measure.quasiMeasurePreserving_fst.ae hbnd) _)
  filter_upwards [h1, h.contact k] with p hp1 hp2
  exact ⟨hp1, hp2⟩

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep
