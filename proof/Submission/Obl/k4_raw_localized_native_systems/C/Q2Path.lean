import Submission.Obl.k4_raw_localized_native_systems.C.WorldBadPair
import Submission.Obl.k4_raw_localized_native_systems.C.PathTags

/-
Adapted from this LOT tree, o178, session x0596, `Q2Path.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# The good path of a later chart system, and its strip data

For a chart system `a` (o153 `Atlas`) in one world, the good path consists of
its selected incidences, at their own block index, that are good for the
terminal angular cap, typical at depth zero and the terminal depth from below,
satisfy the native bounds, and have bounded position and velocity.  Each such
incidence is tagged by its own chart.  Its line satisfies the minor-axis normal
position and velocity constraints of that chart, extended over the whole unit
interval, with width `ρ ≥ √|det Q| κ (1 + 2 ⋅ 2^T)`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

variable {p : Data} {k : ℕ} (a : Atlas p k) (γ : Fin (p.W k))

/-- The good path of a chart system in one world. -/
def goodPath (u τ κ' lam : ℝ) : Set Point :=
  {q | (∃ b, TagPred a γ q b ∧ q ∈ a.F b ∧ lam ≤ ‖longCol (a.Q b)‖) ∧ AngGood p k γ u τ q ∧ Typ0 p k γ τ q ∧
    NativeOK p k γ κ' q ∧ ‖y q.1 0‖ + ‖v q.1‖ ≤ κ'}

/-- The geometric chart hypotheses used along the path (all clauses of the frozen
`chart`, with an arbitrary extra clause). -/
def ChartsHyp (M D : ℕ) (κ r : ℝ) (ex : Fin a.C → Prop) : Prop :=
  ∀ b, chart (p.N k) M D κ a.T ((a.j b : ℕ) : ℝ) r (p.B k (a.γ b)) (p.E k (a.γ b))
    (a.c b) (a.u b) (a.Q b) (a.R b) (a.A b) (a.F b) (ex b)

section

variable {a γ}
variable {M D : ℕ} {κ r : ℝ} {ex : Fin a.C → Prop}

theorem ChartsHyp.det_ne (h : ChartsHyp a M D κ r ex) (b : Fin a.C) : (a.Q b).det ≠ 0 := (h b).1

theorem ChartsHyp.measA (h : ChartsHyp a M D κ r ex) (b : Fin a.C) : MeasurableSet (a.A b) :=
  (h b).2.2.2.2.2.2.1

theorem ChartsHyp.measF (h : ChartsHyp a M D κ r ex) (b : Fin a.C) : MeasurableSet (a.F b) :=
  (h b).2.2.2.2.2.2.2.1

theorem ChartsHyp.frame (h : ChartsHyp a M D κ r ex) (b : Fin a.C) {l : Line} (hl : l ∈ a.A b)
    {t : ℝ} (ht : t ∈ Set.Icc ((a.j b : ℕ) / (2 : ℝ) ^ a.T) (((a.j b : ℕ) + 1) / (2 : ℝ) ^ a.T)) :
    ‖Matrix.toEuclideanLin (a.Q b)⁻¹ (y l t - a.c b - t • a.u b)‖ ≤ κ :=
  (((h b).2.2.2.2.2.2.2.2.2.1 l hl).2.2 t ht).1

theorem ChartsHyp.selected (h : ChartsHyp a M D κ r ex) (b : Fin a.C) {q : Point}
    (hq : q ∈ a.F b) : q ∈ p.E k (a.γ b) ∧ q.1 ∈ a.A b ∧
      q.2 ∈ Set.Icc ((a.j b : ℕ) / (2 : ℝ) ^ a.T) (((a.j b : ℕ) + 1) / (2 : ℝ) ^ a.T) := by
  obtain ⟨h1, h2, h3, -⟩ := (h b).2.2.2.2.2.2.2.2.2.2.1 q hq
  exact ⟨h1, h2, h3⟩

end

theorem measurableSet_goodPath {u τ κ' lam : ℝ} (hp : Valid p) {M D : ℕ} {κ r : ℝ}
    {ex : Fin a.C → Prop} (hc : ChartsHyp a M D κ r ex)
    (hu : 0 < u) (huη : u ≤ p.η * p.L) : MeasurableSet (goodPath a γ u τ κ' lam) := by
  have hL : 0 ≤ p.L := hp.length_pos.le
  obtain ⟨hGm, -⟩ := valid_G_spec hp k γ hu huη
  obtain ⟨hgm, -⟩ := valid_g_spec hp k γ hL le_rfl
  obtain ⟨hg0m, -⟩ := valid_g_spec hp k γ le_rfl hL
  have hobsL := measurable_obs' (p.B k γ) (δ (p.N k) p.L)
  have hobs0 := measurable_obs' (p.B k γ) (δ (p.N k) 0)
  have hjoint : Measurable (jointObs (p.B k γ) (p.N k) p.L u) := by
    rw [jointObs_eq]; exact hobsL.prodMk (measurable_velBin _ _)
  have hx : Measurable (fun q : Point => x q.1 q.2) := by
    unfold x; fun_prop
  have hev : ∀ R : MvPolynomial (Fin 4) ℝ, Measurable (fun q : Point => MvPolynomial.eval (x q.1 q.2) R) :=
    fun R => (MvPolynomial.continuous_eval R).measurable.comp hx
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_
    (MeasurableSet.inter ?_ ?_)))
  · have : {q : Point | ∃ b, TagPred a γ q b ∧ q ∈ a.F b ∧ lam ≤ ‖longCol (a.Q b)‖} =
        ⋃ b, {q | TagPred a γ q b} ∩ a.F b ∩ {_q | lam ≤ ‖longCol (a.Q b)‖} := by
      ext q; simp [and_assoc]
    have h1 : MeasurableSet
        {q : Point | ∃ b, TagPred a γ q b ∧ q ∈ a.F b ∧ lam ≤ ‖longCol (a.Q b)‖} := by
      rw [this]
      refine MeasurableSet.iUnion fun b =>
        ((measurableSet_tagPred a γ hc.measA b).inter (hc.measF b)).inter ?_
      by_cases h : lam ≤ ‖longCol (a.Q b)‖
      · simp [h]
      · simp [h]
    exact h1
  · exact (measurableSet_le (hGm.comp hjoint) measurable_const).inter
      (measurableSet_le measurable_const (hgm.comp hobsL))
  · exact measurableSet_le (hg0m.comp hobs0) measurable_const
  · refine MeasurableSet.inter (measurableSet_le (hev _).abs measurable_const)
      (MeasurableSet.inter (measurableSet_le (hev _).abs measurable_const)
        (MeasurableSet.inter (measurableSet_le (hev _).abs measurable_const)
          (measurableSet_le measurable_const (hev _).abs)))
  · have hy : Measurable (fun q : Point => ‖y q.1 0‖ + ‖v q.1‖) := by
      unfold y v x; fun_prop
    exact measurableSet_le hy measurable_const

/-- Every incidence of the good path is tagged by a chart that selects it. -/
theorem goodPath_tag {u τ κ' lam : ℝ} {M D : ℕ} {κ r : ℝ} {ex : Fin a.C → Prop}
    (hc : ChartsHyp a M D κ r ex)
    (hdisj : ∀ b b', b ≠ b' → a.γ b = a.γ b' → a.j b = a.j b' → Disjoint (a.A b) (a.A b'))
    (hC : 0 < a.C) {q : Point} (hq : q ∈ goodPath a γ u τ κ' lam) :
    TagPred a γ q (tagOf a γ hC q) ∧ q ∈ a.F (tagOf a γ hC q) ∧
      lam ≤ ‖longCol (a.Q (tagOf a γ hC q))‖ := by
  obtain ⟨⟨b, hb, hF, hlong⟩, -⟩ := hq
  rw [tagOf_eq a γ hC hdisj hb]
  exact ⟨hb, hF, hlong⟩

end

end Submission.Obl.k4_raw_localized_native_systems.C
