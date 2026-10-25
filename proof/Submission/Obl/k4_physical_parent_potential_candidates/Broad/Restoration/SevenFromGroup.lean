-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/SevenFromGroup.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/SevenFromGroup.lean (session x0945).
-- Existing source attributions are preserved below.

import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.SevenCells
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.PhysicalExit

/-!
# Seven directions from the cells of a physical group

`seven_directions_of_cells` asks for conditional velocity laws on cells of the normalized unit
ball and for tubes of certified group points realizing every charged central velocity bin. For a
physical group (a set `Gev` of events whose lines are group points for time `τw` about each
event) these are built here in any normalization `c + M x` with explicit inverse:

* the normalized base point moves along a line with direction `lineDir M l`, whose time component
  is positive, and the normalized velocity is `lineVelocity M l` (`lineDir = D₀ • lift v`);
* the conditional law of a cell is the normalized velocity law of the group events in it;
* a charged central bin contains the velocity of some event of the cell, and the event's line,
  for the time `(8 At D₀)⁻¹` about it, is the required tube (`certifiedGroupPoint_of_physical`).

The breadth, palette, tail and density assumptions are stated directly for the group measure.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open Metric Set MeasureTheory MvPolynomial
open GeneralPositionSampling
open scoped ENNReal

/-- The direction in which the normalized base point of a line moves, per unit of time. -/
def lineDir (M : Matrix (Fin 3) (Fin 3) ℝ) (l : Line) : Base :=
  WithLp.toLp 2 (fun i => M i 0 + M i 1 * l.2 3 + M i 2 * l.2 4)

/-- The normalized velocity of a line: its direction divided by the time component. -/
def lineVelocity (M : Matrix (Fin 3) (Fin 3) ℝ) (l : Line) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![lineDir M l 1 / lineDir M l 0, lineDir M l 2 / lineDir M l 0]

lemma lineDir_eq_smul_lift (M : Matrix (Fin 3) (Fin 3) ℝ) (l : Line) (h0 : lineDir M l 0 ≠ 0) :
    lineDir M l = lineDir M l 0 • lift (lineVelocity M l) := by
  ext i
  fin_cases i <;> simp [lift, lineVelocity] <;> field_simp

lemma normalizedBase_graphPoint (c : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (B : ℝ)
    (l : Line) (s s₀ : ℝ) :
    normalizedBase c M B (graphPoint l s) =
      normalizedBase c M B (graphPoint l s₀) + (s - s₀) • lineDir M l := by
  ext i
  simp only [normalizedBase, pointOfCoordinates, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    lineDir]
  rw [coordinateMap_castSucc, coordinateMap_castSucc]
  simp only [graphPoint, Fin.sum_univ_three, Fin.castSucc_zero, Fin.castSucc_one,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have h2 : (2 : Fin 3).castSucc = (2 : Fin 4) := rfl
  rw [h2]
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  ring

lemma hidden_graphPoint (c : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (B : ℝ) (l : Line)
    (s s₀ : ℝ) :
    (pointOfCoordinates (coordinateMap c M B (graphPoint l s))).2 =
      (pointOfCoordinates (coordinateMap c M B (graphPoint l s₀))).2 + (s - s₀) * (B * l.2 5) := by
  simp only [pointOfCoordinates, coordinateMap, graphPoint]
  simp
  ring

lemma measurable_lineVelocity (M : Matrix (Fin 3) (Fin 3) ℝ) :
    Measurable (fun p : Event => lineVelocity M p.1) := by
  have hc : ∀ i, Measurable (fun p : Event => lineDir M p.1 i) := by
    intro i
    simp only [lineDir, PiLp.toLp_apply]
    fun_prop
  unfold lineVelocity
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  refine measurable_pi_iff.mpr fun k => ?_
  fin_cases k
  · exact Measurable.div (hc 1) (hc 0)
  · exact Measurable.div (hc 2) (hc 0)

/-- **Seven directions from the cells of a physical group.** -/
theorem seven_directions_of_group {c c' : Fin 3 → ℝ} {M M' : Matrix (Fin 3) (Fin 3) ℝ}
    {B B' : ℝ} (hM : M' * M = 1) (hc : ∀ k, c' k = -∑ j : Fin 3, M' k j * c j)
    (hB : B' * B = 1) {R0 Rc : Poly} {Pot : MvPolynomial (Fin 3) ℝ}
    {εfit A₁ σ Vc At A0 θ h hc0 τw : ℝ}
    (μ0 : Measure Event) (Gev : Set Event) (hGm : MeasurableSet Gev)
    (hline : ∀ p ∈ Gev, 0 < lineDir M p.1 0 ∧ (8 * At * lineDir M p.1 0)⁻¹ ≤ τw ∧
      ∀ s, |s - p.2| ≤ τw → PhysicalGroupPoint B' R0 Rc Pot εfit A₁ σ Vc (graphPoint p.1 s))
    {ι : Type*} [Fintype ι] (cell : ι → Set Base) (hcell : ∀ s, MeasurableSet (cell s))
    (hdisj : Pairwise (Function.onFun Disjoint cell))
    (hcellBall : ∀ s, cell s ⊆ closedBall (0 : Base) 1)
    (hdiam : ∀ s, ∀ u ∈ cell s, ∀ y ∈ cell s, ‖u - y‖ ≤ hc0)
    (hpos : ∀ s, μ0 (Gev ∩ (fun p : Event => normalizedBase c M B (graphPoint p.1 p.2)) ⁻¹'
      cell s) ≠ 0)
    (hfin : ∀ s, μ0 (Gev ∩ (fun p : Event => normalizedBase c M B (graphPoint p.1 p.2)) ⁻¹'
      cell s) ≠ ∞)
    (βc : ℝ≥0∞) (hcap : ∀ s, μ0 (Gev ∩ (fun p : Event =>
      normalizedBase c M B (graphPoint p.1 p.2)) ⁻¹' cell s) ≤ βc * volume (cell s))
    (π : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure π] (hπ0 : π univ ≠ 0)
    {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hdom : ∀ s (U : Set (EuclideanSpace ℝ (Fin 2))), MeasurableSet U →
      μ0 (Gev ∩ (fun p : Event => normalizedBase c M B (graphPoint p.1 p.2)) ⁻¹' cell s ∩
        (fun p : Event => lineVelocity M p.1) ⁻¹' U) ≤
      K * π U * μ0 (Gev ∩ (fun p : Event => normalizedBase c M B (graphPoint p.1 p.2)) ⁻¹'
        cell s))
    {δ R w : ℝ} (hδ : 0 < δ) (hw : 0 < w) {κ τ : ℝ≥0∞}
    (hb : ∀ s (m : EuclideanSpace ℝ (Fin 2)) (c₀ : ℝ), ‖m‖ = 1 →
      μ0 (Gev ∩ (fun p : Event => normalizedBase c M B (graphPoint p.1 p.2)) ⁻¹' cell s ∩
        (fun p : Event => lineVelocity M p.1) ⁻¹' {x | |inner ℝ m x - c₀| ≤ δ}) ≤
      κ * μ0 (Gev ∩ (fun p : Event => normalizedBase c M B (graphPoint p.1 p.2)) ⁻¹' cell s))
    (htail : ∀ s, μ0 (Gev ∩ (fun p : Event => normalizedBase c M B (graphPoint p.1 p.2)) ⁻¹'
        cell s ∩ (fun p : Event => lineVelocity M p.1) ⁻¹' {v | R < ‖v‖}) ≤
      τ * μ0 (Gev ∩ (fun p : Event => normalizedBase c M B (graphPoint p.1 p.2)) ⁻¹' cell s))
    (hgood : 686 * κ + 7 * τ < 1) (hne : Nonempty ι)
    (hAt : 0 ≤ At) (hR : 1 + 2 * (R + w) ^ 2 ≤ At ^ 2) (hch : hc0 ≤ h) (hwh : w ≤ h)
    (hθ1 : θ ≤ 1)
    (hdetA : A0⁻¹ ≤ δ ^ 2 - 4 * w * (2 * R + w / 2))
    (hvolA : 2 * K ^ 7 * (βc * ENNReal.ofReal A0⁻¹) ≤
      (1 - (686 * κ + 7 * τ)) * (∑ s, μ0 (Gev ∩ (fun p : Event =>
        normalizedBase c M B (graphPoint p.1 p.2)) ⁻¹' cell s)) / π univ ^ 7)
    (hβc0 : βc ≠ 0) (hβctop : βc ≠ ∞) (hK0 : K ≠ 0) :
    ∃ (p : Fin 7 → Base) (E : Set Base),
      (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ At) ∧
      (∀ i k l : Fin 7, i ≠ k → i ≠ l → k ≠ l →
        A0⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p k, p l] r) t)|) ∧
      MeasurableSet E ∧ E ⊆ closedBall (0 : Base) 1 ∧ ENNReal.ofReal A0⁻¹ ≤ volume E ∧
      ∀ u ∈ E, ∀ i, CertifiedTubeWitness (transportPolynomial c' M' B' R0)
        (basePullback c' M' Pot) (transportPolynomial c' M' B' Rc) εfit A₁ σ Vc At θ h u
        (p i) := by
  classical
  set Zn : Event → Base := fun p => normalizedBase c M B (graphPoint p.1 p.2) with hZn
  set vel : Event → EuclideanSpace ℝ (Fin 2) := fun p => lineVelocity M p.1 with hvel
  have hZnm : Measurable Zn := measurable_eventBase c M B
  have hvelm : Measurable vel := measurable_lineVelocity M
  set G : ι → Set Event := fun s => Gev ∩ Zn ⁻¹' cell s with hGdef
  have hGsm : ∀ s, MeasurableSet (G s) := fun s => hGm.inter (hZnm (hcell s))
  set m : ι → ℝ≥0∞ := fun s => μ0 (G s) with hmdef
  set μ : ι → Measure (EuclideanSpace ℝ (Fin 2)) :=
    fun s => (m s)⁻¹ • (μ0.restrict (G s)).map vel with hμdef
  have hμapply : ∀ s (U : Set (EuclideanSpace ℝ (Fin 2))), MeasurableSet U →
      μ s U = (m s)⁻¹ * μ0 (G s ∩ vel ⁻¹' U) := by
    intro s U hU
    simp only [hμdef, Measure.smul_apply, smul_eq_mul]
    rw [Measure.map_apply hvelm hU, Measure.restrict_apply (hvelm hU), inter_comm]
  have hprob : ∀ s, IsProbabilityMeasure (μ s) := by
    intro s
    constructor
    rw [hμapply s univ MeasurableSet.univ, preimage_univ, inter_univ]
    exact ENNReal.inv_mul_cancel (hpos s) (hfin s)
  have hle : ∀ s {U : Set (EuclideanSpace ℝ (Fin 2))} {a : ℝ≥0∞}, MeasurableSet U →
      μ0 (G s ∩ vel ⁻¹' U) ≤ a * m s → μ s U ≤ a := by
    intro s U a hU hUa
    rw [hμapply s U hU]
    calc (m s)⁻¹ * μ0 (G s ∩ vel ⁻¹' U) ≤ (m s)⁻¹ * (a * m s) := by gcongr
      _ = a := by
        rw [mul_comm a, ← mul_assoc, ENNReal.inv_mul_cancel (hpos s) (hfin s), one_mul]
  have hbreadth : ∀ s, StripBreadth (μ s) δ κ := by
    intro s mv c₀ hmv
    have hmeas : MeasurableSet {x : EuclideanSpace ℝ (Fin 2) | |inner ℝ mv x - c₀| ≤ δ} :=
      measurableSet_le (by fun_prop) measurable_const
    exact hle s hmeas (hb s mv c₀ hmv)
  have hdomμ : ∀ s, μ s ≤ K • π := by
    intro s
    refine Measure.le_iff.mpr fun U hU => ?_
    have h := hle s hU (hdom s U hU)
    simpa only [Measure.smul_apply, smul_eq_mul] using h
  have htailμ : ∀ s, μ s {v | R < ‖v‖} ≤ τ := by
    intro s
    exact hle s (measurableSet_lt measurable_const continuous_norm.measurable) (htail s)
  have hM0 : ∑ s, m s ≠ 0 := by
    obtain ⟨s₀⟩ := hne
    intro hsum
    exact hpos s₀ ((Finset.sum_eq_zero_iff.mp hsum) s₀ (Finset.mem_univ _))
  have hMtop : ∑ s, m s ≠ ∞ := ENNReal.sum_ne_top.mpr fun s _ => hfin s
  refine seven_directions_of_cells cell hcell hdisj hcellBall hdiam m βc hcap μ π hπ0 hK hdomμ
    hδ hw hbreadth htailμ hgood hM0 hMtop hAt hR hch hwh hdetA hvolA hβc0 hβctop hK0 ?_
  -- every charged central bin is realized by the tube of a group line
  intro s β hcen hβ
  have hev : μ0 (G s ∩ vel ⁻¹' bin w β) ≠ 0 := by
    intro h0
    apply hβ
    rw [hμapply s _ (measurableSet_bin w β), h0, mul_zero]
  obtain ⟨p, ⟨hpG, hpcell⟩, hpbin⟩ := nonempty_of_measure_ne_zero hev
  obtain ⟨hD0, hDτ, hgp⟩ := hline p hpG
  set D₀ := lineDir M p.1 0 with hD₀
  have hvR : ∀ k, |vel p k| ≤ R + w := by
    intro k
    have h1 := abs_sub_binCenter_le hw hpbin k
    have h2 := hcen k
    have : |vel p k| ≤ |vel p k - binCenter w β k| + |binCenter w β k| := by
      have := abs_sub_abs_le_abs_sub (vel p k) (binCenter w β k)
      linarith
    linarith
  have hlift : ‖lift (vel p)‖ ≤ At := norm_lift_le (R := R + w) hAt hvR hR
  refine ⟨Zn p, hpcell, vel p, hpbin,
    (pointOfCoordinates (coordinateMap c M B (graphPoint p.1 p.2))).2,
    (B * p.1.2 5) / (8 * At * D₀), Icc (-1) 1, hcellBall s hpcell, measurableSet_Icc, le_rfl, ?_,
    ?_⟩
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · intro t ht
    have hAtpos : 0 < At := by
      have : (1 : ℝ) ≤ At ^ 2 := by nlinarith [sq_nonneg (R + w)]
      nlinarith [sq_nonneg At]
    set s' := p.2 + t / (8 * At * D₀) with hs'
    have hdt : |s' - p.2| ≤ τw := by
      rw [hs', add_sub_cancel_left, abs_div, abs_of_pos (by positivity : 0 < 8 * At * D₀)]
      calc |t| / (8 * At * D₀) ≤ 1 / (8 * At * D₀) := by
            gcongr; exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
        _ = (8 * At * D₀)⁻¹ := one_div _
        _ ≤ τw := hDτ
    have hphys := hgp s' hdt
    have hbase : (pointOfCoordinates (coordinateMap c M B (graphPoint p.1 s'))).1 =
        Zn p + t • ((8 * At)⁻¹ • lift (vel p)) := by
      have h1 := normalizedBase_graphPoint c M B p.1 s' p.2
      have h2 := lineDir_eq_smul_lift M p.1 hD0.ne'
      change normalizedBase c M B (graphPoint p.1 s') = _
      have hD0' : D₀ ≠ 0 := hD0.ne'
      have hAt' : At ≠ 0 := hAtpos.ne'
      have hcoef : t / (8 * At * D₀) * D₀ = t * (8 * At)⁻¹ := by
        field_simp
      rw [h1, h2, hs', add_sub_cancel_left, smul_smul, smul_smul, ← hD₀, hcoef]
    have hhid : (pointOfCoordinates (coordinateMap c M B (graphPoint p.1 s'))).2 =
        (pointOfCoordinates (coordinateMap c M B (graphPoint p.1 p.2))).2 +
          (B * p.1.2 5) / (8 * At * D₀) * t := by
      rw [hidden_graphPoint c M B p.1 s' p.2, hs', add_sub_cancel_left]
      ring
    have hball : (pointOfCoordinates (coordinateMap c M B (graphPoint p.1 s'))).1 ∈
        ball (0 : Base) 4 := by
      rw [hbase, mem_ball, dist_zero_right]
      have hZ1 := hcellBall s hpcell
      rw [mem_closedBall, dist_zero_right] at hZ1
      calc ‖Zn p + t • ((8 * At)⁻¹ • lift (vel p))‖
          ≤ ‖Zn p‖ + |t| * ((8 * At)⁻¹ * ‖lift (vel p)‖) := by
            refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < 8 * At))]
        _ ≤ 1 + 1 * ((8 * At)⁻¹ * At) := by
            gcongr
            · exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
        _ < 4 := by
            have : (8 * At)⁻¹ * At = 1 / 8 := by field_simp
            rw [this]; norm_num
    have hcg := certifiedGroupPoint_of_physical hM hc hB hphys hball
    rw [hbase, hhid] at hcg
    exact hcg

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
