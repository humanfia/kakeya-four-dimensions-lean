import Submission.Obl.k4_physical_parent_potential_candidates.PhysicalBranch

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory MvPolynomial PhysicalPotentialData
open scoped ENNReal

noncomputable section

/-- The fixed physical intercept at the left edge of an original bin. -/
def physicalGroupCenter (a w : ℝ) (g : ℤ) : ℝ := (g:ℝ)*a*w

theorem physical_intercept_bin_window {I a w : ℝ} (ha : 0 < a) (hw : 0 < w)
    {g : ℤ} (hg : ⌊(I/a)/w⌋ = g) : |I-physicalGroupCenter a w g| ≤ a*w := by
  rw [div_div] at hg
  have hb := Int.floor_eq_iff.mp hg
  have hlo : (g:ℝ)*(a*w) ≤ I := (le_div_iff₀ (mul_pos ha hw)).mp hb.1
  have hhi : I < ((g:ℝ)+1)*(a*w) := (div_lt_iff₀ (mul_pos ha hw)).mp hb.2
  unfold physicalGroupCenter
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

namespace PhysicalSource

variable {q T j : ℕ} {ν : Measure Ln}
  {B a ζ d : ℝ} {c u : P2} {P0 : Po} {A : Set Ln} {F H : Set Ev}
  (source : PhysicalSource q ν B a ζ d T j c u P0 A F H)

def groupLines (w : ℝ) (g : ℤ) : Set Ln :=
  lineBin source.lineSet (fun l => ⌊(ownIntercept T j c u P0 source.Pot l/a)/w⌋) g

theorem measurable_groupLines (w : ℝ) (g : ℤ) : MeasurableSet (source.groupLines w g) :=
  measurableSet_lineBin source.measurable_lineSet
    (Int.measurable_floor.comp (((measurable_ownIntercept T j c u P0 source.Pot).div_const a).div_const w)) g

theorem groupLines_subset (hSA : ∀ e ∈ source.S, e.1 ∈ A) (w : ℝ) (g : ℤ) :
    source.groupLines w g ⊆ A :=
  inter_subset_left.trans (source.lineSet_subset hSA)

theorem group_events_lines {w : ℝ} {g : ℤ} {G : Set Ev}
    (hG : G ⊆ source.positiveEvents ∩ (source.interceptBin w) ⁻¹' {g}) :
    ∀ e ∈ G, e.1 ∈ source.groupLines w g := by
  intro e he
  exact ⟨(hG he).1.2, (hG he).2⟩

theorem group_lines_fit {w : ℝ} (hw : 0 < w) (hζw : ζ ≤ w) (g : ℤ)
    (l : Ln) (hl : l ∈ source.groupLines w g) :
    ∀ t ∈ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹) (((j:ℝ)+1)*((2:ℝ)^T)⁻¹),
      |eval (xp l t) P0 -
        (eval (fun i => packetBase T j c u (l,t) i) source.Pot +
          physicalGroupCenter a w g)| ≤ 2*a*w := by
  intro t ht
  have hf := source.line_fit l hl.1 t ht
  have hi := physical_intercept_bin_window source.a_pos hw hl.2
  calc
    _ = |(eval (xp l t) P0 - eval (fun i => packetBase T j c u (l,t) i) source.Pot -
          ownIntercept T j c u P0 source.Pot l) +
        (ownIntercept T j c u P0 source.Pot l-physicalGroupCenter a w g)| := by congr 1; ring
    _ ≤ |eval (xp l t) P0 - eval (fun i => packetBase T j c u (l,t) i) source.Pot -
          ownIntercept T j c u P0 source.Pot l| +
        |ownIntercept T j c u P0 source.Pot l-physicalGroupCenter a w g| := abs_add_le _ _
    _ ≤ a*ζ+a*w := add_le_add hf hi
    _ ≤ 2*a*w := by nlinarith [mul_le_mul_of_nonneg_left hζw source.a_pos.le]

theorem normalized_group_band
    (hSA : source.S ⊆ A ×ˢ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹)
      ((j:ℝ)*((2:ℝ)^T)⁻¹+((2:ℝ)^T)⁻¹))
    {w : ℝ} (hw : 0 < w) (hζw : ζ ≤ w) {g : ℤ} {e : Ev}
    (he : e ∈ source.S) (hbin : source.interceptBin w e = g) :
    |packetSignal P0 e/a -
      (eval (fun i => packetBase T j c u e i) source.Pot/a +
        physicalGroupCenter a w g/a)| ≤ 2*w := by
  have hf := source.fit_at_source_event hSA e he
  have hi := physical_intercept_bin_window source.a_pos hw hbin
  have hfit : |packetSignal P0 e -
      (eval (fun i => packetBase T j c u e i) source.Pot+physicalGroupCenter a w g)| ≤ a*(2*w) := by
    calc
      _ = |(packetSignal P0 e-eval (fun i => packetBase T j c u e i) source.Pot-
            ownIntercept T j c u P0 source.Pot e.1)+
          (ownIntercept T j c u P0 source.Pot e.1-physicalGroupCenter a w g)| := by congr 1; ring
      _ ≤ |packetSignal P0 e-eval (fun i => packetBase T j c u e i) source.Pot-
            ownIntercept T j c u P0 source.Pot e.1|+
          |ownIntercept T j c u P0 source.Pot e.1-physicalGroupCenter a w g| := abs_add_le _ _
      _ ≤ a*ζ+a*w := add_le_add hf hi
      _ ≤ a*(2*w) := by nlinarith [mul_le_mul_of_nonneg_left hζw source.a_pos.le]
  calc
    _ = |(packetSignal P0 e-
        (eval (fun i => packetBase T j c u e i) source.Pot+physicalGroupCenter a w g))/a| := by
      congr 1
      ring
    _ = |packetSignal P0 e-
        (eval (fun i => packetBase T j c u e i) source.Pot+physicalGroupCenter a w g)|/a := by
      rw [abs_div, abs_of_pos source.a_pos]
    _ ≤ 2*w := (div_le_iff₀ source.a_pos).2 (by nlinarith [hfit])

/-- A fixed intercept bin inherits the scalar-refined base cap. The same
w^d appears here and in its original-reference MK-heavy mass. -/
theorem group_scalar_base_cap
    (hSA : source.S ⊆ A ×ˢ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹)
      ((j:ℝ)*((2:ℝ)^T)⁻¹+((2:ℝ)^T)⁻¹))
    {w : ℝ} (hw : 0 < w) (hζw : ζ ≤ w) (hεw : source.ε ≤ 2*w) (hw1 : 2*w ≤ 1)
    {g : ℤ} {G : Set Ev} (hGm : MeasurableSet G)
    (hG : G ⊆ source.S ∩ (source.interceptBin w) ⁻¹' {g}) :
    ∀ U : Set P3, MeasurableSet U →
      ((ν.prod volume).restrict G) {e | packetBase T j c u e ∈ U} ≤
        ENNReal.ofReal (source.K*(2*w)^d)*
          (ENNReal.ofReal (((2:ℝ)^T)⁻¹)*ν A)*volume U := by
  intro U hU
  let f : P3 → ℝ := fun z => eval (fun i => z i) source.Pot/a+physicalGroupCenter a w g/a
  have hfm : Measurable f := by
    exact (((MvPolynomial.continuous_eval source.Pot).measurable.comp
      (show Measurable (fun z : P3 => fun i => z i) by fun_prop)).div_const a).add_const _
  apply le_trans ?_ (source.scalar_cap (2*w) hεw hw1 U hU f hfm)
  rw [Measure.restrict_apply' hGm, Measure.restrict_apply' source.measurable_S]
  apply measure_mono
  intro e he
  exact ⟨⟨he.1, source.normalized_group_band hSA hw hζw (hG he.2).1 (hG he.2).2⟩,
    (hG he.2).1⟩


/-- Every original-state union retains the same quantitative directional test.
The direction distribution is still the original product law restricted to G. -/
theorem retained_state_strip_ratio [IsFiniteMeasure ν]
    {G : Set Ev}
    (hratios : ∀ Q : Set Ev, MeasurableSet Q →
      (∀ k, ((ν.prod volume).restrict source.S) (source.fineState ⁻¹' {k} ∩ Q) ≤
        ENNReal.ofReal ((1:ℝ)/1000000000000) *
          ((ν.prod volume).restrict source.S) (source.fineState ⁻¹' {k})) →
      ∀ L : Set ((Fin 3 → ℤ) × ℤ),
        ((ν.prod volume).restrict G) (source.fineState ⁻¹' L ∩ Q) ≤
          ENNReal.ofReal ((1:ℝ)/1000000) *
            ((ν.prod volume).restrict G) (source.fineState ⁻¹' L)) :
    ∀ L : Set ((Fin 3 → ℤ) × ℤ), ∀ n : P2, ∀ t : ℝ, ‖n‖ = 1 →
      ((ν.prod volume).restrict G)
        {e | source.fineState e ∈ L ∧ |inner ℝ n (v e.1)-t| ≤ source.K^(-100:ℝ)} ≤
        ENNReal.ofReal ((1:ℝ)/1000000) *
          ((ν.prod volume).restrict G) {e | source.fineState e ∈ L} := by
  intro L n t hn
  let Q : Set Ev := {e | |inner ℝ n (v e.1)-t| ≤ source.K^(-100:ℝ)}
  have hQ : MeasurableSet Q := by
    have hv : Measurable (fun e : Ev => v e.1) := measurable_velocity.comp measurable_fst
    exact measurableSet_le (by fun_prop) measurable_const
  apply hratios Q hQ ?_ L
  intro k
  have hnum : ENNReal.ofReal ((1:ℝ)/1000000000000) = (1/1000000000000:ENNReal) := by
    norm_num [ENNReal.ofReal_div_of_pos]
  rw [hnum]
  convert source.breadth k n t hn using 1 <;> congr 1

/-- The actual one-branch physical group, with its original mass and its
scalar-refined base density, ready for direct or sampled restoration. -/
theorem exists_physical_heavy_group [IsFiniteMeasure ν]
    (hSA : source.S ⊆ A ×ˢ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹)
      ((j:ℝ)*((2:ℝ)^T)⁻¹+((2:ℝ)^T)⁻¹))
    {C w : ℝ} (hC : 0 < C)
    (hMK : Submission.Lib.K4ContinuousKakeya.FiniteMK 3 C)
    (hw : 0 < w) (hw1 : 2*w ≤ 1)
    (hresolve : countingResolution source.K (physicalPotentialLip q source.K)*ζ ≤ w) :
    ∃ (g : ℤ) (β : Bool) (G : Set Ev), MeasurableSet G ∧
      G ⊆ source.positiveEvents ∩ (source.interceptBin w) ⁻¹' {g} ∩
        parentBranch P0 ⁻¹' {β} ∧
      physicalHeavyFloor ((2:ℝ)^T)⁻¹ (ν.real A) C source.K w d ≤
        (ν.prod volume).real G ∧
      (∀ e ∈ G, e.1 ∈ source.groupLines w g) ∧
      (∀ L : Set ((Fin 3 → ℤ) × ℤ), ∀ n : P2, ∀ t : ℝ, ‖n‖ = 1 →
        ((ν.prod volume).restrict G)
          {e | source.fineState e ∈ L ∧ |inner ℝ n (v e.1)-t| ≤ source.K^(-100:ℝ)} ≤
          ENNReal.ofReal ((1:ℝ)/1000000) *
            ((ν.prod volume).restrict G) {e | source.fineState e ∈ L}) ∧
      (∀ U : Set P3, MeasurableSet U →
        ((ν.prod volume).restrict G) {e | packetBase T j c u e ∈ U} ≤
          ENNReal.ofReal (source.K*(2*w)^d)*
            (ENNReal.ofReal (((2:ℝ)^T)⁻¹)*ν A)*volume U) := by
  have hK : 0 ≤ source.K := by linarith [source.K_two]
  have hH : 0 ≤ physicalPotentialLip q source.K := physicalPotentialLip_nonneg q hK
  have hD : 1 ≤ countingResolution source.K (physicalPotentialLip q source.K) := by
    unfold countingResolution
    linarith [pow_nonneg hK 100]
  have hζ : 0 < ζ := source.ε_pos.trans_le source.ε_le
  have hζw : ζ ≤ w := (by nlinarith [mul_le_mul_of_nonneg_right hD hζ.le] :
    ζ ≤ countingResolution source.K (physicalPotentialLip q source.K)*ζ).trans hresolve
  obtain ⟨g, β, G, hGm, hGsub, hmass, hratios⟩ :=
    source.exists_physical_heavy_branch hSA hC hMK hw (by linarith) hresolve
  refine ⟨g, β, G, hGm, hGsub, hmass,
    source.group_events_lines (fun e he => (hGsub he).1),
    source.retained_state_strip_ratio hratios, ?_⟩
  exact source.group_scalar_base_cap hSA hw hζw (by linarith [source.ε_le]) hw1 hGm
    (fun e he => ⟨(hGsub he).1.1.1, (hGsub he).1.2⟩)

end PhysicalSource

end

end Submission.Obl.k4_physical_parent_potential_candidates
