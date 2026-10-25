import Submission.Obl.k4_conditional_common_affine_field.AxisCaps
import Submission.Obl.k4_conditional_common_affine_field.GoodSet
import Submission.Obl.k4_conditional_common_affine_field.VelocityWitnesses

namespace Submission.Obl.k4_conditional_common_affine_field

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4ScalarCoreTools.Finalization

/-- An event-level two-axis preparation, in the original measure. Its menus consist
of original chart options, with the same coefficient bounds. -/
structure AxisPreparation {α : Type*} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) (b v : α → ℝ) (v₀ χb χv δ e ω K H r : ℝ)
    (f : α × ℝ → Fin 2 → ℝ) (L : ℤ × ℤ → Finset (Fin 3 → ℝ)) where
  w₁ : ℝ
  w₂ : ℝ
  separated : r ≤ |w₂-w₁|
  raw_axis_bounds : |w₁| ≤ H ∧ |w₂| ≤ H
  axis_bounds : |w₁-v₀| ≤ H ∧ |w₂-v₀| ≤ H
  region : Set (α × ℝ)
  measurable_region : MeasurableSet region
  region_good : region ⊆ goodSet b v χb χv K e f L
  mass : ENNReal.ofReal (1/(2*K^2))*μ univ ≤ μ region
  bounded : ∀ p ∈ region, |p.2| ≤ 1 ∧
    |axisIntercept b v w₁ p| ≤ 2*H ∧ |axisIntercept b v w₂ p| ≤ 2*H
  rowOpts : ℤ → Finset (Fin 3 → ℝ)
  colOpts : ℤ → Finset (Fin 3 → ℝ)
  row_card : ∀ j, ((rowOpts j).card : ℝ) ≤ 25*K
  col_card : ∀ j, ((colOpts j).card : ℝ) ≤ 25*K
  row_coeff : ∀ j, ∀ a ∈ rowOpts j, ∀ i, |a i| ≤ K
  col_coeff : ∀ j, ∀ a ∈ colOpts j, ∀ i, |a i| ≤ K
  row_fit : ∀ p ∈ region, ∃ a ∈ rowOpts ⌊axisIntercept b v w₁ p/ω⌋,
    |f p 0-a 0-a 1*p.2| ≤ 3*H*e ∧ |f p 1-a 2| ≤ 3*H*e
  col_fit : ∀ p ∈ region, ∃ a ∈ colOpts ⌊axisIntercept b v w₂ p/ω⌋,
    |f p 0-a 0-a 1*p.2| ≤ 3*H*e ∧ |f p 1-a 2| ≤ 3*H*e
  cell_ceiling : ∀ i j : ℤ,
    μ (region ∩ {p | ⌊axisIntercept b v w₁ p/ω⌋=j ∧ ⌊axisIntercept b v w₂ p/ω⌋=i}) ≤
      ENNReal.ofReal ((12*H^2+11)^2*K*ω^2)

/-- Conditional velocity domination at the actual fine state prepares two
separated directions and their fiber menus, without a loss for the coarse chart count. -/
theorem prepare_axes {α : Type*} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) [IsFiniteMeasure μ] (hμ : μ univ ≠ 0)
    (π : Measure ℝ) [IsProbabilityMeasure π] (b v : α → ℝ)
    (v₀ χb χv δ e ω K H r S : ℝ)
    (f : α × ℝ → Fin 2 → ℝ) (L : ℤ × ℤ → Finset (Fin 3 → ℝ))
    (hb : Measurable b) (hv : Measurable v) (hf : Measurable f)
    (hδ : 0 < δ) (he : 0 < e) (hχb : 0 < χb) (hχv : 0 < χv)
    (hK : 1 ≤ K) (hKH : K+1 ≤ H) (hδ1 : δ ≤ 1)
    (hδω : δ ≤ ω) (hδe : δ ≤ e) (hδr : δ ≤ r) (hr1 : 2*r ≤ 1)
    (hHr : 1/H ≤ r) (hχbω : (H+3)*ω ≤ χb) (hχvδ : δ ≤ χv)
    (hsmall : K^2*(2*r)^S ≤ 1/2)
    (hcoeff : ∀ l, |b l|+|v l|+|v₀| ≤ K)
    (hgood : ∀ᵐ p ∂μ, p ∈ goodSet b v χb χv K e f L)
    (hbase : ∀ q : Fin 2 → ℤ,
      μ {p | (fun j => ⌊base b v v₀ p j/δ⌋)=q} ≤ ENNReal.ofReal (K*δ^2))
    (hpalette : ∀ x s : ℝ, δ ≤ s → s ≤ 1 →
      π (Icc (x-s) (x+s)) ≤ ENNReal.ofReal (K*s^S))
    (hcond : ∀ q j, μ {p | fineState b v v₀ δ e f p=q ∧ ⌊v p.1/δ⌋=j} ≤
      ENNReal.ofReal K * μ {p | fineState b v v₀ δ e f p=q} *
        π (Ico ((j : ℝ)*δ) (((j : ℝ)+1)*δ)))
    (hcard : ∀ q, ((L q).card : ℝ) ≤ K)
    (hlist : ∀ q, ∀ a ∈ L q, ∀ i, |a i| ≤ K) :
    Nonempty (AxisPreparation μ b v v₀ χb χv δ e ω K H r f L) := by
  classical
  have hKpos : 0 < K := by linarith
  have hH : 1 ≤ H := by linarith
  have hKleH : K ≤ H := by linarith
  let A := goodSet b v χb χv K e f L
  have hA : MeasurableSet A := measurableSet_goodSet hb hv χb χv K e hf L
  obtain ⟨j,hj,W,hWm,hWA,hWmass,hWwitness⟩ := exists_two_velocity_bins
    μ hμ A hA hgood (fineState b v v₀ δ e f) (measurable_fineState hb hv v₀ δ e hf)
    (fun p => v p.1) (hv.comp measurable_fst) π δ r K S hδ hδr hr1 hKpos
    hsmall hpalette hcond
  have hWpos : μ W ≠ 0 := by
    have hpos : 0 < ENNReal.ofReal (1/(2*K^2))*μ univ :=
      pos_iff_ne_zero.mpr (mul_ne_zero
        (ENNReal.ofReal_pos.mpr (by positivity)).ne' hμ)
    exact (hpos.trans_le hWmass).ne'
  obtain ⟨p₀,hp₀⟩ := nonempty_of_measure_ne_zero hWpos
  obtain ⟨q₁,hq₁,q₂,hq₂,_,_,hq₁code,hq₂code⟩ := hWwitness p₀ hp₀
  have hclose (q : α × ℝ) (a : ℤ) (hqa : ⌊v q.1/δ⌋=a) :
      |v q.1-δ*(a : ℝ)| ≤ δ := by
    simpa only [hqa] using floor_scaled_error hδ (v q.1)
  have haxis (q : α × ℝ) (a : ℤ) (hqa : ⌊v q.1/δ⌋=a) :
      |δ*(a : ℝ)| ≤ H ∧ |δ*(a : ℝ)-v₀| ≤ H := by
    have hnear : |δ*(a : ℝ)-v q.1| ≤ δ := by
      simpa only [abs_sub_comm] using hclose q a hqa
    have hraw := (abs_sub_le (δ*(a : ℝ)) (v q.1) 0).trans
      (add_le_add hnear (le_refl |v q.1-0|))
    have hcenter := (abs_sub_le (δ*(a : ℝ)) (v q.1) v₀).trans
      (add_le_add hnear (abs_sub (v q.1) v₀))
    simp only [sub_zero] at hraw
    constructor <;> linarith [hcoeff q.1,abs_nonneg (b q.1),abs_nonneg (v q.1),abs_nonneg v₀]
  have haxis₁ := haxis q₁ j.1 hq₁code
  have haxis₂ := haxis q₂ j.2 hq₂code
  let w₁ := δ*(j.1 : ℝ)
  let w₂ := δ*(j.2 : ℝ)
  have hsep : r ≤ |w₂-w₁| := by simpa only [w₁,w₂,abs_sub_comm] using hj
  let R : ℤ → Finset (Fin 3 → ℝ) := fun k => chartMenu L χb χv (ω*(k : ℝ)) w₁
  let C : ℤ → Finset (Fin 3 → ℝ) := fun k => chartMenu L χb χv (ω*(k : ℝ)) w₂
  have hfitH (q : α × ℝ) (hq : q ∈ A) :
      ∃ a ∈ L (⌊b q.1/χb⌋,⌊v q.1/χv⌋),
        |f q 0-a 0-a 1*q.2| ≤ H*e ∧ |f q 1-a 2| ≤ H*e := by
    obtain ⟨a,ha,h₀,h₁⟩ := hq.2.2
    have hm : K*e ≤ H*e := mul_le_mul_of_nonneg_right hKleH he.le
    exact ⟨a,ha,h₀.trans hm,h₁.trans hm⟩
  have hrowfit (p : α × ℝ) (hp : p ∈ W) :
      ∃ a ∈ R ⌊axisIntercept b v w₁ p/ω⌋,
        |f p 0-a 0-a 1*p.2| ≤ 3*H*e ∧ |f p 1-a 2| ≤ 3*H*e := by
    obtain ⟨q,hq,q',hq',hs,hs',hc,hc'⟩ := hWwitness p hp
    exact axis_menu_has_predictor b v v₀ δ e χb χv ω H w₁ f L
      hδ he hχb hχv hH hδω hδe hχbω hχvδ haxis₁.2 hq.1 hs (hclose q j.1 hc)
      (fun q a ha i => (hlist q a ha i).trans hKleH) (hfitH q hq)
  have hcolfit (p : α × ℝ) (hp : p ∈ W) :
      ∃ a ∈ C ⌊axisIntercept b v w₂ p/ω⌋,
        |f p 0-a 0-a 1*p.2| ≤ 3*H*e ∧ |f p 1-a 2| ≤ 3*H*e := by
    obtain ⟨q',hq',q,hq,hs',hs,hc',hc⟩ := hWwitness p hp
    exact axis_menu_has_predictor b v v₀ δ e χb χv ω H w₂ f L
      hδ he hχb hχv hH hδω hδe hχbω hχvδ haxis₂.2 hq.1 hs (hclose q j.2 hc)
      (fun q a ha i => (hlist q a ha i).trans hKleH) (hfitH q hq)
  refine ⟨{
    w₁ := w₁, w₂ := w₂, separated := hsep
    raw_axis_bounds := ⟨haxis₁.1,haxis₂.1⟩
    axis_bounds := ⟨haxis₁.2,haxis₂.2⟩
    region := W, measurable_region := hWm, region_good := hWA, mass := hWmass
    bounded := ?_
    rowOpts := R, colOpts := C
    row_card := fun k => card_chartMenu L χb χv (ω*(k : ℝ)) w₁ K hcard
    col_card := fun k => card_chartMenu L χb χv (ω*(k : ℝ)) w₂ K hcard
    row_coeff := fun k => chartMenu_property L χb χv (ω*(k : ℝ)) w₁ _ hlist
    col_coeff := fun k => chartMenu_property L χb χv (ω*(k : ℝ)) w₂ _ hlist
    row_fit := hrowfit, col_fit := hcolfit
    cell_ceiling := axis_grid_cell_ceiling μ W b v v₀ w₁ w₂ δ ω H K
      hδ hδω hH hKpos.le haxis₁.2 (hHr.trans hsep) hbase }⟩
  intro p hp
  have ht := (hWA hp).1
  have hbv : |b p.1|+|v p.1| ≤ K := by linarith [hcoeff p.1,abs_nonneg v₀]
  have hb₁ := axisIntercept_bound b v w₁ K H (by linarith) haxis₁.1 ht hbv
  have hb₂ := axisIntercept_bound b v w₂ K H (by linarith) haxis₂.1 ht hbv
  exact ⟨by rw [abs_of_nonneg ht.1]; exact ht.2, by linarith, by linarith⟩

end Submission.Obl.k4_conditional_common_affine_field
