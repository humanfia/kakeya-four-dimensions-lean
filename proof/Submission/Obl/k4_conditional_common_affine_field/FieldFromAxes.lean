import Submission.Obl.k4_conditional_common_affine_field.UniformGridField
import Submission.Obl.k4_conditional_common_affine_field.AxisPreparation
import Submission.Obl.k4_conditional_common_affine_field.AxisDeletion
import Submission.Obl.k4_conditional_common_affine_field.EraseMixed

namespace Submission.Obl.k4_conditional_common_affine_field

open Set MeasureTheory
open scoped ENNReal

noncomputable def gridError (P : ℕ) (B H e ω : ℝ) : ℝ := B^P*(3*H*e+ω)

noncomputable def mixedError (P : ℕ) (B K H e ω : ℝ) : ℝ :=
  8*(96*K*K/((B^P)⁻¹))^2*(gridError P B H e ω+K*e)

noncomputable def returnError (P : ℕ) (B K H e ω ρ : ℝ) : ℝ :=
  gridError P B H e ω+mixedError P B K H e ω*(2*H)^2/ρ^2

/-- The grid principle, the old pencil caps and original long-line Remez supply
the common affine/constant pair on the original law. -/
theorem common_field_from_axes {α : Type} [MeasurableSpace α]
    (P : ℕ) (hgrid : GridFieldAt P) (ν : Measure α) [IsProbabilityMeasure ν]
    (μ : Measure (α × ℝ)) [IsFiniteMeasure μ]
    (b v : α → ℝ) (v₀ χb χv δ e ω K H r B ρ D : ℝ)
    (f : α × ℝ → Fin 2 → ℝ) (L : ℤ × ℤ → Finset (Fin 3 → ℝ))
    (hb : Measurable b) (hv : Measurable v) (hf : Measurable f)
    (prep : AxisPreparation μ b v v₀ χb χv δ e ω K H r f L)
    (hK : 1 ≤ K) (hH : 1 ≤ H) (hB : 2 ≤ B) (he : 0 < e) (hω : 0 < ω)
    (hKH : K ≤ H) (hHB : H ≤ B) (h2HB : 2*H ≤ B) (hmenu : 25*K ≤ B)
    (hκ : (12*H^2+11)^2*K ≤ B) (hHr : 1/H ≤ r)
    (hmesh : ω ≤ (B^P)⁻¹) (hprepMass : ENNReal.ofReal B⁻¹ ≤ μ prep.region)
    (hdom : μ ≤ ENNReal.ofReal K • ν.prod volume)
    (hlist : ∀ q, ((L q).card : ℝ) ≤ K)
    (hρ : 0 < ρ) (hD : 0 ≤ D) (hsmall : 4*D ≤ (B^P)⁻¹)
    (hpencil : ∀ w : ℝ, μ {p | |v p.1-w| < ρ} ≤ ENNReal.ofReal D) :
    ∃ C : Fin 4 → ℝ, (∀ i, |C i| ≤ 4*(B^P)*H) ∧
      ENNReal.ofReal (B^P)⁻¹ ≤ μ {p |
        |f p 0-C 0-C 1*base b v v₀ p 0-C 2*base b v v₀ p 1| ≤ returnError P B K H e ω ρ ∧
          |f p 1-C 3| ≤ returnError P B K H e ω ρ} := by
  classical
  have hHpos : 0 < H := by linarith
  have hBpos : 0 < B := by linarith
  have hKpos : 0 < K := by linarith
  let u := prep.w₂-prep.w₁
  have hsep : B⁻¹ ≤ |u| := by
    have h := one_div_le_one_div_of_le hHpos hHB
    simpa only [one_div] using h.trans (hHr.trans prep.separated)
  have hubound : |u| ≤ B := by
    have h := (abs_sub prep.w₂ prep.w₁).trans
      (add_le_add prep.raw_axis_bounds.2 prep.raw_axis_bounds.1)
    exact h.trans (by linarith)
  obtain ⟨β,c,T,hTm,hTW,hTmass,hβ,hc,hfit⟩ := hgrid (α × ℝ) μ prep.region
    Prod.snd (axisIntercept b v prep.w₁) (axisIntercept b v prep.w₂) f prep.rowOpts prep.colOpts
    B ω (3*H*e) u hB hω (by positivity) hmesh prep.measurable_region measurable_snd
    (measurable_axisIntercept hb hv _) (measurable_axisIntercept hb hv _) hf hsep hubound
    (fun p _ => axisIntercept_sub b v _ _ p)
    (fun p hp => ⟨(prep.bounded p hp).1,((prep.bounded p hp).2.1).trans h2HB,
      ((prep.bounded p hp).2.2).trans h2HB,
      fun i => ((prep.region_good hp).2.1 i).trans (hKH.trans hHB)⟩)
    (fun j => (prep.row_card j).trans hmenu) (fun j => (prep.col_card j).trans hmenu)
    (fun j a ha i => (prep.row_coeff j a ha i).trans (hKH.trans hHB))
    (fun j a ha i => (prep.col_coeff j a ha i).trans (hKH.trans hHB))
    prep.row_fit prep.col_fit
    (fun i j => (prep.cell_ceiling i j).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hκ (sq_nonneg ω)))) hprepMass
  let E₀ := gridError P B H e ω
  let Q := mixedError P B K H e ω
  have hE₀ : 0 ≤ E₀ := by dsimp [E₀,gridError]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q,mixedError]; positivity
  have hTtime : T ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
    intro p hp
    exact ⟨mem_univ _,(prep.region_good (hTW hp)).1⟩
  have hTchart (p : α × ℝ) (hp : p ∈ T) :
      ∃ a ∈ L (⌊b p.1/χb⌋,⌊v p.1/χv⌋), |f p 0-a 0-a 1*p.2| ≤ K*e := by
    obtain ⟨a,ha,h₀,h₁⟩ := (prep.region_good (hTW hp)).2.2
    exact ⟨a,ha,h₀⟩
  have hmix : |β 3| * ρ^2 ≤ Q := lineMixedTerm_from_pencils ν μ
    (fun l => (⌊b l/χb⌋,⌊v l/χv⌋)) L b v hv (fun p => f p 0) T β
    K K ((B^P)⁻¹) ρ D E₀ (K*e) prep.w₁ prep.w₂ hKpos hK (by positivity) hρ hD hsmall
    hdom hTm hTtime hTmass hlist (fun p hp => (hfit p hp).1) hTchart
    (hpencil _) (hpencil _)
  let C := affineOfAxes β c v₀ prep.w₁ prep.w₂
  have hC : ∀ i, |C i| ≤ 4*(B^P)*H :=
    affineOfAxes_bound β c v₀ prep.w₁ prep.w₂ (B^P) H (by positivity) hH hβ hc
      prep.axis_bounds.1 prep.axis_bounds.2
  refine ⟨C,hC,hTmass.trans (measure_mono ?_)⟩
  intro p hp
  have hbound := prep.bounded p (hTW hp)
  have herr := erase_mixed_error (f p 0) (β 0) (β 1) (β 2) (β 3)
    (axisIntercept b v prep.w₁ p) (axisIntercept b v prep.w₂ p) (2*H) ρ Q E₀
    hρ (by positivity) hbound.2.1 hbound.2.2 hmix (hfit p hp).1
  have hid := affineOfAxes_identity β c v₀ prep.w₁ prep.w₂ p.2 (base b v v₀ p 1)
  rw [← axisIntercept_eq_base b v v₀ prep.w₁ p,
    ← axisIntercept_eq_base b v v₀ prep.w₂ p] at hid
  have hfirst : |f p 0-C 0-C 1*base b v v₀ p 0-C 2*base b v v₀ p 1| ≤
      returnError P B K H e ω ρ := by
    change |f p 0-C 0-C 1*p.2-C 2*base b v v₀ p 1| ≤ E₀+Q*(2*H)^2/ρ^2
    rw [← hid] at herr
    convert herr using 1
    congr 1
    dsimp only [C]
    ring
  have hsecond : |f p 1-C 3| ≤ returnError P B K H e ω ρ := by
    have h := (hfit p hp).2
    change |f p 1-c| ≤ E₀+Q*(2*H)^2/ρ^2
    exact h.trans (le_add_of_nonneg_right (by positivity))
  exact ⟨hfirst,hsecond⟩

end Submission.Obl.k4_conditional_common_affine_field
