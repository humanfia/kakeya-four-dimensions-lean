import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.ResidualTarget

/- The deep-history menu construction follows this LOT tree o274/x0971,
commit 7eef0d70, Support/Sigma.lean, with three output coordinates and the supplied
corrected-residual variation in place of its four coordinate estimates. -/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

def residualOutputCoords (F : Frame) (C : Fin 4 → ℝ) (b : Fin 6 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  ![F.zt t, F.zZ b t, F.resid b t - transv C (F.zt t) (F.zZ b t) (F.tr b t)]

def residualOutputDecode (z : Fin 3 → ℤ) : (Fin 2 → ℤ) × ℤ := (![z 0, z 1], z 2)

theorem measurable_outBins {α : Type} [MeasurableSpace α] (F : Frame) (C : Fin 4 → ℝ)
    (σ τv : ℝ) {b : α → Fin 6 → ℝ} (hb : Measurable b) :
    Measurable fun p : α × ℝ => outBins F C σ τv (b p.1) p.2 := by
  have hbi : ∀ e, Measurable fun p : α × ℝ => b p.1 e :=
    fun e => (measurable_pi_apply e).comp (hb.comp measurable_fst)
  unfold outBins Frame.zt Frame.zZ Frame.resid Frame.tr transv
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro e
    fin_cases e <;> simp <;> fun_prop
  · fun_prop

/-- Renew velocity domination after passing to the final output states. Only 27
states occur on each original deep history, and its full original reference is charged. -/
theorem residual_output_prune {α : Type} [MeasurableSpace α] {cfg : Data α}
    {k : ℕ} {s se R v' : ℝ}
    (hν : IsProbabilityMeasure (cfg.ν k)) (hK1 : 1 ≤ cfg.K k)
    (hb : Measurable (cfg.b k))
    (hμ : cfg.μ k ≤ ENNReal.ofReal (cfg.K k) • (cfg.ν k).prod volume)
    (hB : BlocksAt cfg k s R) (hBe : BlocksAt cfg k se R)
    (hv'1 : R⁻¹ ≤ v') (hv'2 : v' ≤ R)
    (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) (θ : Measure (α × ℝ)) (C : Fin 4 → ℝ)
    (hθ : θ ≤ cfg.μ k)
    (hθsupp : ∀ᵐ p ∂θ, p.1 ∈ cfg.B k s i ∧ p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i))
    (hnest : ∀ j : Fin (cfg.n k se), ∃ h : Fin (cfg.n k s), cfg.A k se j ⊆ cfg.A k s h ∧
      Data.I (cfg.T k se) (cfg.j k se j) ⊆ Data.I (cfg.T k s) (cfg.j k s h))
    {σ τv : ℝ} (hσ : 0 < σ) (hτv : 0 < τv)
    (hvar : ∀ j : Fin (cfg.n k se),
      ∀ p ∈ (cfg.B k se j ×ˢ Data.I (cfg.T k se) (cfg.j k se j)) ∩
          (cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i)),
      ∀ p' ∈ (cfg.B k se j ×ˢ Data.I (cfg.T k se) (cfg.j k se j)) ∩
          (cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i)),
        |(blockFrame cfg k s i L).zt p.2 - (blockFrame cfg k s i L).zt p'.2| ≤ σ ∧
        |(blockFrame cfg k s i L).zZ (cfg.b k p.1) p.2 -
          (blockFrame cfg k s i L).zZ (cfg.b k p'.1) p'.2| ≤ σ ∧
        |((blockFrame cfg k s i L).resid (cfg.b k p.1) p.2 -
            transv C ((blockFrame cfg k s i L).zt p.2)
              ((blockFrame cfg k s i L).zZ (cfg.b k p.1) p.2)
              ((blockFrame cfg k s i L).tr (cfg.b k p.1) p.2)) -
          ((blockFrame cfg k s i L).resid (cfg.b k p'.1) p'.2 -
            transv C ((blockFrame cfg k s i L).zt p'.2)
              ((blockFrame cfg k s i L).zZ (cfg.b k p'.1) p'.2)
              ((blockFrame cfg k s i L).tr (cfg.b k p'.1) p'.2))| ≤ τv)
    (δp : ℝ≥0∞) (hδ0 : δp ≠ 0) (hδtop : δp ≠ ⊤) :
    ∃ θ' : Measure (α × ℝ), θ' ≤ θ ∧
      θ univ ≤ θ' univ + δp * (((27 : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal ((2 : ℝ) ^ cfg.T k s)⁻¹ * cfg.ν k (cfg.A k s i))) ∧
      ∀ (o : (Fin 2 → ℤ) × ℤ) (A : Set ℤ),
        θ' {p | outBins (blockFrame cfg k s i L) C σ τv (cfg.b k p.1) p.2 = o ∧
            vbin (cfg.N k ^ (-v')) (cfg.b k p.1 3) ∈ A} ≤
          (ENNReal.ofReal (cfg.K k) / δp) *
            θ' {p | outBins (blockFrame cfg k s i L) C σ τv (cfg.b k p.1) p.2 = o} *
              paletteBins (cfg.π k) (cfg.N k ^ (-v')) A := by
  classical
  let F := blockFrame cfg k s i L
  let par : Fin (cfg.n k se) → Fin (cfg.n k s) := fun j => Classical.choose (hnest j)
  have hpar : ∀ j, cfg.A k se j ⊆ cfg.A k s (par j) ∧
      Data.I (cfg.T k se) (cfg.j k se j) ⊆ Data.I (cfg.T k s) (cfg.j k s (par j)) :=
    fun j => Classical.choose_spec (hnest j)
  let r : Fin 3 → ℝ := ![σ, σ, τv]
  have hr : ∀ e, 0 < r e := by intro e; fin_cases e <;> simp [r, hσ, hτv]
  let G := cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i)
  have hex : ∀ j : Fin (cfg.n k se), ∃ M : Finset (Fin 3 → ℤ), M.card ≤ 27 ∧
      ∀ p ∈ (cfg.B k se j ×ˢ Data.I (cfg.T k se) (cfg.j k se j)) ∩ G,
        (fun e => ⌊residualOutputCoords F C (cfg.b k p.1) p.2 e / r e⌋) ∈ M := by
    intro j
    apply exists_floor_menu _ G (fun p => residualOutputCoords F C (cfg.b k p.1) p.2) r hr
    intro p hp p' hp' e
    have hv := hvar j p hp p' hp'
    fin_cases e
    · simpa [residualOutputCoords, r, F] using hv.1
    · simpa [residualOutputCoords, r, F] using hv.2.1
    · simpa [residualOutputCoords, r, F] using hv.2.2
  choose menu hcard hmenu using hex
  let menus : Fin (cfg.n k se) → Finset ((Fin 2 → ℤ) × ℤ) :=
    fun j => (menu j).image residualOutputDecode
  have hcards : ∀ j, (menus j).card ≤ 27 :=
    fun j => Finset.card_image_le.trans (hcard j)
  have hmenus : ∀ᵐ p ∂θ, ∀ j, p.1 ∈ cfg.B k se j →
      p.2 ∈ Data.I (cfg.T k se) (cfg.j k se j) →
        outBins F C σ τv (cfg.b k p.1) p.2 ∈ menus j := by
    filter_upwards [hθsupp] with p hp j hj1 hj2
    apply Finset.mem_image.mpr
    refine ⟨_, hmenu j p ⟨⟨hj1, hj2⟩, hp⟩, ?_⟩
    rfl
  exact deep_prune hν hK1 hμ hB hBe par hpar hv'1 hv'2 i θ hθ hθsupp
    (fun p => outBins F C σ τv (cfg.b k p.1) p.2) (measurable_outBins F C σ τv hb)
    27 menus hcards hmenus δp hδ0 hδtop

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
