-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.LinearityIteration.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.IteratedRefinement
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.InteriorParameters

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set Metric

/-- The tubes, slope, and plane field are fixed throughout the multiscale
refinement. Only the shadings change. -/
structure SlopeGeometry where
  n : ℕ
  x : Fin n → Space
  v : Fin n → Space
  f : ℝ → ℝ
  P : Space → Space

def RegularGrainFamily (σ η δ : ℝ) (G : SlopeGeometry)
    (Y : Fin G.n → Set Space) : Prop :=
  δ ≤ (1 / 100 : ℝ) ∧ ExtremalFamily σ η δ G.n G.x G.v Y ∧
    Grains σ δ (δ ^ (-η)) G.v Y G.f G.P ∧ LipschitzWith 1 G.f ∧
    ∀ z ∈ Icc (-1 : ℝ) 1, |G.f z| ≤ 3

/-- A function is affine on each interval of a given real grid. -/
def AffineOnGrid (h : ℝ) (L : ℝ → ℝ) : Prop :=
  ∀ j : ℤ, ∃ b s : ℝ, ∀ z ∈ Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
    L z = b + s * z

/-- The conclusion of a single local-linearity selection, at the family level. -/
def AffineSlopeFit (ρ : ℝ) (f : ℝ → ℝ) {n : ℕ}
    (Y : Fin n → Set Space) : Prop :=
  ∃ L : ℝ → ℝ, AffineOnGrid (Real.sqrt ρ) L ∧
    ∀ p ∈ ⋃ i, Y i, |f (p 2) - L (p 2)| ≤ ρ

theorem AffineSlopeFit.mono {ρ : ℝ} {f : ℝ → ℝ} {n : ℕ}
    {Y Z : Fin n → Set Space} (h : AffineSlopeFit ρ f Y) (hZY : ∀ i, Z i ⊆ Y i) :
    AffineSlopeFit ρ f Z := by
  obtain ⟨L, hgrid, hfit⟩ := h
  exact ⟨L, hgrid, fun p hp => hfit p ((iUnion_mono hZY) hp)⟩

theorem RegularGrainFamily.mono_error {σ η ε δ : ℝ} {G : SlopeGeometry}
    {Y : Fin G.n → Set Space} (hδ : 0 < δ) (hηε : η ≤ ε)
    (h : RegularGrainFamily σ η δ G Y) : RegularGrainFamily σ ε δ G Y := by
  have hδ1 : δ ≤ 1 := by linarith [h.1]
  refine ⟨h.1, h.2.1.mono_error hδ hδ1 hηε, ?_, h.2.2.2⟩
  exact h.2.2.1.mono_constant hδ
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hηε))

/-- The single-scale geometric input is stated with an independent interior-scale
margin. Its error and cutoff are uniform in the scale, tubes, and plane field. -/
def SingleScaleLinearity (σ : ℝ) : Prop :=
  ∀ ε θ : ℝ, 0 < ε → 0 < θ → ∃ η d₀ : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ ρ : ℝ, δ ^ (1 - θ) ≤ ρ → ρ ≤ δ ^ θ →
      ∀ (G : SlopeGeometry) (Y : Fin G.n → Set Space),
        RegularGrainFamily σ η δ G Y →
        ∃ Z : Fin G.n → Set Space, (∀ i, Z i ⊆ Y i) ∧
          RegularGrainFamily σ ε δ G Z ∧ AffineSlopeFit ρ G.f Z

/-- Single-scale local linearity gives simultaneous affine fits on any fixed finite
list of interior scales. The common input error is chosen before the tube scale
and before the family. -/
theorem finite_scale_linearity {σ θ d₁ : ℝ} (hθ : 0 < θ) (hd₁ : 0 < d₁)
    (h : SingleScaleLinearity σ) {ι : Type*} (J : Finset ι)
    (scale : ι → ℝ → ℝ)
    (hscale : ∀ i δ, 0 < δ → δ ≤ d₁ → δ ≤ 1 →
      δ ^ (1 - θ) ≤ scale i δ ∧ scale i δ ≤ δ ^ θ) :
    ∀ ε : ℝ, 0 < ε → ∃ η d₀ : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
        ∀ (G : SlopeGeometry) (Y : Fin G.n → Set Space),
          RegularGrainFamily σ η δ G Y →
          ∃ Z : Fin G.n → Set Space, (∀ i, Z i ⊆ Y i) ∧
            RegularGrainFamily σ ε δ G Z ∧ ∀ j ∈ J, AffineSlopeFit (scale j δ) G.f Z := by
  apply simultaneous_uniform_refinement
    (A := fun G : SlopeGeometry => Fin G.n → Set Space)
    (fun _ Z Y => ∀ i, Z i ⊆ Y i)
    (fun _ _ _ => subset_rfl)
    (fun _ _ _ _ h₁ h₂ i => (h₁ i).trans (h₂ i))
    (fun η δ G Y => RegularGrainFamily σ η δ G Y)
    (fun j δ G Y => AffineSlopeFit (scale j δ) G.f Y)
    (fun _ _ _ _ _ hZY hfit => hfit.mono hZY)
  intro j ε hε
  obtain ⟨η, d₀, hη, hηε, hd₀, hstep⟩ := h ε θ hε hθ
  refine ⟨η, min d₀ d₁, hη, hηε, lt_min hd₀ hd₁, ?_⟩
  intro δ hδ hδd G Y hY
  have hδ1 : δ ≤ 1 := by linarith [hY.1]
  have hδd₀ := hδd.trans (min_le_left _ _)
  have hδd₁ := hδd.trans (min_le_right _ _)
  exact hstep δ hδ hδd₀ (scale j δ) (hscale j δ hδ hδd₁ hδ1).1
    (hscale j δ hδ hδd₁ hδ1).2 G Y hY

/-- All affine fits needed by a geometric smoothing hierarchy can be obtained
simultaneously using strictly interior scales. -/
theorem interior_linearity_hierarchy {σ κ C : ℝ}
    (h : SingleScaleLinearity σ) (hκ : 0 < κ) (hκ1 : κ < 1) (hC : 0 < C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ θ η d₀ : ℝ),
      0 < N ∧ 0 < ζ ∧ 0 < θ ∧ (N : ℝ) * θ ≤ κ ∧
      0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
        ∀ (G : SlopeGeometry) (Y : Fin G.n → Set Space),
          RegularGrainFamily σ η δ G Y →
          C * N * (δ ^ (1 - κ)) ^ (-(1 / (N : ℝ) + 2 * ζ)) ≤ δ ^ (-κ) ∧
          ∃ Z : Fin G.n → Set Space, (∀ i, Z i ⊆ Y i) ∧
            RegularGrainFamily σ ε δ G Z ∧
            ∀ k : Fin N, AffineSlopeFit
              ((δ ^ (1 - κ)) ^ (((k : ℝ) + 1) / N)) G.f Z := by
  obtain ⟨N, ζ, θ, d₁, hN, hζ, hθ, _, hNθ, hd₁, hparams⟩ :=
    exists_interior_scale_parameters hκ hκ1 hC
  let scale : Fin N → ℝ → ℝ := fun k δ =>
    (δ ^ (1 - κ)) ^ (((k : ℝ) + 1) / N)
  obtain ⟨η, d₂, hη, hηε, hd₂, hfits⟩ :=
    finite_scale_linearity hθ hd₁ h Finset.univ scale
      (fun k δ hδ hδd hδ1 => (hparams δ hδ hδd hδ1).1 k) ε hε
  refine ⟨N, ζ, θ, η, min d₁ d₂, hN, hζ, hθ, hNθ, hη, hηε,
    lt_min hd₁ hd₂, ?_⟩
  intro δ hδ hδd G Y hY
  have hδ1 : δ ≤ 1 := by linarith [hY.1]
  refine ⟨(hparams δ hδ (hδd.trans (min_le_left _ _)) hδ1).2, ?_⟩
  obtain ⟨Z, hZY, hZ, hfit⟩ := hfits δ hδ (hδd.trans (min_le_right _ _)) G Y hY
  exact ⟨Z, hZY, hZ, fun k => hfit k (Finset.mem_univ k)⟩

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
