-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.SplitProposal.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.Glue
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.RescaleEstimate
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.SplitTypes

/-!
# A corrected split of o019, with the glue proved

The split s015 (children o044 grains, o045 flat prisms, o046 local rescaling, o047 gain) was
rejected because the gain child asserted the Katz–Tao count `K ρ (δ^-ζ) N y w` for the whole
supplied `ρ`-cover. Here:

* the local rescaling `R` is no longer a child: `local_rescaling_of_estimate` proves it from `E`,
  so the gain child takes `E` (and `J`) instead of `R` (this also keeps its type under 4000 chars);
* the gain child `GainChild` outputs a *refinement* (`Refined`): a sub-family `S' ⊆ S`, sub-shadings
  `Z' ⊆ Z` keeping a `δ^ζ` share of the mass, and a new `ρ`-cover (same `ρ`) with exactly the data
  of o019's alternative (B) at error `ζ`, as the review asked;
* the grains child `GrainsChild` and the flat-prism child `FlatChild` are o044 and o045 unchanged.

`glue_of_children` proves o019's conclusion from `E` and the three children.
-/

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory

namespace Interfaces

/-- The data of o019's alternative (B) at error `ζ` and scale `ρ`, carried by a refinement
`S' ⊆ S`, `Z' ⊆ Z` of a given sub-family. -/
def Refined (ζ δ ρ : ℝ) (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V) (S : Finset (Fin n))
    (Z : Fin n → Set V) : Prop :=
  ∃ (S' : Finset (Fin n)) (Z' : Fin n → Set V) (N' : ℕ) (y' w' : Fin N' → V)
    (f' : Fin n → Fin N'),
    S' ⊆ S ∧ (∀ i, MeasurableSet (Z' i) ∧ Z' i ⊆ Z i) ∧
    o (δ ^ ζ) * ∑ i, μ (Y i) ≤ ∑ i ∈ S', μ (Z' i) ∧
    (∀ k, ‖w' k‖ = 1) ∧ (∀ i ∈ S', T δ (x i) (v i) ⊆ T ρ (y' (f' i)) (w' (f' i))) ∧
    K ρ (δ ^ (-ζ)) N' y' w' ∧ F ρ (δ ^ (-ζ)) N' y' w' ∧ B δ ρ (δ ^ (-ζ)) n N' x v S' y' w' f'

/-- The flat-prism child (o045, unchanged): Proposition 5.2 in the form used by §9. -/
def FlatChild (σ ω : ℝ) : Prop :=
  E σ ω → J σ ω

/-- The two-scale grains child (o044, unchanged): Proposition 7.5. -/
def GrainsChild (σ ω : ℝ) : Prop :=
  E σ ω → ∀ h : ℝ, 0 < h → ∃ α : ℝ, 0 < α ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧ η ≤ h ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ n x v Y, A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
      o (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ μ (⋃ i, Y i) ∨
      ∃ S Z ρ N y w f, G ω δ h n x v Y S Z ρ N y w f

/-- The corrected gain child (WZ §9, Steps 1–6 after Proposition 7.5): either a refinement of
the grains configuration is factored at scale `ρ` with error `δ^-ζ`, or the volume gains.
It takes `E` and the flat-prism estimate `J`; the local rescaling `R` it needs follows from `E`
(`local_rescaling_of_estimate`). -/
def GainChild (σ ω : ℝ) : Prop :=
  E σ ω → J σ ω → ∀ ζ : ℝ, 0 < ζ → ∃ h : ℝ, 0 < h ∧ h ≤ ζ ∧ ∃ α : ℝ, 0 < α ∧
    ∃ κ : ℝ, 0 < κ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ n x v Y,
      A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
      ∀ S Z ρ N y w f, G ω δ h n x v Y S Z ρ N y w f →
        Refined ζ δ ρ n x v Y S Z ∨
          o (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ μ (⋃ i, Y i)

/-- The conclusion of o019, in the notation of `Interfaces`. -/
def Conclusion (σ ω : ℝ) : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ∃ α : ℝ, 0 < α ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ n x v Y, A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
      o (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ μ (⋃ i, Y i) ∨
      ∃ (S : Finset (Fin n)) (Z : Fin n → Set V) (ρ : ℝ) (N : ℕ) (y w : Fin N → V)
        (f : Fin n → Fin N), (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
        o (δ ^ ζ) * ∑ i, μ (Y i) ≤ ∑ i ∈ S, μ (Z i) ∧
        δ ^ (1 - ω / 100) ≤ ρ ∧ ρ ≤ δ ^ (ω / 100) ∧ (∀ k, ‖w k‖ = 1) ∧
        (∀ i ∈ S, T δ (x i) (v i) ⊆ T ρ (y (f i)) (w (f i))) ∧
        K ρ (δ ^ (-ζ)) N y w ∧ F ρ (δ ^ (-ζ)) N y w ∧ B δ ρ (δ ^ (-ζ)) n N x v S y w f

/-- The glue of the corrected split: `E(σ,ω)` and the three children give o019. -/
theorem glue_of_children {σ ω : ℝ}
    (hE : E σ ω) (hflat : FlatChild σ ω) (hgrains : GrainsChild σ ω)
    (hgain : GainChild σ ω) : Conclusion σ ω := by
  intro ζ hζ
  have hJ : J σ ω := hflat hE
  obtain ⟨h, hh, -, α₂, hα₂, κ₂, hκ₂, hgain'⟩ := hgain hE hJ ζ hζ
  obtain ⟨α₁, hα₁, κ₁, hκ₁, η, hη, hηh, hgr⟩ := hgrains hE h hh
  refine ⟨min α₁ α₂, lt_min hα₁ hα₂, min κ₁ κ₂, lt_min hκ₁ hκ₂, η, hη, ?_⟩
  intro δ hδ hδ100 n x v Y hinput
  have hδ1 : δ ≤ 1 := by linarith
  rcases hgr δ hδ hδ100 n x v Y hinput with hvol | ⟨S, Z, ρ, N, y, w, f, hG⟩
  · exact Or.inl (gain_mono hδ hδ1 (min_le_left _ _) (min_le_left _ _) hκ₁.le hvol)
  have hinput' := a_mono_normalized hinput hδ hδ1 hηh
  rcases hgain' δ hδ hδ100 n x v Y hinput' S Z ρ N y w f hG with href | hvol
  · obtain ⟨S', Z', N', y', w', f', -, hZ', hmass, hw', hcover, hK, hF, hB⟩ := href
    obtain ⟨hC, hρlo, hρhi, -⟩ := hG
    exact Or.inr ⟨S', Z', ρ, N', y', w', f',
      fun i => ⟨(hZ' i).1, (hZ' i).2.trans (hC.1 i).2.1⟩, hmass, hρlo, hρhi, hw', hcover,
      hK, hF, hB⟩
  · exact Or.inl (gain_mono hδ hδ1 (min_le_right _ _) (min_le_right _ _) hκ₂.le hvol)

/-- The frozen flat-prism child gives `FlatChild` (its abbreviations instantiated by `rfl`). -/
theorem flatChild_of_frozen (h : SplitTypes.flatFrozen) {σ ω : ℝ} (hσ : 0 < σ) (hσu : σ ≤ 1 / 2)
    (hω : 0 < ω) (hωu : ω ≤ 1) : FlatChild σ ω :=
  h σ ω hσ hσu hω hωu _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl

/-- The frozen grains child gives `GrainsChild`. -/
theorem grainsChild_of_frozen (h : SplitTypes.grainsFrozen) {σ ω : ℝ} (hσ : 0 < σ)
    (hσu : σ ≤ 1 / 2) (hω : 0 < ω) (hωu : ω ≤ 1) : GrainsChild σ ω :=
  h σ ω hσ hσu hω hωu _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl

/-- The frozen gain child gives `GainChild`. -/
theorem gainChild_of_frozen (h : SplitTypes.gainFrozen) {σ ω : ℝ} (hσ : 0 < σ)
    (hσu : σ ≤ 1 / 2) (hω : 0 < ω) (hωu : ω ≤ 1) : GainChild σ ω :=
  h σ ω hσ hσu hω hωu _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl

/-- Variant gain child: the local rescaling `R` as its only premise. -/
def GainChild2 (σ ω : ℝ) : Prop :=
  R σ ω → ∀ ζ : ℝ, 0 < ζ → ∃ h : ℝ, 0 < h ∧ h ≤ ζ ∧ ∃ α : ℝ, 0 < α ∧
    ∃ κ : ℝ, 0 < κ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ n x v Y,
      A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
      ∀ S Z ρ N y w f, G ω δ h n x v Y S Z ρ N y w f →
        Refined ζ δ ρ n x v Y S Z ∨
          o (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ μ (⋃ i, Y i)

/-- The glue of the variant split (children: rescale, grains, gain with premise `R`). -/
theorem glue_of_children_v2 {σ ω : ℝ} (hE : E σ ω) (hR : E σ ω → R σ ω)
    (hgrains : GrainsChild σ ω) (hgain : GainChild2 σ ω) : Conclusion σ ω := by
  intro ζ hζ
  obtain ⟨h, hh, -, α₂, hα₂, κ₂, hκ₂, hgain'⟩ := hgain (hR hE) ζ hζ
  obtain ⟨α₁, hα₁, κ₁, hκ₁, η, hη, hηh, hgr⟩ := hgrains hE h hh
  refine ⟨min α₁ α₂, lt_min hα₁ hα₂, min κ₁ κ₂, lt_min hκ₁ hκ₂, η, hη, ?_⟩
  intro δ hδ hδ100 n x v Y hinput
  have hδ1 : δ ≤ 1 := by linarith
  rcases hgr δ hδ hδ100 n x v Y hinput with hvol | ⟨S, Z, ρ, N, y, w, f, hG⟩
  · exact Or.inl (gain_mono hδ hδ1 (min_le_left _ _) (min_le_left _ _) hκ₁.le hvol)
  have hinput' := a_mono_normalized hinput hδ hδ1 hηh
  rcases hgain' δ hδ hδ100 n x v Y hinput' S Z ρ N y w f hG with href | hvol
  · obtain ⟨S', Z', N', y', w', f', -, hZ', hmass, hw', hcover, hK, hF, hB⟩ := href
    obtain ⟨hC, hρlo, hρhi, -⟩ := hG
    exact Or.inr ⟨S', Z', ρ, N', y', w', f',
      fun i => ⟨(hZ' i).1, (hZ' i).2.trans (hC.1 i).2.1⟩, hmass, hρlo, hρhi, hw', hcover,
      hK, hF, hB⟩
  · exact Or.inl (gain_mono hδ hδ1 (min_le_right _ _) (min_le_right _ _) hκ₂.le hvol)

/-- The frozen variant gain child gives `GainChild2`. -/
theorem gainChild2_of_frozen (h : SplitTypes.gain2Frozen) {σ ω : ℝ} (hσ : 0 < σ)
    (hσu : σ ≤ 1 / 2) (hω : 0 < ω) (hωu : ω ≤ 1) : GainChild2 σ ω :=
  h σ ω hσ hσu hω hωu _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl

/-- The frozen rescale child gives `E σ ω → R σ ω`. -/
theorem rescale_of_frozen (h : SplitTypes.rescaleFrozen) {σ ω : ℝ} (hσ : 0 < σ)
    (hσu : σ ≤ 1 / 2) (hω : 0 < ω) (hωu : ω ≤ 1) : E σ ω → R σ ω :=
  h σ ω hσ hσu hω hωu _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl

end Interfaces

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
