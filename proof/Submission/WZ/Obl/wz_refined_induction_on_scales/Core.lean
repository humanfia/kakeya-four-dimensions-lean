-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_refined_induction_on_scales.Core.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_refined_induction_on_scales.RefineCount
import Submission.WZ.Obl.wz_refined_induction_on_scales.Cutoff

/-!
# The glue of the split of o019

`glue_core` is WZ §9, Step 1, with the gain child's conclusion (the rescaling child's `R` is passed
to the grains child): after the grains child gives a
configuration `G` at error `δ^-h`, either some sub-collection `U` of the `ρ`-tubes whose fibres
carry a `δ^{ζ/2}` share of the shading mass obeys the Katz–Tao count `δ^-ζ` — and then
`refined_of_mass` gives o019's alternative (B) — or none does, and the gain child gives (A).
Large `δ` are handled by `remove_scale_cutoff`. `main_of_frozen_children` states the result for
the frozen children.
-/

namespace WangZahlLot.Obl.wz_refined_induction_on_scales

open MeasureTheory

namespace Interfaces

/-- The core of the glue (WZ §9, Step 1, and the scale cutoff): `E`, the grains child and the
conclusion of the gain child give o019. -/
theorem glue_core {σ ω : ℝ} (hσ : 0 < σ) (hE : E σ ω) (hR : R σ ω)
    (hgrains : GrainsChild σ ω) (hbody : GainBody σ ω) : Conclusion σ ω := by
  intro ζ hζ
  obtain ⟨h, hh, hhζ, α₂, hα₂, κ₂, hκ₂, hgain'⟩ := hbody ζ hζ
  obtain ⟨α₁, hα₁, κ₁, hκ₁, η, hη, hηh, hgr⟩ := hgrains hE hR h hh
  set α := min α₁ α₂ with hα
  have hαpos : 0 < α := lt_min hα₁ hα₂
  -- the scale below which Step 1's counting applies
  set e := ζ - ζ / 2 - 4 * h with he
  have hepos : 0 < e := by rw [he]; linarith
  set δ₀ := (1 / 384 : ℝ) ^ (1 / e) with hδ₀
  have hδ₀pos : 0 < δ₀ := by positivity
  have hsmall_of : ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → 384 * δ ^ e ≤ 1 := by
    intro δ hδ hδδ₀
    have h1 : δ ^ e ≤ δ₀ ^ e := Real.rpow_le_rpow hδ.le hδδ₀ hepos.le
    have h2 : δ₀ ^ e = 1 / 384 := by
      rw [hδ₀, ← Real.rpow_mul (by norm_num), one_div_mul_cancel hepos.ne', Real.rpow_one]
    linarith
  -- the second alternative of o019, as a predicate
  let Bpred : ℝ → (n : ℕ) → (Fin n → V) → (Fin n → V) → (Fin n → Set V) → Prop :=
    fun δ n x v Y => ∃ (S : Finset (Fin n)) (Z : Fin n → Set V) (ρ : ℝ) (N : ℕ)
      (y w : Fin N → V) (f : Fin n → Fin N), (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      o (δ ^ ζ) * ∑ i, μ (Y i) ≤ ∑ i ∈ S, μ (Z i) ∧
      δ ^ (1 - ω / 100) ≤ ρ ∧ ρ ≤ δ ^ (ω / 100) ∧ (∀ k, ‖w k‖ = 1) ∧
      (∀ i ∈ S, T δ (x i) (v i) ⊆ T ρ (y (f i)) (w (f i))) ∧
      K ρ (δ ^ (-ζ)) N y w ∧ F ρ (δ ^ (-ζ)) N y w ∧ B δ ρ (δ ^ (-ζ)) n N x v S y w f
  have hsmall : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ δ₀ → ∀ n x v Y,
      Hypotheses δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
      ENNReal.ofReal (min κ₁ κ₂ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤
        volume (⋃ i, Y i) ∨ Bpred δ n x v Y := by
    intro δ hδ hδ100 hδδ₀ n x v Y hinput
    have hδ1 : δ ≤ 1 := by linarith
    have hinputA : A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y := hypotheses_iff.mp hinput
    rcases hgr δ hδ hδ100 n x v Y hinputA with hvol | ⟨S, Z, ρ, N, y, w, f, hG⟩
    · exact Or.inl (gain_mono hδ hδ1 (min_le_left _ _) (min_le_left _ _) hκ₁.le hvol)
    have hinput' := a_mono_normalized hinputA hδ hδ1 hηh
    by_cases hex : ∃ U : Finset (Fin N),
        o (δ ^ (ζ / 2)) * ∑ i ∈ S, μ (Z i) ≤ ∑ i ∈ S.filter (fun i => f i ∈ U), μ (Z i) ∧
        ∀ W, Convex ℝ W → o (q {k | k ∈ U ∧ T ρ (y k) (w k) ⊆ W} * ρ ^ 2) ≤
          o (δ ^ (-ζ)) * μ W
    · obtain ⟨U, hmassU, hKU⟩ := hex
      have hC := hG.1
      have href := refined_of_mass hδ hδ1 (by positivity) (by linarith) (hsmall_of δ hδ hδδ₀)
        hinput' hC U hmassU hKU
      obtain ⟨S', Z', N', y', w', f', -, hZ', hmass, hw', hcover, hK, hF, hB⟩ := href
      obtain ⟨hC', hρlo, hρhi, -⟩ := hG
      exact Or.inr ⟨S', Z', ρ, N', y', w', f',
        fun i => ⟨(hZ' i).1, (hZ' i).2.trans (hC'.1 i).2.1⟩, hmass, hρlo, hρhi, hw', hcover,
        hK, hF, hB⟩
    · push Not at hex
      have hvol := hgain' δ hδ hδ100 n x v Y hinput' S Z ρ N y w f hG
        (fun U hU hK => (hex U hU) |> fun ⟨W, hW, hlt⟩ => absurd (hK W hW) (not_le.mpr hlt))
      exact Or.inl (gain_mono hδ hδ1 (min_le_right _ _) (min_le_right _ _) hκ₂.le hvol)
  obtain ⟨κ, hκ, hall⟩ := remove_scale_cutoff hσ.le hη.le (lt_min hκ₁ hκ₂) hδ₀pos Bpred hsmall
  refine ⟨α, hαpos, κ, hκ, η, hη, ?_⟩
  intro δ hδ hδ100 n x v Y hinput
  exact hall δ hδ hδ100 n x v Y (hypotheses_iff.mpr hinput)

/-- The glue: `E(σ,ω)` and the four children give o019's conclusion. -/
theorem glue_of_children {σ ω : ℝ} (hσ : 0 < σ) (hE : E σ ω) (hrescale : E σ ω → R σ ω)
    (hflat : FlatChild σ ω) (hgrains : GrainsChild σ ω) (hgain : GainChild σ ω) :
    Conclusion σ ω :=
  glue_core hσ hE (hrescale hE) hgrains (hgain hE (hflat hE))

end Interfaces

open Interfaces

theorem main_of_frozen_children (hrescale : Frozen.rescaleFrozen) (hflat : Frozen.flatFrozen)
    (hgrains : Frozen.grainsFrozen) (hgain : Frozen.gainFrozen) :
    ∀ σ ω : ℝ, 0 < σ → σ ≤ (1 / 2 : ℝ) → 0 < ω → ω ≤ 1 → ∀ T, T = (fun (d : ℝ) (p q : LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening d (segment ℝ p (p + q))) → ∀ K, K = (fun (d m : ℝ) (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) => ∀ W, Convex ℝ W → ENNReal.ofReal (Set.ncard {i | T d (x i) (v i) ⊆ W} * d ^ 2) ≤ ENNReal.ofReal m * MeasureTheory.volume W) → ∀ F, F = (fun (d l : ℝ) (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) => ∀ (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r → ENNReal.ofReal (Set.ncard {i | T d (x i) (v i) ⊆ Metric.ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r}}) ≤ ENNReal.ofReal (l * n) * MeasureTheory.volume (Metric.ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r})) → ∀ A, A = (fun (d η m l : ℝ) (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) => 0 < n ∧ (∀ i, ‖v i‖ = 1 ∧ T d (x i) (v i) ⊆ Metric.ball 0 1 ∧ MeasurableSet (Y i) ∧ Y i ⊆ T d (x i) (v i)) ∧ (∀ i j, i ≠ j → MeasureTheory.volume (T d (x i) (v i) ∩ T d (x j) (v j)) ≤ 1 / 2 * MeasureTheory.volume (T d (x i) (v i))) ∧ ENNReal.ofReal (d ^ η * n * d ^ 2) ≤ ∑ i, MeasureTheory.volume (Y i) ∧ K d m n x v ∧ F d l n x v) → (∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → ∀ n x v Y, A δ η m l n x v Y → ENNReal.ofReal (a * δ ^ (ω + ε) * m⁻¹ * (n * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * l * (n * δ)) ^ (-σ)) ≤ MeasureTheory.volume (⋃ i, Y i)) → (∀ ζ : ℝ, 0 < ζ → ∃ α : ℝ, 0 < α ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ n x v Y, A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y → ENNReal.ofReal (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ MeasureTheory.volume (⋃ i, Y i) ∨ ∃ (S : Finset (Fin n)) (Z : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) (ρ : ℝ) (N : ℕ) (y w : Fin N → LeanEval.Analysis.WangZahlKakeya.Space) (f : Fin n → Fin N), (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧ ENNReal.ofReal (δ ^ ζ) * ∑ i, MeasureTheory.volume (Y i) ≤ ∑ i ∈ S, MeasureTheory.volume (Z i) ∧ δ ^ (1 - ω / 100) ≤ ρ ∧ ρ ≤ δ ^ (ω / 100) ∧ (∀ k, ‖w k‖ = 1) ∧ (∀ i ∈ S, T δ (x i) (v i) ⊆ T ρ (y (f i)) (w (f i))) ∧ K ρ (δ ^ (-ζ)) N y w ∧ F ρ (δ ^ (-ζ)) N y w ∧ ∀ k (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r → ENNReal.ofReal (Set.ncard {i | i ∈ S ∧ f i = k ∧ T δ (x i) (v i) ⊆ T (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k) ∩ {p | |inner ℝ u p - t| ≤ r}}) * MeasureTheory.volume (T (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k)) ≤ ENNReal.ofReal (δ ^ (-ζ) * Set.ncard {i | i ∈ S ∧ f i = k}) * MeasureTheory.volume (T (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k) ∩ {p | |inner ℝ u p - t| ≤ r})) := by
  intro σ ω hσ hσu hω hωu T₀ hT K₀ hK F₀ hF A₀ hA
  subst T₀
  subst K₀
  subst F₀
  subst A₀
  intro hE
  exact glue_of_children hσ hE (rescale_of_frozen hrescale hσ hσu hω hωu)
    (flatChild_of_frozen hflat hσ hσu hω hωu)
    (grainsChild_of_frozen hgrains hσ hσu hω hωu) (gainChild_of_frozen hgain hσ hσu hω hωu)

end WangZahlLot.Obl.wz_refined_induction_on_scales
