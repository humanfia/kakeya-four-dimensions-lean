-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.SplitV3.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.RefineCount
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.Cutoff

/-!
# Split variant v3: WZ §9 Step 1 in the glue

Compared with the corrected split (`SplitProposal`), the refinement branch of WZ §9 Step 1 is
proved in the glue (`refined_of_mass`): after the grains child produces a configuration `G` at
error `δ^-h`, either some sub-collection `U` of the `ρ`-tubes whose fibres carry a `δ^{ζ/2}` share
of the mass obeys the Katz–Tao count `δ^-ζ` — and then o019's alternative (B) holds — or none does.
The gain child `GainChild3` only treats the second case and has a single conclusion, the volume
gain. Its proof is WZ §9 Steps 1–6 with Proposition 4.6 applied to a mass class of the `ρ`-tubes
(proved here as `Factor.factor_frozen`, a child with a ready proof), Proposition 5.2 (`J`) and `E`.
-/

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory

namespace Interfaces

/-- The conclusion of the gain child of split v3 (after its premises `E` and `J`). -/
def GainBody (σ ω : ℝ) : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ∃ h : ℝ, 0 < h ∧ h ≤ ζ / 10 ∧ ∃ α : ℝ, 0 < α ∧
    ∃ κ : ℝ, 0 < κ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ n x v Y,
      A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
      ∀ S Z ρ N y w f, G ω δ h n x v Y S Z ρ N y w f →
        (∀ U : Finset (Fin N),
          o (δ ^ (ζ / 2)) * ∑ i ∈ S, μ (Z i) ≤ ∑ i ∈ S.filter (fun i => f i ∈ U), μ (Z i) →
          ¬ ∀ W, Convex ℝ W →
            o (q {k | k ∈ U ∧ T ρ (y k) (w k) ⊆ W} * ρ ^ 2) ≤ o (δ ^ (-ζ)) * μ W) →
        o (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ μ (⋃ i, Y i)

/-- The gain child of split v3. -/
def GainChild3 (σ ω : ℝ) : Prop :=
  E σ ω → J σ ω → GainBody σ ω

/-- The core of the glue of split v3: `E`, the grains child and the conclusion of the gain child
give o019. -/
theorem glue_core_v3 {σ ω : ℝ} (hσ : 0 < σ) (hE : E σ ω)
    (hgrains : GrainsChild σ ω) (hbody : GainBody σ ω) : Conclusion σ ω := by
  intro ζ hζ
  obtain ⟨h, hh, hhζ, α₂, hα₂, κ₂, hκ₂, hgain'⟩ := hbody ζ hζ
  obtain ⟨α₁, hα₁, κ₁, hκ₁, η, hη, hηh, hgr⟩ := hgrains hE h hh
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

/-- The glue of split v3. -/
theorem glue_of_children_v3 {σ ω : ℝ} (hσ : 0 < σ) (hE : E σ ω) (hflat : FlatChild σ ω)
    (hgrains : GrainsChild σ ω) (hgain : GainChild3 σ ω) : Conclusion σ ω :=
  glue_core_v3 hσ hE hgrains (hgain hE (hflat hE))

end Interfaces

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
