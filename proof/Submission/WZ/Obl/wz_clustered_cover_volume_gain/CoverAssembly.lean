-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.CoverAssembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CrossScaleCount
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainData
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FineCoverEstimate
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.Glue
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.RescaleEstimate
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.SelectedInput

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set MeasureTheory
open scoped ENNReal

lemma cover_error_mono {δ h h' ρ : ℝ} {n N : ℕ} {x v : Fin n → V}
    {Y Z : Fin n → Set V} {S : Finset (Fin n)} {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : h ≤ h')
    (hC : C δ h n x v Y S Z ρ N y w f) : C δ h' n x v Y S Z ρ N y w f := by
  obtain ⟨hZ, hmass, hw, hcover, hF, hB, hbal, hX, hdeg⟩ := hC
  have herr : δ ^ (-h) ≤ δ ^ (-h') := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  refine ⟨hZ, ?_, hw, hcover, Parent.Interfaces.f_mono hF herr, Parent.Interfaces.b_mono hB herr,
    ?_, hX, fun i hi => (hdeg i hi).trans herr⟩
  · exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hh)) le_rfl).trans hmass
  · intro k k'
    exact (hbal k k').trans (mul_le_mul_of_nonneg_right herr (Nat.cast_nonneg _))

lemma selected_fine_card_power {δ h τ ν ξ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    (f : Fin n → Fin N) (U : Finset (Fin N))
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hconst : 384 ≤ δ ^ (-ν)) (hbudget : τ + h + ν ≤ ξ)
    (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y) (hZY : ∀ i, Z i ⊆ Y i)
    (hkeep : O (δ ^ τ) * ∑ i, volume (Y i) ≤ ∑ i ∈ S.filter (fun i => f i ∈ U), volume (Z i)) :
    (n : ℝ) ≤ δ ^ (-ξ) * (S.filter fun i => f i ∈ U).card := by
  have hcount := Parent.SelectedFamily.retained_fine_card (S.filter fun i => f i ∈ U)
    hδ hδ1 hA (fun i _ => hZY i) hkeep
  calc
    _ = δ ^ (-(τ + h)) * (δ ^ (τ + h) * n) := by
      rw [← mul_assoc, ← Real.rpow_add hδ]; simp
    _ ≤ δ ^ (-(τ + h)) * (384 * (S.filter fun i => f i ∈ U).card) :=
      mul_le_mul_of_nonneg_left hcount (Real.rpow_nonneg hδ.le _)
    _ ≤ δ ^ (-(τ + h)) * (δ ^ (-ν) * (S.filter fun i => f i ∈ U).card) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hconst (Nat.cast_nonneg _))
        (Real.rpow_nonneg hδ.le _)
    _ = δ ^ (-(τ + h + ν)) * (S.filter fun i => f i ∈ U).card := by
      rw [← mul_assoc, ← Real.rpow_add hδ]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)) (Nat.cast_nonneg _)

/-- A single dense selected fibre controls the common fine level, while
richness converts its parent count into the Section 9 fine-scale factor. -/
theorem fine_level_bound {σ ω : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 ≤ ω) (hE : E σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ Cf η₀ : ℝ, 0 < Cf ∧ 0 < η₀ ∧
    ∀ δ ρ b h a ζ J M : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ ρ → ρ ≤ 1 →
      0 < b → 0 < J → 0 ≤ h → 0 ≤ M →
    ∀ (n N : ℕ) (x v : Fin n → V) (Y Z : Fin n → Set V) (S : Finset (Fin n))
      (y w : Fin N → V) (f : Fin n → Fin N) (k : Fin N),
    A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y → C δ h n x v Y S Z ρ N y w f →
    O (δ ^ η₀ * q n {i | i ∈ S ∧ f i = k} * δ ^ 2) ≤
      ∑ i ∈ S.filter (fun i => f i = k), volume (Z i) →
    (∀ p, p ∈ assignedFiber f Z k → M ≤ fiberBodyCount f Z k p) →
    δ ^ (a - ζ) * (b / ρ) ^ 2 * J ≤ N →
    M ≤ Cf * δ ^ (σ * ζ - ε - h - σ * (a + h)) * (δ / ρ) ^ (-ω) *
      ((n : ℝ) / J * δ * ρ / b ^ 2) ^ σ := by
  intro ε hε
  have hR := Parent.Interfaces.local_rescaling_of_estimate hσ hσhalf hω hE
  obtain ⟨Cf, hCf, η₀, hη₀, H⟩ := Parent.Interfaces.fine_multiplicity_of_cover hσ hR ε hε
  refine ⟨Cf, η₀, hCf, hη₀, ?_⟩
  intro δ ρ b h a ζ J M hδ hδ100 hδρ hρ1 hb hJ hh hM n N x v Y Z S y w f k hA hC hdense hlevel hrich
  have hMbound := H δ ρ h h hδ hδ100 hδρ hρ1 hh le_rfl n N x v Y Z S y w f hA hC k hdense M hM
    (by
      intro p hp
      rw [show Parent.Interfaces.q {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} =
        fiberBodyCount f Z k p from supported_fine_count f (fun i => (hC.1 i).2.2) k p]
      obtain ⟨i, hi, hik, hip⟩ := hp
      exact hlevel p ⟨i, hik, hip⟩)
  have hout := Parent.fine_multiplicity_of_rich_coarse_cover hδ (hδ.trans_le hδρ)
    hb hJ (Nat.cast_nonneg n) (Nat.cast_nonneg (Set.ncard {i | i ∈ S ∧ f i = k}))
    hσ hCf.le (Parent.Interfaces.c_fiber_count_bound hδ hC k) hrich hMbound
  simpa only [show σ * ζ - (ε + h) - σ * (a + h) = σ * ζ - ε - h - σ * (a + h) by ring] using hout

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
