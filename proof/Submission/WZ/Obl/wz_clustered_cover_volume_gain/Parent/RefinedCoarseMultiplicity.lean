-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.RefinedCoarseMultiplicity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.PartialCoarseEstimate
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.OccupiedMultiplicity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoarsePower

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open scoped Classical

noncomputable section

def packetUnion {n N L : ℕ} (S : Finset (Fin n)) (Z : Fin n → Set Space)
    (f : Fin n → Fin N) (U : Finset (Fin N)) (g : Fin N → Fin L) (j : Fin L) : Set Space :=
  ⋃ i ∈ S.filter (fun i => f i ∈ U ∧ g (f i) = j), Z i

namespace Interfaces

/-- The actual coarse-scale multiplicity estimate after density-preserving
subshading, including the complete normalization and coefficient power losses. -/
theorem refined_coarse_multiplicity {σ ω : ℝ} (hσ : 0 ≤ σ) (hE : E σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ Cc ηE : ℝ, 0 < Cc ∧ 0 < ηE ∧
    ∀ {δ η h ρ ν d t m a b H M0 : ℝ} {n N L : ℕ}
      {x v : Fin n → V} {Y Z Z' : Fin n → Set V} {S : Finset (Fin n)}
      {y w : Fin N → V} {f : Fin n → Fin N} {U : Finset (Fin N)}
      {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {g : Fin N → Fin L},
      0 < δ → δ ≤ 1 → δ ≤ ρ → 0 ≤ h → 0 ≤ η → 0 ≤ ν → 0 ≤ d → b ≤ 1 / 3 →
      U.Nonempty → A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y → C δ h n x v Y S Z ρ N y w f →
      Factor.AssignedCover 4 ρ (δ ^ (-ν)) y w U m a b L z e g →
      δ ^ t * b ≤ a → (∀ i, Z' i ⊆ Z i) →
      (∃ j, (packetShading b S Z' f U g j).Nonempty) →
      (n : ℝ) ≤ δ ^ (-d) * (S.filter fun i => f i ∈ U).card →
      (∀ k ∈ U, (∃ i ∈ S, f i = k ∧ (Z' i).Nonempty) →
        o (δ ^ H * q {i | i ∈ S ∧ f i = k} * δ ^ 2) ≤ ∑ i ∈ S with f i = k, μ (Z' i)) →
      900 * ((3 / 100 : ℝ) * b) ^ ηE ≤ δ ^ H → 0 ≤ M0 →
      (∀ p ∈ ⋃ j, packetUnion S Z' f U g j, o M0 ≤ multiplicity (packetUnion S Z' f U g) p) →
      M0 ≤ Cc * δ ^ (-(2 * (ν + t) + σ * (h + ν + d + η) + ε)) *
        (b ^ (-ω) * (L * b) ^ σ) := by
  classical
  intro ε hε
  obtain ⟨κ, ηE, hκ, hηE, hbound⟩ := partial_factored_coarse_estimate hE ε hε
  let C0 := κ * (3 / 100 : ℝ) ^ (ω + ε + 2 - σ) * (225 / 2 : ℝ) ^ (-2 : ℝ) *
    (1000000 : ℝ) ^ (-σ)
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  refine ⟨360 / C0, ηE, by positivity, hηE, ?_⟩
  intro δ η h ρ ν d t m a b H M0 n N L x v Y Z Z' S y w f U z e g
    hδ hδ1 hδρ hh hη hν hd hb3 hU hA hC hcover hround hsub hoccupied hcard hdense hdensity hM0 hmult
  let M := ((9 * b / (8 * a)) * δ ^ (-ν)) / (1 / 100 : ℝ)
  let l := (δ ^ (-h) * δ ^ (-ν) * δ ^ (-d) * δ ^ (-η)) / (1 / 100 : ℝ) ^ 3
  let P := Finset.univ.filter fun j => (packetShading b S Z' f U g j).Nonempty
  have ha : 0 < a := hδ.trans_le (hδρ.trans hcover.width)
  have hb : 0 < b := ha.trans_le hcover.ordered
  have hδb : δ ≤ b := hδρ.trans (hcover.width.trans hcover.ordered)
  have hK : 1 ≤ δ ^ (-ν) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hD : 1 ≤ δ ^ (-d) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hM : 1 ≤ M := by
    have hratio : 1 ≤ 9 * b / (8 * a) := (one_le_div (by positivity)).mpr (by linarith [hcover.ordered])
    have hmul := one_le_mul_of_one_le_of_one_le hratio hK
    dsimp [M]
    apply (one_le_div (by norm_num : (0 : ℝ) < 1 / 100)).mpr
    linarith
  have hl : 0 < l := by dsimp [l]; positivity
  have hba : b / a ≤ δ ^ (-t) := by
    apply (div_le_iff₀ ha).mpr
    have hh := mul_le_mul_of_nonneg_left hround (Real.rpow_nonneg hδ.le (-t))
    have he : δ ^ (-t) * δ ^ t = 1 := by rw [← Real.rpow_add hδ]; simp
    simpa only [← mul_assoc, he, one_mul] using hh
  have hMu : M ≤ (225 / 2 : ℝ) * δ ^ (-(ν + t)) := by
    calc
      M = (225 / 2 : ℝ) * (b / a) * δ ^ (-ν) := by dsimp [M]; ring
      _ ≤ (225 / 2 : ℝ) * δ ^ (-t) * δ ^ (-ν) := by gcongr
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hδ]; congr 2 <;> ring
  have hlv : l ≤ (1000000 : ℝ) * δ ^ (-(h + ν + d + η)) := by
    apply le_of_eq
    dsimp [l]
    rw [show -(h + ν + d + η) = -h + -ν + -d + -η by ring,
      Real.rpow_add hδ, Real.rpow_add hδ, Real.rpow_add hδ]
    ring
  have hL : 0 < L := by
    obtain ⟨j, _⟩ := hoccupied
    exact Nat.zero_lt_of_lt j.isLt
  have hvol := hbound hδ hδ1 hδρ hh hη hK hD hb3 hU hA hC hcover
    hsub hoccupied hcard hdense hdensity
  have hpower := coarse_estimate_power_selected (ω := ω) hδ hb
    (by norm_num : (0 : ℝ) < 3 / 100) hκ.le hM hl (Nat.cast_pos.mpr hL)
    (Nat.cast_nonneg P.card) (by norm_num : (0 : ℝ) < 225 / 2)
    (by norm_num : (0 : ℝ) < 1000000) hσ hε.le hδb hMu hlv
  let s := 2 * (ν + t) + σ * (h + ν + d + η) + ε
  have hcoef : 0 < C0 * δ ^ s * b ^ ω * (L * b) ^ (-σ) := by positivity
  have hout := occupied_coarse_level_bound hb hb3 hcoef hM0
    (packetUnion S Z' f U g) z e
    (factored_packetShading_subset hδ hδρ hA hC hcover hsub) hoccupied hmult
    ((ENNReal.ofReal_le_ofReal hpower).trans hvol)
  refine hout.trans_eq ?_
  change 360 / (C0 * δ ^ s * b ^ ω * (L * b) ^ (-σ)) = _
  rw [Real.rpow_neg hδ.le, Real.rpow_neg hb.le,
    Real.rpow_neg (by positivity : 0 ≤ (L : ℝ) * b)]
  dsimp only [s]
  field_simp

end Interfaces

end

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
