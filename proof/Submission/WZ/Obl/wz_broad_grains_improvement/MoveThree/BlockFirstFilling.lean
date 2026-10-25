-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.BlockFirstFilling.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/BlockFirstFilling.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BlockPacketMass
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FirstPacketFilling
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FirstFillingParameters

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent (uniformMap)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit)

noncomputable section

def firstFillingMassConstant : ℝ := 393216 * (2 * 6 ^ 3 * 22 ^ 3)

/-- First fillings of the actual angular pieces of a normalized block.
The old indices and angular labels remain explicit. -/
structure BlockFirstFilling {ω ζ δ ε b ρ c β τ : ℝ} {p n : ℕ} {x v : Fin n → V}
    {Y : Fin n → Set V} {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
    {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
    (A : BlockAngularData D R G β τ) (lam den k : ℝ) (hk : 0 < k) where
  center : Fin A.labels.card → V
  frame : Fin A.labels.card → V ≃ₗᵢ[ℝ] V
  affine : Fin A.labels.card → V ≃ᵃ[ℝ] V
  coordinates : ∀ l q j, (affine l).linear q j =
    (![A.packetShort⁻¹, A.packetMiddle⁻¹, (1 / 4 : ℝ)] : Fin 3 → ℝ) j * frame l q j
  jacobian : ∀ l Q, μ (affine l '' Q) =
    O (1 / (4 * A.packetShort * A.packetMiddle)) * μ Q
  enclosure : ∀ l i, i ∈ A.active l → D.normalizedBody R G.affine i ⊆
    P A.packetShort A.packetMiddle 4 (center l) (frame l)
  good : Finset (Fin A.labels.card)
  indices : Fin A.labels.card → Finset (Fin R.card)
  direction : Fin A.labels.card → Fin R.card → Fin 3 → V
  supported : ∀ l, indices l ⊆ A.active l ∧ (l ∉ good → indices l = ∅)
  count : (lam * δ ^ (τ + 21 * ε / 40) / 16) * R.card ≤
    ∑ l ∈ good, ((indices l).card : ℝ)
  retained : (1 / 2 : ENNReal) * (∑ l, ∑ i, μ (A.normalizedPiece l i)) ≤
    ∑ l ∈ good, ∑ i, μ (A.normalizedPiece l i)
  filling : let F := fun l => (affine l).trans (uniformMap hk).toAffineEquiv
    let B := 256 * k * (2 * ρ) / A.packetShort
    ∀ l ∈ good, (indices l).Nonempty ∧
      (lam / 8) * (A.active l).card ≤ ((indices l).card : ℝ) ∧ B ≤ 1 / 1000000 ∧
      ∀ i ∈ indices l, O (48 * lam * (2 * ρ) ^ 2) ≤ μ (A.normalizedPiece l i) ∧
        Orthonormal ℝ (direction l i) ∧
        ‖F l (A.start i + (1 / 2 : ℝ) • A.axis i)‖ < 1 / 100 ∧
        F l '' T (2 * ρ) (A.start i) (A.axis i) ⊆
          WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism B B
            (F l (A.start i + (1 / 2 : ℝ) • A.axis i)) (direction l i) ∧
        O ((den * k / 16000) * B ^ 2) ≤ μ
          (WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism B B
            (F l (A.start i + (1 / 2 : ℝ) • A.axis i)) (direction l i) ∩
              F l '' (⋃ j, A.normalizedPiece l j))

namespace BlockAngularData

variable {ω ζ δ ε b ρ c β τ : ℝ} {p n : ℕ} {x v : Fin n → V}
  {Y : Fin n → Set V} {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
  {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}

/-- All geometric and analytic hypotheses of first filling now follow from
the actual packet data, apart from the displayed scalar budgets. -/
theorem first_filling_of_budgets (A : BlockAngularData D R G β τ)
    (hδ : 0 < δ) (hR : R.Nonempty) (hshort : G.short ≤ 1 / 8) (hβ : 0 ≤ β)
    {θ lam den k : ℝ} (hlam : 0 < lam) (hden : 0 < den) (hk : 0 < k)
    (hksmall : k ≤ 1 / 1000000000)
    (hr1 : 2 * ρ ≤ 1 / 100) (hθ1 : θ ≤ 1)
    (hslab : 2 * ρ + 5 * (A.packetShort / 2) ≤ 1 / 100)
    (hflat : 100 * (2 * ρ + 5 * (A.packetShort / 2)) ≤ 3 * A.packetMiddle)
    (hθ : 32 * (2 * ρ + 5 * (A.packetShort / 2)) ≤ θ) (hθb : θ ≤ 3 * A.packetMiddle)
    (hsmall : (2 * (240 : ℝ) ^ β) * (θ / (3 * A.packetMiddle)) ^ β ≤ lam / 8)
    (hnum : den * (10 ^ 13 * ((3 * A.packetMiddle) / θ) * (1 + Real.log (1 / (2 * ρ)))) ≤
      (lam / 16000) ^ 2 * (48 * lam))
    (hmass : 1536 * lam * (2 * ρ) ^ 2 * (2 * 6 ^ 3 * 22 ^ 3) ≤
      δ ^ (τ + 21 * ε / 40) * (ρ ^ 2 / 64)) :
    Nonempty (BlockFirstFilling A lam den k hk) := by
  classical
  have hρ : 0 < ρ := (D.dimensions hδ).2.1
  obtain ⟨ha, hra, hab, hb, _⟩ := A.packet_dimensions hδ hR
  obtain ⟨z, e, f, hbox, hlinear, hvol, hball⟩ := A.packet_normalizations hδ hR hshort
  obtain ⟨good, Q, u, _, hsupp, hcount, hretain, hfill⟩ := first_packet_fillings
    (Finset.univ : Finset (Fin A.labels.card)) A.active
    (by positivity : 0 < 2 * ρ) hr1 hra hab hb hθ1 hslab hflat hθ hθb
    hlam (by positivity : 0 < 2 * (240 : ℝ) ^ β) hden
    (by positivity : 0 < ρ ^ 2 / 64) hk hksmall hsmall hnum
    A.start A.axis A.normalizedPiece z e f
    (fun i => (A.lengths i).1) (fun i => (A.lengths i).2)
    (fun l _ i hi => ⟨hbox l i hi (A.endpoints i).1, hbox l i hi (A.endpoints i).2⟩)
    (fun l _ => A.normalizedPiece_measurable l)
    (fun l _ i => (A.normalizedPiece_subset l i).trans ((G.contained i).trans (A.tubes i)))
    (fun l _ => A.normalizedPiece_outside l)
    (fun l _ => A.normalizedPiece_mass_upper l)
    (A.normalizedPiece_mass_lower hδ) (A.normalizedPiece_count_sum hδ) hmass
    (fun l _ q u r _ hr _ => A.normalizedPiece_broad hδ hR hβ l q u r hr)
    (fun l _ => hlinear l) (fun l _ => hvol l) (fun l _ => hball l)
  exact ⟨{
    center := z, frame := e, affine := f, coordinates := hlinear, jacobian := hvol,
    enclosure := hbox,
    good := good, indices := Q, direction := u, supported := hsupp,
    count := hcount, retained := hretain, filling := hfill }⟩

end BlockAngularData

/-- One cutoff supplies first fillings for all normalized blocks. The exponent
choices are made before the original scale and the block are known. -/
theorem block_first_filling_uniform {ζ β s t e η k : ℝ}
    (hζ : 0 < ζ) (hβ : 0 < β) (hs : 0 < s) (hsg : s < ζ / 8)
    (ht : t < s * β) (hte : s + 3 * t < e) (heη : e < η)
    (hk : 0 < k) (hksmall : k ≤ 1 / 1000000000) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
      ∀ (ω ε b ρ c τ : ℝ) (p n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V)
        (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
        (R : Finset (Fin D.L)), R.Nonempty → ∀ G : D.NormalizedBlock R,
        ∀ A : BlockAngularData D R G β τ, τ + 21 * ε / 40 ≤ t →
          Nonempty (BlockFirstFilling A (δ ^ t / firstFillingMassConstant) (δ ^ e) k hk) ∧
          6144 * δ ^ η ≤ δ ^ e * k / 16000 := by
  have hH : 0 < firstFillingMassConstant := by norm_num [firstFillingMassConstant]
  obtain ⟨d₁, hd₁, hd₁small, H⟩ := first_filling_parameter_cutoff hs hsg hβ.le ht hte heη
    (by positivity : 0 < 2 * (240 : ℝ) ^ β) hH (by norm_num : (0 : ℝ) < 25) hk
  obtain ⟨d₂, hd₂, Hshort⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    (by positivity : 0 < ζ / 8) (by norm_num : (0 : ℝ) < 1 / 8)
  refine ⟨min d₁ d₂, lt_min hd₁ hd₂, (min_le_left _ _).trans hd₁small, ?_⟩
  intro δ hδ hδd ω ε b ρ c τ p n x v Y D R hR G A hmass
  have hδd₁ := hδd.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := hδd₁.trans (hd₁small.trans (by norm_num))
  obtain ⟨_, hρ, _, hc, hc1⟩ := D.dimensions hδ
  have hδr : δ ≤ 2 * ρ := by
    have hh := D.grains.1.trans (D.grains.2.1.trans
      (mul_le_of_le_one_right hρ.le hc1))
    linarith only [hh, hρ]
  obtain ⟨_, hra, hab, hb, _, _, hflat⟩ := A.packet_dimensions hδ hR
  obtain ⟨hr1, hslab, hfl, hθ, hθ1, hθb, hsmall, hnum, hnet⟩ :=
    H δ hδ hδd₁ (2 * ρ) A.packetShort A.packetMiddle hδr hra hab hb hflat
  have hshort : G.short ≤ 1 / 8 := by
    have hh := A.wider
    rw [Real.rpow_neg hδ.le, inv_mul_eq_div] at hh
    have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hδ _)).mp hh
    have hsmall := Hshort δ hδ (hδd.trans (min_le_right _ _))
    have hu := mul_le_of_le_one_left (Real.rpow_nonneg hδ.le (ζ / 8)) A.upper
    exact hh.trans (hu.trans hsmall)
  refine ⟨A.first_filling_of_budgets hδ hR hshort hβ.le (by positivity) (by positivity)
    hk hksmall hr1 hθ1 hslab hfl hθ hθb hsmall hnum ?_, hnet⟩
  have hexp := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hmass
  calc
    1536 * (δ ^ t / firstFillingMassConstant) * (2 * ρ) ^ 2 * (2 * 6 ^ 3 * 22 ^ 3) =
        δ ^ t * (ρ ^ 2 / 64) := by norm_num [firstFillingMassConstant]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hexp (by positivity)

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
