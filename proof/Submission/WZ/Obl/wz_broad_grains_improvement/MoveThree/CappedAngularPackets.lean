-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.CappedAngularPackets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/CappedAngularPackets.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.AngularPrismEstimate
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.AngularAspect
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BlockTubes
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BlockDensityUpper
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BlockParameters

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_flat_factored_improvement (BodyEstimate)
open WangZahlLot.Obl.wz_broad_grains_initialization
  (PacketRefinement measurable_angular_packets_power)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis boxAxis_norm inner_boxAxis)
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate exists_rpow_cutoff)

noncomputable section

/-- Angular packets made from the actual short axes of normalized grains. -/
structure BlockAngularData {ω ζ δ ε b ρ c : ℝ} {p n : ℕ} {x v : Fin n → V}
    {Y : Fin n → Set V} (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (R : Finset (Fin D.L)) (G : D.NormalizedBlock R) (β τ : ℝ) where
  start : Fin R.card → V
  axis : Fin R.card → V
  scale : ℝ
  shade : Fin R.card → Set V
  packets : V → Finset (Finset (Fin R.card))
  center : V → Finset (Fin R.card) → Fin R.card
  lengths : ∀ i, (1 / 4 : ℝ) ≤ ‖axis i‖ ∧ ‖axis i‖ ≤ 1
  tubes : ∀ i, D.normalizedBody R G.affine i ⊆ T (2 * ρ) (start i) (axis i)
  endpoints : ∀ i, start i ∈ D.normalizedBody R G.affine i ∧
    start i + axis i ∈ D.normalizedBody R G.affine i
  lower : 2 * ρ ≤ scale
  upper : scale ≤ 1
  refinement : PacketRefinement β (2 * ρ) scale (fun i => unit (axis i))
    (D.normalizedShade R G.affine) shade packets center
  mass : O (δ ^ τ) * ∑ i, μ (D.normalizedShade R G.affine i) ≤ ∑ i, μ (shade i)
  wider : δ ^ (-(ζ / 8)) * G.short ≤ scale

/-- In a density-capped saturated block, angular selection takes place at
a scale larger than the old short side by a fixed zeta power. -/
theorem capped_block_angular_packets_with_relative_budget {σ ω ζ t : ℝ}
    (hσ : 0 < σ) (hω : 0 < ω) (hζ : 0 < ζ) (hbody : BodyEstimate σ ω) (ht : 0 < t) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ β ≤ t ∧ ∀ s : ℝ, 0 < s →
      ∃ τ η : ℝ, 0 < τ ∧ τ ≤ s * β ∧ τ ≤ s ∧ 0 < η ∧ η ≤ min 1 (ζ / 16) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ η → ∀ p : ℕ,
      ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
        ∀ (b ρ c : ℝ) (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
        A δ (ε / 4) (δ ^ (-(ε / 4))) (δ ^ (-(ε / 4))) n x v Y →
        (∀ q ∈ ⋃ i, Y i, ∀ r : ℝ, 0 < r → r ≤ 1 →
          μ ((⋃ i, Y i) ∩ ball q r) ≤ O (δ ^ (-(ζ * σ / 16)) * (δ / r) ^ (ω + σ) * r ^ 3)) →
        ∀ (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
          (R : Finset (Fin D.L)), R.Nonempty → ∀ G : D.NormalizedBlock R,
          G.short ≤ 1 / 8 → Nonempty (BlockAngularData D R G β τ) := by
  let e := ζ * σ / 256
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨A₀, η₀, d₁, hA₀, hη₀, hd₁, hd₁small, H⟩ := angular_prism_body_estimate hbody e he
  let β := min t (min 1 (ζ * σ / 128))
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβ1 : β ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨β, hβ, hβ1, min_le_left _ _, ?_⟩
  intro s hs
  let τ := min (s * β) (min (η₀ / 4) (ζ * σ / 128))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨dsel, hdsel, _, Hsel⟩ := measurable_angular_packets_power hβ hβ1 hτ
  refine ⟨τ, min τ (min 1 (ζ / 16)), hτ, min_le_left _ _,
    (min_le_left _ _).trans (mul_le_of_le_one_right hs.le hβ1),
    by positivity, min_le_right _ _, ?_⟩
  intro ε hε hεη p
  have hετ : ε ≤ τ := hεη.trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := hεη.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεζ : ε ≤ ζ / 16 := hεη.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨d₂, hd₂, hd₂one, HP⟩ := grainPackingCoefficient_power_bound hε
  let C := (A₀ / 2) / (110592 * (2 : ℝ) ^ p) * (16 : ℝ) ^ (-σ) * (819200 : ℝ) ^ (-ω)
  let K := 512 * (4 : ℝ) ^ (σ + ω) * (36 : ℝ) ^ (σ + ω)
  have hC : 0 < C := by dsimp [C]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨d₃, hd₃, HC⟩ := exists_rpow_cutoff (by positivity : 0 < 3 * ζ * σ / 16)
    (by positivity : 0 < C / (4 * K))
  obtain ⟨d₄, hd₄, HS⟩ := exists_rpow_cutoff (by positivity : 0 < ω / 100)
    (by positivity : 0 < dsel / 2)
  obtain ⟨d₅, hd₅, HB⟩ := exists_rpow_cutoff hη₀
    (by norm_num : (0 : ℝ) < 1 / (2 * (2 * 6 ^ 3 * 22 ^ 3)))
  obtain ⟨d₆, hd₆, HA⟩ := exists_rpow_cutoff (by positivity : 0 < ζ / 8)
    (by norm_num : (0 : ℝ) < 36 / 80)
  refine ⟨min d₁ (min d₂ (min d₃ (min d₄ (min d₅ (min d₆ (1 / 4000000)))))),
    by positivity, (min_le_left _ _).trans hd₁small, ?_⟩
  intro δ hδ hδd b ρ c n x v Y hA hcap D R hR G hshort8
  have hδd₁ := hδd.trans (min_le_left _ _)
  have hdrest := hδd.trans (min_le_right _ _)
  have hδd₂ := hdrest.trans (min_le_left _ _)
  have hdrest := hdrest.trans (min_le_right _ _)
  have hδd₃ := hdrest.trans (min_le_left _ _)
  have hdrest := hdrest.trans (min_le_right _ _)
  have hδd₄ := hdrest.trans (min_le_left _ _)
  have hdrest := hdrest.trans (min_le_right _ _)
  have hδd₅ := hdrest.trans (min_le_left _ _)
  have hdrest := hdrest.trans (min_le_right _ _)
  have hδd₆ := hdrest.trans (min_le_left _ _)
  have hδtiny : δ ≤ 1 / 4000000 := hdrest.trans (min_le_right _ _)
  have hδsmall : δ ≤ 1 / 4096 := by linarith
  have hδ1 : δ ≤ 1 := hδd₂.trans hd₂one
  have hδ2 : δ ^ (2 : ℕ) ≤ δ := by nlinarith
  obtain ⟨ha, hρ, hρ1, hc, hc1⟩ := D.dimensions hδ
  have hδρ : δ ≤ ρ := D.grains.1.trans (D.grains.2.1.trans
    (mul_le_of_le_one_right hρ.le hc1))
  have hrsel : 2 * ρ ≤ dsel := by
    have hh := D.scale_stop.trans (HS δ hδ hδd₄)
    linarith
  obtain ⟨s, v', hlen, hshorttube, hends, hv', htubes, hnormal⟩ := G.tube_data hδ
  obtain ⟨θ, Z, packets, center, hρθ, hθ1, href, hmass⟩ :=
    Hsel (2 * ρ) (by positivity) hrsel R.card (fun i => unit (v' i))
      (D.normalizedShade R G.affine) (Finset.card_pos.mpr hR) hv' G.measurable
  have hθ : 0 < θ := (by positivity : 0 < 2 * ρ).trans_le hρθ
  have hδθ : δ ≤ θ := hδρ.trans ((by linarith : ρ ≤ 2 * ρ).trans hρθ)
  have hmassδ : O (δ ^ τ) * ∑ i, μ (D.normalizedShade R G.affine i) ≤ ∑ i, μ (Z i) := by
    apply le_trans _ hmass
    apply mul_le_mul' _ le_rfl
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hδ.le (by linarith) hτ.le)
  let l := τ + 21 * ε / 40
  have hlη : l ≤ η₀ := by
    have hh : τ ≤ η₀ / 4 := (min_le_right _ _).trans (min_le_left _ _)
    dsimp [l]; linarith
  have hsmallpower : 2 * e + l + β ≤ ζ * σ / 16 := by
    have hτmax : τ ≤ ζ * σ / 128 := (min_le_right _ _).trans (min_le_right _ _)
    have hβmax : β ≤ ζ * σ / 128 := (min_le_right _ _).trans (min_le_right _ _)
    dsimp [e, l]; nlinarith
  have hdense : O (δ ^ (21 * ε / 40) * R.card * (ρ ^ 2 / 64)) ≤
      ∑ i, μ (D.normalizedShade R G.affine i) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => G.dense i)
    simp only [G.body_volume, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hh
    convert hh using 1
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1; ring
  have hmass' : O (δ ^ l * R.card * (ρ ^ 2 / 64)) ≤ ∑ i, μ (Z i) := by
    apply le_trans _ hmassδ
    apply le_trans _ (mul_le_mul' le_rfl hdense)
    apply le_of_eq
    rw [← ENNReal.ofReal_mul (by positivity), show l = τ + 21 * ε / 40 from rfl,
      Real.rpow_add hδ]
    congr 1; ring
  have hbudget : 2 * (δ ^ (2 : ℕ)) ^ η₀ * (2 * 6 ^ 3 * 22 ^ 3) ≤ δ ^ l := by
    have hpow : (δ ^ (2 : ℕ)) ^ η₀ = δ ^ η₀ * δ ^ η₀ := by
      rw [← Real.rpow_natCast δ 2, ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
      congr 1; norm_num; ring
    rw [hpow]
    have hb := (le_div_iff₀ (by norm_num : (0 : ℝ) < 2 * (2 * 6 ^ 3 * 22 ^ 3))).mp
      (HB δ hδ hδd₅)
    have hp := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hδ.le η₀)
    have hexp := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hlη
    nlinarith only [hp, hexp]
  have hcount := D.block_cardinality_bound hδ hδsmall hε1 hA R
  have hM := (grainCoefficient_bounds ha.le (mul_pos hρ hc).le hc.le D.z D.e D.Q).1
  have hP := grainPackingCoefficient_ge_one δ ε
  have hbase : δ ^ (2 : ℕ) ≤ (ρ / 100) / 32768 := by
    have hh := mul_le_mul_of_nonneg_left hδtiny hδ.le
    nlinarith only [hh, hδρ, hδ.le]
  have hslab i : D.normalizedBody R G.affine i ⊆
      {q | |inner ℝ (boxAxis G.frame 0) q - inner ℝ (boxAxis G.frame 0) G.center| ≤ G.short / 2} := by
    intro q hq
    have hh := (G.enclosure i hq).1
    change |G.frame (q - G.center) 0| ≤ _ at hh
    simpa only [Set.mem_ofPred_eq, map_sub, PiLp.sub_apply, inner_boxAxis] using hh
  have hraw := H (δ ^ (2 : ℕ)) (sq_pos_of_pos hδ) (hδ2.trans hδd₁)
    R.card (D.normalizedBody R G.affine) (D.normalizedShade R G.affine) Z
    (fun i => G.affine (D.z (enumerate R i)))
    (fun i => s i + (1 / 2 : ℝ) • v' i - (1 / 2 : ℝ) • unit (v' i))
    (fun i => unit (v' i)) G.short (ρ / 100) (2 * ρ) (ρ ^ 2 / 64)
    (grainCoefficient D.a ρ c D.z D.e D.Q) (grainPackingCoefficient δ ε) β θ (δ ^ l)
    hcount G.short_pos hshort8 hθ hθ1 hρθ (by positivity) hbase (by positivity) hM hP
    (by positivity) G.geometry.compact G.geometry.convex G.round G.long G.body_volume
    G.unit_ball G.contained hv' htubes G.convex_count G.packing
    (boxAxis G.frame 0) (inner ℝ (boxAxis G.frame 0) G.center) (boxAxis_norm _ _) hslab hnormal
    packets center href hmass' hbudget
  let B := min (80 * θ) 4
  let A' := min (36 * G.short) B
  have hB : 0 < B := lt_min (by positivity) (by norm_num)
  have hA' : 0 < A' := lt_min (by have hh := G.short_pos; positivity) hB
  let X := (ρ / A') ^ (σ + ω) * (4 * G.short * G.middle)
  have hX : 0 < X := by
    have hh := G.short_pos
    have hh' := G.short_pos.trans_le G.ordered
    dsimp [X]; positivity
  have hlo : O (C * δ ^ (2 * e + l) *
      (grainCoefficient D.a ρ c D.z D.e D.Q) ^ (σ / 2) *
      (grainPackingCoefficient δ ε) ^ (-σ) * (A' / B) ^ (σ / 2) * X) ≤
        O (2 * θ ^ (-β)) * μ (⋃ i, D.normalizedShade R G.affine i) := by
    apply le_trans _ hraw
    apply ENNReal.ofReal_le_ofReal
    exact saturated_packet_density_factor (by positivity) (by positivity) hδ hρ hA' hB
      (zero_lt_one.trans_le hM) (zero_le_one.trans hP) G.saturated
  have hscale : A' / 36 ≤ G.short := by
    have hh : A' ≤ 36 * G.short := min_le_left _ _
    linarith
  have hup := D.normalized_block_density_upper_at hδ (show 0 ≤ σ + ω by positivity) hA
    (by simpa only [add_comm σ ω] using hcap) R G (by positivity : 0 < A' / 36) hscale
  have hratio : (ρ / (A' / 36)) ^ (σ + ω) =
      (36 : ℝ) ^ (σ + ω) * (ρ / A') ^ (σ + ω) := by
    rw [show ρ / (A' / 36) = 36 * (ρ / A') by ring,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 36) (by positivity)]
  have hup' : μ (⋃ i, D.normalizedShade R G.affine i) ≤ O (K * δ ^ (-(ζ * σ / 16)) * X) := by
    rw [hratio] at hup
    convert hup using 1 <;> dsimp [K, X] <;> ring
  have haspect := packet_aspect_of_density_bounds hδ hδ1 hσ hζ hεζ hsmallpower D.large.le
    (zero_lt_one.trans_le hP) (HP δ hδ hδd₂) hβ.le hδθ hC hK hX (HC δ hδ hδd₃) hlo hup'
  have hwide := angular_scale_of_prism_aspect hδ hδ1 hζ G.short_pos hθ
    (by have hh := HA δ hδ hδd₆; linarith) haspect
  exact ⟨⟨s, v', θ, Z, packets, center, hlen, hshorttube, hends, hρθ, hθ1, href, hmassδ, hwide⟩⟩

/-- Both the angular exponent and the retained-mass loss can be made
smaller than an arbitrary prescribed budget. -/
theorem capped_block_angular_packets_with_budget {σ ω ζ t : ℝ}
    (hσ : 0 < σ) (hω : 0 < ω) (hζ : 0 < ζ) (hbody : BodyEstimate σ ω) (ht : 0 < t) :
    ∃ β τ η : ℝ, 0 < β ∧ β ≤ 1 ∧ β ≤ t ∧ 0 < τ ∧ τ ≤ t ∧
      0 < η ∧ η ≤ min 1 (ζ / 16) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ η → ∀ p : ℕ,
      ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
        ∀ (b ρ c : ℝ) (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
        A δ (ε / 4) (δ ^ (-(ε / 4))) (δ ^ (-(ε / 4))) n x v Y →
        (∀ q ∈ ⋃ i, Y i, ∀ r : ℝ, 0 < r → r ≤ 1 →
          μ ((⋃ i, Y i) ∩ ball q r) ≤
            O (δ ^ (-(ζ * σ / 16)) * (δ / r) ^ (ω + σ) * r ^ 3)) →
        ∀ (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
          (R : Finset (Fin D.L)), R.Nonempty → ∀ G : D.NormalizedBlock R,
          G.short ≤ 1 / 8 → Nonempty (BlockAngularData D R G β τ) := by
  obtain ⟨β, hβ, hβ1, hβt, H⟩ :=
    capped_block_angular_packets_with_relative_budget hσ hω hζ hbody ht
  obtain ⟨τ, η, hτ, _, hτt, hη, hηmax, H⟩ := H t ht
  exact ⟨β, τ, η, hβ, hβ1, hβt, hτ, hτt, hη, hηmax, H⟩

/-- The unbudgeted form of the angular-packet construction. -/
theorem capped_block_angular_packets {σ ω ζ : ℝ}
    (hσ : 0 < σ) (hω : 0 < ω) (hζ : 0 < ζ) (hbody : BodyEstimate σ ω) :
    ∃ β τ η : ℝ, 0 < β ∧ β ≤ 1 ∧ 0 < τ ∧ 0 < η ∧ η ≤ min 1 (ζ / 16) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ η → ∀ p : ℕ,
      ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
        ∀ (b ρ c : ℝ) (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
        A δ (ε / 4) (δ ^ (-(ε / 4))) (δ ^ (-(ε / 4))) n x v Y →
        (∀ q ∈ ⋃ i, Y i, ∀ r : ℝ, 0 < r → r ≤ 1 →
          μ ((⋃ i, Y i) ∩ ball q r) ≤
            O (δ ^ (-(ζ * σ / 16)) * (δ / r) ^ (ω + σ) * r ^ 3)) →
        ∀ (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
          (R : Finset (Fin D.L)), R.Nonempty → ∀ G : D.NormalizedBlock R,
          G.short ≤ 1 / 8 → Nonempty (BlockAngularData D R G β τ) := by
  obtain ⟨β, τ, η, hβ, hβ1, _, hτ, _, hη, hηmax, H⟩ :=
    capped_block_angular_packets_with_budget hσ hω hζ hbody (show (0 : ℝ) < 1 by norm_num)
  exact ⟨β, τ, η, hβ, hβ1, hτ, hη, hηmax, H⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
