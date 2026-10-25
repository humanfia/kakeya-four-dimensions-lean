-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.CapComparison.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/CapComparison.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641 commit 8a2b46b, CapComparison.lean. -/
import Mathlib

/-!
# The aggregate cap comparison of the second net step

Scalar part of the concentration contradiction after the first filling (requested by x0670,
13:38Z): the low-`q` labels carry, by the summed net estimate (`summed_low_q_net_conc` on
branch x0617), at least `K * S` with

  `K = Cnet * δ^en * R^s * J * w0 / M * δ^(-zs)`, `S ≥ δ^t / H * δ^l * n / 16`,

while their physical shadings have pointwise overlap `Kov ≤ 2 δ^(-β)` and lie under a
density cap `cap ≤ Ccap * δ^(-uc) * R^s * Vblk`, with the old block saturation
`M * Vblk ≤ Csat * n * w0`. The geometry `J`, `R^s`, `w0`, `n / M` cancels, so the
comparison `J * Kov * cap < K * S / 2` (the hypothesis `hcomp` of
`high_q_labels_carry_half`) holds as soon as
`64 * Ccap * Csat * H < Cnet * δ^(en + t + l + β + uc - zs)`, which holds at all small `δ`
when the exponent gap `zs - (en + t + l + β + uc)` is positive.
-/

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

/-- The aggregate comparison: all geometric factors cancel through the old saturation. -/
theorem aggregate_cap_comparison
    {δ J Kov cap K S n w0 M Vblk R s Ccap Csat H Cnet β uc en t l zs : ℝ}
    (hδ : 0 < δ) (hJ : 0 < J) (hR : 0 < R) (hw0 : 0 < w0) (hM : 0 < M) (hn : 0 < n)
    (hCcap : 0 ≤ Ccap) (hH : 0 < H) (hCnet : 0 < Cnet)
    (hKov : Kov ≤ 2 * δ ^ (-β))
    (hcap0 : 0 ≤ cap) (hcap : cap ≤ Ccap * δ ^ (-uc) * R ^ s * Vblk)
    (hsat : M * Vblk ≤ Csat * n * w0)
    (hS : δ ^ t / H * δ ^ l * n / 16 ≤ S)
    (hK : K = Cnet * δ ^ en * R ^ s * J * w0 / M * δ ^ (-zs))
    (hsmall : 64 * Ccap * Csat * H < Cnet * δ ^ (en + t + l + β + uc - zs)) :
    J * Kov * cap < K * S / 2 := by
  -- the common positive factor
  set X : ℝ := J * R ^ s * w0 * n / M with hX
  have hRs : 0 < R ^ s := Real.rpow_pos_of_pos hR s
  have hXpos : 0 < X := by rw [hX]; positivity
  have hdβ : 0 < δ ^ (-β) := Real.rpow_pos_of_pos hδ _
  have hduc : 0 < δ ^ (-uc) := Real.rpow_pos_of_pos hδ _
  -- the block volume through the saturation
  have hVblk : Vblk ≤ Csat * n * w0 / M := by
    rw [le_div_iff₀ hM]; linarith [hsat]
  -- upper bound for the left side
  have hleft : J * Kov * cap ≤ 2 * Ccap * Csat * δ ^ (-β) * δ ^ (-uc) * X := by
    have h1 : J * Kov * cap ≤ J * (2 * δ ^ (-β)) * (Ccap * δ ^ (-uc) * R ^ s * Vblk) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hKov hJ.le) hcap hcap0
      exact mul_nonneg hJ.le (by positivity)
    have h2 : Ccap * δ ^ (-uc) * R ^ s * Vblk ≤
        Ccap * δ ^ (-uc) * R ^ s * (Csat * n * w0 / M) :=
      mul_le_mul_of_nonneg_left hVblk (by positivity)
    have h3 : J * (2 * δ ^ (-β)) * (Ccap * δ ^ (-uc) * R ^ s * (Csat * n * w0 / M)) =
        2 * Ccap * Csat * δ ^ (-β) * δ ^ (-uc) * X := by
      rw [hX]; field_simp
    calc J * Kov * cap ≤ _ := h1
      _ ≤ J * (2 * δ ^ (-β)) * (Ccap * δ ^ (-uc) * R ^ s * (Csat * n * w0 / M)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := h3
  -- lower bound for the right side
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hright : Cnet * (δ ^ en * δ ^ (-zs) * δ ^ t * δ ^ l) / (32 * H) * X ≤ K * S / 2 := by
    have h1 : K * (δ ^ t / H * δ ^ l * n / 16) ≤ K * S := mul_le_mul_of_nonneg_left hS hK0
    have h2 : Cnet * (δ ^ en * δ ^ (-zs) * δ ^ t * δ ^ l) / (32 * H) * X =
        K * (δ ^ t / H * δ ^ l * n / 16) / 2 := by
      rw [hK, hX]; field_simp; ring
    rw [h2]; linarith
  -- the exponent bookkeeping
  have hexp : δ ^ (en + t + l + β + uc - zs) =
      (δ ^ en * δ ^ (-zs) * δ ^ t * δ ^ l) * (δ ^ β * δ ^ uc) := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ,
      ← Real.rpow_add hδ]
    congr 1; ring
  have hinv : δ ^ (-β) * δ ^ (-uc) * (δ ^ β * δ ^ uc) = 1 := by
    calc δ ^ (-β) * δ ^ (-uc) * (δ ^ β * δ ^ uc) =
          (δ ^ (-β) * δ ^ β) * (δ ^ (-uc) * δ ^ uc) := by ring
      _ = δ ^ (-β + β) * δ ^ (-uc + uc) := by rw [Real.rpow_add hδ, Real.rpow_add hδ]
      _ = 1 := by rw [neg_add_cancel, neg_add_cancel, Real.rpow_zero, mul_one]
  have hP : 0 < δ ^ β * δ ^ uc := by positivity
  have hmid : 2 * Ccap * Csat * δ ^ (-β) * δ ^ (-uc) <
      Cnet * (δ ^ en * δ ^ (-zs) * δ ^ t * δ ^ l) / (32 * H) := by
    rw [lt_div_iff₀ (by positivity)]
    have hkey : 64 * Ccap * Csat * H <
        Cnet * (δ ^ en * δ ^ (-zs) * δ ^ t * δ ^ l) * (δ ^ β * δ ^ uc) := by
      rw [hexp] at hsmall; linarith
    have hscaled := mul_lt_mul_of_pos_right hkey
      (show 0 < δ ^ (-β) * δ ^ (-uc) by positivity)
    have hl : 64 * Ccap * Csat * H * (δ ^ (-β) * δ ^ (-uc)) =
        2 * Ccap * Csat * δ ^ (-β) * δ ^ (-uc) * (32 * H) := by ring
    have hr : Cnet * (δ ^ en * δ ^ (-zs) * δ ^ t * δ ^ l) * (δ ^ β * δ ^ uc) *
        (δ ^ (-β) * δ ^ (-uc)) = Cnet * (δ ^ en * δ ^ (-zs) * δ ^ t * δ ^ l) := by
      calc _ = Cnet * (δ ^ en * δ ^ (-zs) * δ ^ t * δ ^ l) *
            (δ ^ (-β) * δ ^ (-uc) * (δ ^ β * δ ^ uc)) := by ring
        _ = _ := by rw [hinv, mul_one]
    rw [hl, hr] at hscaled
    exact hscaled
  calc J * Kov * cap ≤ _ := hleft
    _ < Cnet * (δ ^ en * δ ^ (-zs) * δ ^ t * δ ^ l) / (32 * H) * X :=
        mul_lt_mul_of_pos_right hmid hXpos
    _ ≤ _ := hright

/-- The smallness hypothesis of `aggregate_cap_comparison` holds uniformly below a cutoff
once the exponent `en + t + l + β + uc - zs` is at most `-g` for a fixed gap `g > 0`. -/
theorem aggregate_cap_comparison_cutoff (Ccap Csat H Cnet g : ℝ) (hCcap : 0 ≤ Ccap)
    (hCsat : 0 ≤ Csat) (hH : 0 < H) (hCnet : 0 < Cnet) (hg : 0 < g) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ e : ℝ, e ≤ -g →
      64 * Ccap * Csat * H < Cnet * δ ^ e := by
  set B : ℝ := (64 * Ccap * Csat * H + 1) / Cnet with hB
  have hB0 : 0 < B := by rw [hB]; positivity
  refine ⟨min 1 (B ^ (-(1 / g))), lt_min one_pos (Real.rpow_pos_of_pos hB0 _),
    min_le_left _ _, ?_⟩
  intro δ hδ hδd e he
  have hδ1 : δ ≤ 1 := hδd.trans (min_le_left _ _)
  have hδB : δ ≤ B ^ (-(1 / g)) := hδd.trans (min_le_right _ _)
  -- δ^(-g) ≥ B
  have h1 : B ≤ δ ^ (-g) := by
    have hmono : (B ^ (-(1 / g))) ^ (-g) ≤ δ ^ (-g) :=
      Real.rpow_le_rpow_of_nonpos hδ hδB (by linarith)
    have hval : (B ^ (-(1 / g))) ^ (-g) = B := by
      rw [← Real.rpow_mul hB0.le]
      have : -(1 / g) * -g = 1 := by field_simp
      rw [this, Real.rpow_one]
    linarith [hmono, hval]
  -- δ^e ≥ δ^(-g)
  have h2 : δ ^ (-g) ≤ δ ^ e := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 he
  have h3 : B ≤ δ ^ e := h1.trans h2
  have h4 : Cnet * B = 64 * Ccap * Csat * H + 1 := by
    rw [hB]; field_simp
  have h5 : Cnet * B ≤ Cnet * δ ^ e := mul_le_mul_of_nonneg_left h3 hCnet.le
  linarith

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
