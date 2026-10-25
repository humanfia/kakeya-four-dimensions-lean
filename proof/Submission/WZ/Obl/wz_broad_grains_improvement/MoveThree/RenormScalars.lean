-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.RenormScalars.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/RenormScalars.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0708 commit 170d089, RenormScalars.lean. -/
import Mathlib

/-!
# Scalars for renormalising a capped physical enclosure

Requested by x0708 (14:49Z). A capped physical enclosure of short side `A` around old grains
of thickness `a` (with `δ ≤ a ≤ ρ c` and `a ≤ A < δ^(1 - vLoss)`) is renormalised at the radius
`r = max (2 ρ) (A / c)` by the diagonal map of Jacobian `J2 = r / (64 A c^2)`. This file
records the scalar consequences:

* `A / a ≤ δ^(-vLoss)` and `r ≤ 2 δ^(-vLoss) ρ`;
* an old row of physical mass `λ a ρ c^2` has renormalised mass
  `J2 * (λ a ρ c^2) ≥ (1/128) λ δ^(2 vLoss) r^2`;
* `r ≤ 1/100` and the packet growth `θ ≥ δ^(-t) r` (from `θ ≥ δ^(-t0) ρ`, `t + vLoss < t0`)
  below uniform cutoffs;
* a generic absorption `C δ^q ≤ δ^p` for `p < q` below a uniform cutoff.
-/

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

/-- The short-side ratio. -/
theorem renorm_ratio {δ a A vLoss : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a)
    (hA : A < δ ^ (1 - vLoss)) : A / a ≤ δ ^ (-vLoss) := by
  have ha : 0 < a := hδ.trans_le hδa
  rw [div_le_iff₀ ha]
  have h1 : δ ^ (1 - vLoss) = δ ^ (-vLoss) * δ := by
    rw [← Real.rpow_add_one hδ.ne']; congr 1; ring
  have h2 : δ ^ (-vLoss) * δ ≤ δ ^ (-vLoss) * a :=
    mul_le_mul_of_nonneg_left hδa (Real.rpow_nonneg hδ.le _)
  linarith

/-- The renormalisation radius is at most `2 δ^(-vLoss) ρ`. -/
theorem renorm_radius {δ a A ρ c vLoss : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hvLoss : 0 ≤ vLoss)
    (hδa : δ ≤ a) (haρc : a ≤ ρ * c) (haA : a ≤ A) (hA : A < δ ^ (1 - vLoss)) (hρ : 0 < ρ)
    (hc : 0 < c) :
    max (2 * ρ) (A / c) ≤ 2 * δ ^ (-vLoss) * ρ := by
  have ha : 0 < a := hδ.trans_le hδa
  have hpow1 : 1 ≤ δ ^ (-vLoss) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  apply max_le
  · nlinarith
  · -- A / c ≤ (A / a) ρ ≤ δ^(-vLoss) ρ
    have hratio := renorm_ratio hδ hδa hA
    have hA0 : 0 < A := ha.trans_le haA
    have h1 : A / c ≤ A / a * ρ := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hc ha]
      nlinarith [mul_le_mul_of_nonneg_left haρc hA0.le]
    have h2 : A / a * ρ ≤ δ ^ (-vLoss) * ρ := mul_le_mul_of_nonneg_right hratio hρ.le
    have h3 : δ ^ (-vLoss) * ρ ≤ 2 * δ ^ (-vLoss) * ρ := by
      have := Real.rpow_pos_of_pos hδ (-vLoss)
      nlinarith
    linarith

/-- The renormalised old-row mass. -/
theorem renorm_row_mass {δ a A ρ c lam vLoss : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hvLoss : 0 ≤ vLoss) (hδa : δ ≤ a) (haρc : a ≤ ρ * c) (haA : a ≤ A)
    (hA : A < δ ^ (1 - vLoss)) (hρ : 0 < ρ) (hc : 0 < c) (hlam : 0 ≤ lam) :
    (1 / 128 : ℝ) * lam * δ ^ (2 * vLoss) * (max (2 * ρ) (A / c)) ^ 2 ≤
      (max (2 * ρ) (A / c)) / (64 * A * c ^ 2) * (lam * a * ρ * c ^ 2) := by
  set r := max (2 * ρ) (A / c) with hr
  have ha : 0 < a := hδ.trans_le hδa
  have hA0 : 0 < A := ha.trans_le haA
  have hr0 : 0 < r := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hrb := renorm_radius hδ hδ1 hvLoss hδa haρc haA hA hρ hc
  have hratio := renorm_ratio hδ hδa hA
  -- δ^(2 vLoss) r ≤ 2 δ^(vLoss) ρ ≤ 2 (a/A) ρ
  have hdv : δ ^ (2 * vLoss) = δ ^ vLoss * δ ^ vLoss := by
    rw [← Real.rpow_add hδ]; congr 1; ring
  have hinv : δ ^ vLoss * δ ^ (-vLoss) = 1 := by
    rw [← Real.rpow_add hδ]; simp
  have hdvpos : 0 < δ ^ vLoss := Real.rpow_pos_of_pos hδ _
  have hkey : δ ^ (2 * vLoss) * r ≤ 2 * (a / A) * ρ := by
    -- δ^vLoss ≤ a / A
    have hva : δ ^ vLoss ≤ a / A := by
      rw [le_div_iff₀ hA0]
      have h1 : A ≤ δ ^ (-vLoss) * a := by rwa [div_le_iff₀ ha] at hratio
      have h2 : δ ^ vLoss * A ≤ δ ^ vLoss * (δ ^ (-vLoss) * a) :=
        mul_le_mul_of_nonneg_left h1 hdvpos.le
      have h3 : δ ^ vLoss * (δ ^ (-vLoss) * a) = a := by rw [← mul_assoc, hinv, one_mul]
      linarith
    have hdv1 : δ ^ vLoss ≤ 1 := Real.rpow_le_one hδ.le hδ1 hvLoss
    calc δ ^ (2 * vLoss) * r = δ ^ vLoss * (δ ^ vLoss * r) := by rw [hdv]; ring
      _ ≤ δ ^ vLoss * (δ ^ vLoss * (2 * δ ^ (-vLoss) * ρ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrb hdvpos.le) hdvpos.le
      _ = δ ^ vLoss * (2 * ρ) := by
          rw [show δ ^ vLoss * (2 * δ ^ (-vLoss) * ρ) = 2 * ρ * (δ ^ vLoss * δ ^ (-vLoss)) by ring,
            hinv, mul_one]
      _ ≤ (a / A) * (2 * ρ) := mul_le_mul_of_nonneg_right hva (by linarith)
      _ = 2 * (a / A) * ρ := by ring
  -- conclude
  have hrhs : r / (64 * A * c ^ 2) * (lam * a * ρ * c ^ 2) = lam * r * (a / A) * ρ / 64 := by
    field_simp
  rw [hrhs]
  have : (1 / 128 : ℝ) * lam * δ ^ (2 * vLoss) * r ^ 2 = lam * r * (δ ^ (2 * vLoss) * r) / 128 := by
    ring
  rw [this]
  have hlr : 0 ≤ lam * r := mul_nonneg hlam hr0.le
  have := mul_le_mul_of_nonneg_left hkey hlr
  nlinarith [this]

/-- `r ≤ 1/100` below a uniform cutoff when `vLoss < ω/100`. -/
theorem renorm_radius_small {ω vLoss : ℝ} (hgap : vLoss < ω / 100) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ δ ρ : ℝ, 0 < δ → δ ≤ d₀ → ρ ≤ δ ^ (ω / 100) →
      2 * δ ^ (-vLoss) * ρ ≤ 1 / 100 := by
  set g := ω / 100 - vLoss with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  refine ⟨min 1 ((1 / 200 : ℝ) ^ (1 / g)), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  intro δ ρ hδ hδd hρ
  have hδ1 : δ ≤ 1 := hδd.trans (min_le_left _ _)
  have hδc : δ ≤ (1 / 200 : ℝ) ^ (1 / g) := hδd.trans (min_le_right _ _)
  have hdg : δ ^ g ≤ 1 / 200 := by
    calc δ ^ g ≤ ((1 / 200 : ℝ) ^ (1 / g)) ^ g := Real.rpow_le_rpow hδ.le hδc hg0.le
      _ = 1 / 200 := by
          rw [← Real.rpow_mul (by norm_num)]
          rw [show 1 / g * g = 1 by field_simp, Real.rpow_one]
  have hsplit : δ ^ (-vLoss) * δ ^ (ω / 100) = δ ^ g := by
    rw [← Real.rpow_add hδ]; congr 1; rw [hg]; ring
  have hpos : 0 < δ ^ (-vLoss) := Real.rpow_pos_of_pos hδ _
  have h1 : 2 * δ ^ (-vLoss) * ρ ≤ 2 * δ ^ (-vLoss) * δ ^ (ω / 100) :=
    mul_le_mul_of_nonneg_left hρ (by positivity)
  nlinarith [h1, hsplit, hdg]

/-- Packet growth survives the renormalisation below a uniform cutoff. -/
theorem renorm_growth {t t0 vLoss : ℝ} (hgap : t + vLoss < t0) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ δ ρ θ : ℝ, 0 < δ → δ ≤ d₀ → 0 ≤ ρ →
      δ ^ (-t0) * ρ ≤ θ → δ ^ (-t) * (2 * δ ^ (-vLoss) * ρ) ≤ θ := by
  set g := t0 - t - vLoss with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  refine ⟨min 1 ((1 / 2 : ℝ) ^ (1 / g)), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  intro δ ρ θ hδ hδd hρ hθ
  have hδc : δ ≤ (1 / 2 : ℝ) ^ (1 / g) := hδd.trans (min_le_right _ _)
  have hdg : δ ^ g ≤ 1 / 2 := by
    calc δ ^ g ≤ ((1 / 2 : ℝ) ^ (1 / g)) ^ g := Real.rpow_le_rpow hδ.le hδc hg0.le
      _ = 1 / 2 := by
          rw [← Real.rpow_mul (by norm_num)]
          rw [show 1 / g * g = 1 by field_simp, Real.rpow_one]
  have hsplit : δ ^ (-t) * δ ^ (-vLoss) = δ ^ g * δ ^ (-t0) := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]; congr 1; rw [hg]; ring
  have hpos : 0 < δ ^ (-t0) := Real.rpow_pos_of_pos hδ _
  calc δ ^ (-t) * (2 * δ ^ (-vLoss) * ρ) = 2 * (δ ^ (-t) * δ ^ (-vLoss)) * ρ := by ring
    _ = 2 * (δ ^ g * δ ^ (-t0)) * ρ := by rw [hsplit]
    _ ≤ 2 * ((1 / 2) * δ ^ (-t0)) * ρ := by gcongr
    _ = δ ^ (-t0) * ρ := by ring
    _ ≤ θ := hθ

/-- Generic absorption of a constant into a positive power gap. -/
theorem const_absorption {C p q : ℝ} (hC : 0 ≤ C) (hpq : p < q) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → C * δ ^ q ≤ δ ^ p := by
  set g := q - p with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  refine ⟨min 1 ((C + 1)⁻¹ ^ (1 / g)), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  intro δ hδ hδd
  have hδc : δ ≤ (C + 1)⁻¹ ^ (1 / g) := hδd.trans (min_le_right _ _)
  have hdg : δ ^ g ≤ (C + 1)⁻¹ := by
    calc δ ^ g ≤ ((C + 1)⁻¹ ^ (1 / g)) ^ g := Real.rpow_le_rpow hδ.le hδc hg0.le
      _ = (C + 1)⁻¹ := by
          rw [← Real.rpow_mul (by positivity)]
          rw [show 1 / g * g = 1 by field_simp, Real.rpow_one]
  have hsplit : δ ^ q = δ ^ g * δ ^ p := by
    rw [← Real.rpow_add hδ]; congr 1; rw [hg]; ring
  have hp : 0 < δ ^ p := Real.rpow_pos_of_pos hδ _
  have h1 : C * δ ^ g ≤ C * (C + 1)⁻¹ := mul_le_mul_of_nonneg_left hdg hC
  have h2 : C * (C + 1)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ (by linarith)]; linarith
  rw [hsplit]
  nlinarith [h1, h2, hp]

/-! ### The clipped normalisation `S = min A (ρ c)` (x0708, 14:53Z) -/

/-- `a / S ≥ δ^vLoss` for the clipped short side `S = min A (ρ c)`. -/
theorem renormS_ratio {δ a A ρ c vLoss : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haρc : a ≤ ρ * c)
    (haA : a ≤ A) (hA : A < δ ^ (1 - vLoss)) :
    δ ^ vLoss ≤ a / min A (ρ * c) := by
  have ha : 0 < a := hδ.trans_le hδa
  have hS : 0 < min A (ρ * c) := lt_min (ha.trans_le haA) (ha.trans_le haρc)
  have hratio := renorm_ratio hδ hδa hA
  have hinv : δ ^ vLoss * δ ^ (-vLoss) = 1 := by
    rw [← Real.rpow_add hδ]; simp
  have hdv : 0 < δ ^ vLoss := Real.rpow_pos_of_pos hδ _
  have h1 : A ≤ δ ^ (-vLoss) * a := by rwa [div_le_iff₀ ha] at hratio
  rw [le_div_iff₀ hS]
  calc δ ^ vLoss * min A (ρ * c) ≤ δ ^ vLoss * A :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) hdv.le
    _ ≤ δ ^ vLoss * (δ ^ (-vLoss) * a) := mul_le_mul_of_nonneg_left h1 hdv.le
    _ = a := by rw [← mul_assoc, hinv, one_mul]

/-- The clipped renormalised old-row mass:
`J2 (λ a ρ c^2) ≥ (λ δ^vLoss / 256) (2ρ)^2` with `J2 = ρ / (64 S c^2)`. -/
theorem renormS_row_mass {δ a A ρ c lam vLoss : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a)
    (haρc : a ≤ ρ * c) (haA : a ≤ A) (hA : A < δ ^ (1 - vLoss)) (hρ : 0 < ρ) (hc : 0 < c)
    (hlam : 0 ≤ lam) :
    lam * δ ^ vLoss / 256 * (2 * ρ) ^ 2 ≤
      ρ / (64 * min A (ρ * c) * c ^ 2) * (lam * a * ρ * c ^ 2) := by
  have ha : 0 < a := hδ.trans_le hδa
  have hS : 0 < min A (ρ * c) := lt_min (ha.trans_le haA) (ha.trans_le haρc)
  have hr := renormS_ratio hδ hδa haρc haA hA
  have hrhs : ρ / (64 * min A (ρ * c) * c ^ 2) * (lam * a * ρ * c ^ 2) =
      lam * ρ ^ 2 / 64 * (a / min A (ρ * c)) := by
    field_simp
  rw [hrhs]
  have hl : lam * δ ^ vLoss / 256 * (2 * ρ) ^ 2 = lam * ρ ^ 2 / 64 * δ ^ vLoss := by ring
  rw [hl]
  exact mul_le_mul_of_nonneg_left hr (by positivity)

/-- The clipped row mass reaches `δ^u (2ρ)^2` below a uniform cutoff when `λ ≥ δ^h` and
`h + vLoss < u`. -/
theorem renormS_row_mass_power {h u vLoss : ℝ} (hgap : h + vLoss < u) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ δ a A ρ c lam : ℝ, 0 < δ → δ ≤ d₀ → δ ≤ a →
      a ≤ ρ * c → a ≤ A → A < δ ^ (1 - vLoss) → 0 < ρ → 0 < c → δ ^ h ≤ lam →
      δ ^ u * (2 * ρ) ^ 2 ≤ ρ / (64 * min A (ρ * c) * c ^ 2) * (lam * a * ρ * c ^ 2) := by
  obtain ⟨d₀, hd₀, hd₀1, Habs⟩ := const_absorption (C := 256) (p := h + vLoss) (q := u)
    (by norm_num) hgap
  refine ⟨d₀, hd₀, hd₀1, ?_⟩
  intro δ a A ρ c lam hδ hδd hδa haρc haA hA hρ hc hlam
  have hlam0 : 0 ≤ lam := (Real.rpow_nonneg hδ.le _).trans hlam
  have hmass := renormS_row_mass hδ hδa haρc haA hA hρ hc hlam0
  have h1 : 256 * δ ^ u ≤ δ ^ (h + vLoss) := Habs δ hδ hδd
  have h2 : δ ^ (h + vLoss) = δ ^ h * δ ^ vLoss := Real.rpow_add hδ _ _
  have h3 : δ ^ u ≤ lam * δ ^ vLoss / 256 := by
    have : δ ^ h * δ ^ vLoss ≤ lam * δ ^ vLoss :=
      mul_le_mul_of_nonneg_right hlam (Real.rpow_nonneg hδ.le _)
    rw [le_div_iff₀ (by norm_num)]
    linarith
  calc δ ^ u * (2 * ρ) ^ 2 ≤ lam * δ ^ vLoss / 256 * (2 * ρ) ^ 2 :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ ≤ _ := hmass

/-- The clipped short slab: `ρ A / (4 S) ≤ δ^(-vLoss) (2ρ)`. -/
theorem renormS_slab {δ a A ρ c vLoss : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hvLoss : 0 ≤ vLoss)
    (hδa : δ ≤ a) (haρc : a ≤ ρ * c) (haA : a ≤ A) (hA : A < δ ^ (1 - vLoss)) (hρ : 0 < ρ) :
    ρ * A / (4 * min A (ρ * c)) ≤ δ ^ (-vLoss) * (2 * ρ) := by
  have ha : 0 < a := hδ.trans_le hδa
  have hA0 : 0 < A := ha.trans_le haA
  have hS : 0 < min A (ρ * c) := lt_min hA0 (ha.trans_le haρc)
  have hpow1 : 1 ≤ δ ^ (-vLoss) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  -- A / S ≤ δ^(-vLoss)
  have hAS : A / min A (ρ * c) ≤ δ ^ (-vLoss) := by
    rcases min_choice A (ρ * c) with hmin | hmin
    · rw [hmin, div_self hA0.ne']; exact hpow1
    · rw [hmin]
      have h1 : A / (ρ * c) ≤ A / a := div_le_div_of_nonneg_left hA0.le ha haρc
      exact h1.trans (renorm_ratio hδ hδa hA)
  have h2 : ρ * A / (4 * min A (ρ * c)) = ρ / 4 * (A / min A (ρ * c)) := by
    field_simp
  rw [h2]
  have h3 : ρ / 4 * (A / min A (ρ * c)) ≤ ρ / 4 * δ ^ (-vLoss) :=
    mul_le_mul_of_nonneg_left hAS (by positivity)
  have h4 : 0 < δ ^ (-vLoss) := Real.rpow_pos_of_pos hδ _
  nlinarith [h3, h4]

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
