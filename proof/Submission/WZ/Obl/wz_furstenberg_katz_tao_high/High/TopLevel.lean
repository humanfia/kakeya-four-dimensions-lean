-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.TopLevel.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0675 High/TopLevel.lean (b19b589).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.PaletteArithmetic
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.Leaves
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.BushProfile
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.Halving

/-!
# The high range from its leaves

`high_range_of_leaves`: for `0 < s < 1`, the four leaves of `High/Leaves.lean` give
`FixedKatzTaoAt s`. A failed estimate (`failData_of_not`) contains a `HighConfig`
(`ConfigLeaf`); its profiles `G` (pins) and `F` (a bush) satisfy the counting bounds of
`High/Profiles.lean` and `High/BushProfile.lean` up to `2 ε n + log_B 900 ≤ 3 θ n`; the premise
(`PremiseLeaf`) and the profile analysis (`UniformityLeaf`) make the bushes near-uniform;
x0672's `halving_select` finds a right-min window of `G - s·id`, where `CaseALeaf` gives the
contradiction.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_tower_balanced_refinement

noncomputable section

/-! ### The palette -/



/-! ### The profiles of a failed configuration -/

section Profiles

variable {r s ε₀ ε : ℝ} {n : ℕ} {S : Finset (E2 × E2)}

theorem ptProfile_ge (h : FailData r s ε₀ ε (S.image Prod.fst) S) (hr1 : r < 1) (hn : 0 < n)
    {t : ℕ} (ht : t ≤ n) :
    (t : ℝ) - Real.logb (palBase r n) 2 - 2 * ε * n ≤ ptProfile r n S t := by
  have hr := h.r_pos
  have hB := palBase_gt_one hr hr1 hn
  have hQ : (S.image Prod.fst).Nonempty := h.P_ne
  have hρ0 : 0 < palBase r n ^ (-(t : ℝ)) := Real.rpow_pos_of_pos (palBase_pos hr) _
  have hρ : r ≤ 2 * palBase r n ^ (-(t : ℝ)) := by
    have := r_le_palScale hr hr1 hn ht
    unfold palScale at this
    linarith
  have hC : 0 < r ^ (-(2 * ε)) := Real.rpow_pos_of_pos hr _
  have hfr : ∀ x ∈ S.image Prod.fst,
      (((S.image Prod.fst).filter (fun z => dist z x ≤ 2 * palBase r n ^ (-(t : ℝ)))).card : ℝ) ≤
        r ^ (-(2 * ε)) * (2 * palBase r n ^ (-(t : ℝ))) * (S.image Prod.fst).card := by
    intro x _
    refine (h.P_kt x _ hρ).trans ?_
    have hQc := h.P_card
    have heq : r ^ (-ε) * ((2 * palBase r n ^ (-(t : ℝ))) / r) =
        r ^ (-(2 * ε)) * (2 * palBase r n ^ (-(t : ℝ))) * r ^ (ε - 1) := by
      have h1 : r ^ (-(2 * ε)) * r ^ (ε - 1) = r ^ (-ε) * r⁻¹ := by
        rw [← Real.rpow_add hr, ← Real.rpow_neg_one r, ← Real.rpow_add hr]
        congr 1; ring
      calc r ^ (-ε) * ((2 * palBase r n ^ (-(t : ℝ))) / r)
          = (2 * palBase r n ^ (-(t : ℝ))) * (r ^ (-ε) * r⁻¹) := by
            rw [div_eq_mul_inv]; ring
        _ = (2 * palBase r n ^ (-(t : ℝ))) * (r ^ (-(2 * ε)) * r ^ (ε - 1)) := by rw [h1]
        _ = _ := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hQc (by positivity)
  have hge := cellProfile_ge hQ hB hC t hfr
  have hlog : Real.logb (palBase r n) (2 * r ^ (-(2 * ε))) =
      Real.logb (palBase r n) 2 + 2 * ε * n := by
    rw [Real.logb_mul (by norm_num) hC.ne', logb_palBase_rpow hr hr1 hn]; ring
  unfold ptProfile
  linarith

theorem bushOf_nonempty (h : FailData r s ε₀ ε (S.image Prod.fst) S) {p₀ : E2}
    (hp₀ : p₀ ∈ S.image Prod.fst) : (bushOf S p₀).Nonempty := by
  have _ := h
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp₀
  exact ⟨q.2, mem_bushOf.mpr (by simpa using hq)⟩

theorem bushOf_unit (h : FailData r s ε₀ ε (S.image Prod.fst) S) (p₀ : E2) :
    ∀ e ∈ bushOf S p₀, ‖e‖ = 1 :=
  fun _ he => (h.D_mem _ (mem_bushOf.mp he)).2

theorem bushProfile_ge (h : FailData r s ε₀ ε (S.image Prod.fst) S) (hr1 : r < 1) (hn : 0 < n)
    (hs1 : s ≤ 1) {p₀ : E2} (hp₀ : p₀ ∈ S.image Prod.fst) {t : ℕ} (ht : t ≤ n) :
    s * t - 2 * ε * n - Real.logb (palBase r n) 2 ≤ bushProfile r n S p₀ t := by
  have hr := h.r_pos
  have hB := palBase_gt_one hr hr1 hn
  have hB0 := palBase_pos (n := n) hr
  have hρ0 : 0 < palBase r n ^ (-(t : ℝ)) := Real.rpow_pos_of_pos hB0 _
  have hρ : r ≤ 2 * palBase r n ^ (-(t : ℝ)) := by
    have := r_le_palScale hr hr1 hn ht
    unfold palScale at this
    linarith
  have hrB : r = palBase r n ^ (-(n : ℝ)) := (palBase_pow_n hr hn).symm
  have hcard : palBase r n ^ ((n : ℝ) * (s - ε)) ≤ ((bushOf S p₀).card : ℝ) := by
    have h1 := h.D_card p₀ hp₀
    rw [rpow_eq_palBase hr hn] at h1
    have : -(n : ℝ) * (ε - s) = (n : ℝ) * (s - ε) := by ring
    rwa [this] at h1
  have hball : ∀ x ∈ bushOf S p₀,
      (((bushOf S p₀).filter (fun z => dist z x ≤ 2 * palBase r n ^ (-(t : ℝ)))).card : ℝ) ≤
        palBase r n ^ ((n : ℝ) * ε + s * ((n : ℝ) - t) + Real.logb (palBase r n) 2) := by
    intro x hx
    refine (h.D_kt p₀ hp₀ x (bushOf_unit h p₀ x hx) _ hρ).trans ?_
    have e1 : r ^ (-ε) = palBase r n ^ ((n : ℝ) * ε) := by
      rw [rpow_eq_palBase hr hn]; ring_nf
    have e2 : 2 * palBase r n ^ (-(t : ℝ)) / r = 2 * palBase r n ^ ((n : ℝ) - t) := by
      calc 2 * palBase r n ^ (-(t : ℝ)) / r
          = 2 * palBase r n ^ (-(t : ℝ)) / palBase r n ^ (-(n : ℝ)) := by rw [← hrB]
        _ = 2 * (palBase r n ^ (-(t : ℝ)) / palBase r n ^ (-(n : ℝ))) := by ring
        _ = 2 * palBase r n ^ ((n : ℝ) - t) := by
            rw [← Real.rpow_sub hB0]; ring_nf
    have e3 : (2 * palBase r n ^ ((n : ℝ) - t)) ^ s =
        (2 : ℝ) ^ s * palBase r n ^ (s * ((n : ℝ) - t)) := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_pos_of_pos hB0 _).le, ← Real.rpow_mul hB0.le]
      ring_nf
    have h2s : (2 : ℝ) ^ s ≤ palBase r n ^ (Real.logb (palBase r n) 2) := by
      rw [Real.rpow_logb hB0 hB.ne' (by norm_num)]
      have hs0 : 0 ≤ s ∨ s < 0 := le_or_gt 0 s
      calc (2 : ℝ) ^ s ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
        _ = 2 := Real.rpow_one 2
    rw [e2, e3, e1]
    have hprod : palBase r n ^ ((n : ℝ) * ε + s * ((n : ℝ) - t) + Real.logb (palBase r n) 2) =
        palBase r n ^ ((n : ℝ) * ε) * (palBase r n ^ (Real.logb (palBase r n) 2) *
          palBase r n ^ (s * ((n : ℝ) - t))) := by
      rw [← Real.rpow_add hB0, ← Real.rpow_add hB0]; ring_nf
    rw [hprod]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos hB0 _).le
    exact mul_le_mul_of_nonneg_right h2s (Real.rpow_pos_of_pos hB0 _).le
  have hge := cellProfile_ge_of_balls (bushOf_nonempty h hp₀) hB t hcard hball
  unfold bushProfile
  linarith

theorem bushProfile_n_le (h : FailData r s ε₀ ε (S.image Prod.fst) S) (hr1 : r < 1)
    (hn : 0 < n) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {p₀ : E2} (hp₀ : p₀ ∈ S.image Prod.fst) :
    bushProfile r n S p₀ n ≤ s * n + ε * n + Real.logb (palBase r n) 2 := by
  have hr := h.r_pos
  have hB := palBase_gt_one hr hr1 hn
  have hB0 := palBase_pos (n := n) hr
  have hrB : r = palBase r n ^ (-(n : ℝ)) := (palBase_pow_n hr hn).symm
  have hle := cellProfile_le_card (bushOf_nonempty h hp₀) hB n
  have hbush := h.bush_le (by linarith) hp₀
  have e1 : r ^ (-ε) = palBase r n ^ ((n : ℝ) * ε) := by
    rw [rpow_eq_palBase hr hn]; ring_nf
  have e2 : 2 / r = 2 * palBase r n ^ (n : ℝ) := by
    calc 2 / r = 2 / palBase r n ^ (-(n : ℝ)) := by rw [← hrB]
      _ = 2 * palBase r n ^ (n : ℝ) := by
          rw [Real.rpow_neg hB0.le, div_inv_eq_mul]
  have e3 : (2 * palBase r n ^ (n : ℝ)) ^ s = (2 : ℝ) ^ s * palBase r n ^ (s * n) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_pos_of_pos hB0 _).le, ← Real.rpow_mul hB0.le]
    ring_nf
  have h2s : (2 : ℝ) ^ s ≤ palBase r n ^ (Real.logb (palBase r n) 2) := by
    rw [Real.rpow_logb hB0 hB.ne' (by norm_num)]
    calc (2 : ℝ) ^ s ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
      _ = 2 := Real.rpow_one 2
  have hcard : ((bushOf S p₀).card : ℝ) ≤
      palBase r n ^ ((n : ℝ) * ε + Real.logb (palBase r n) 2 + s * n) := by
    refine hbush.trans ?_
    rw [e2, e3, e1]
    have hprod : palBase r n ^ ((n : ℝ) * ε + Real.logb (palBase r n) 2 + s * n) =
        palBase r n ^ ((n : ℝ) * ε) * (palBase r n ^ (Real.logb (palBase r n) 2) *
          palBase r n ^ (s * n)) := by
      rw [← Real.rpow_add hB0, ← Real.rpow_add hB0]; ring_nf
    rw [hprod]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos hB0 _).le
    exact mul_le_mul_of_nonneg_right h2s (Real.rpow_pos_of_pos hB0 _).le
  have hpos : (0 : ℝ) < (bushOf S p₀).card := by
    exact_mod_cast (bushOf_nonempty h hp₀).card_pos
  have hlog := Real.logb_le_logb_of_le hB hpos hcard
  rw [Real.logb_rpow hB0 hB.ne'] at hlog
  have _ := hs0
  unfold bushProfile
  linarith

end Profiles

/-! ### The halving arithmetic -/

/-- x0672's `halving_select` with the window fraction `c = (1 - s) / (8 (2 - s))`: some level
`a = 2 ^ (j + 1) M ≤ n = 2 ^ K M` has a right-min `h ∈ [a / 2, (1 - c) a]` of `G - s·id`. -/
theorem halving_window (G : ℕ → ℝ) {s E : ℝ} {K M : ℕ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hKs : (2 : ℝ) / (1 - s) + 3 ≤ 2 ^ K) (hM1 : 1 ≤ M) (hMs : 2 ≤ (1 - s) / 16 * M)
    (hEM : E ≤ 3 * (1 - s) / 32 * M)
    (hlip : ∀ i j : ℕ, i ≤ j → G j - G i ≤ 2 * ((j : ℝ) - i) + E)
    (htop : ((2 ^ K * M : ℕ) : ℝ) - E ≤ G (2 ^ K * M))
    (hbot : G M ≤ 2 * M + E) :
    ∃ h a : ℕ, a ≤ 2 ^ K * M ∧ ((2 ^ K * M : ℕ) : ℝ) ≤ 2 ^ K * (a : ℝ) ∧ (a : ℝ) ≤ 2 * h ∧
      (h : ℝ) + (1 - s) / (8 * (2 - s)) * a ≤ a ∧
      ∀ i : ℕ, h ≤ i → i ≤ a → G h - s * h ≤ G i - s * i := by
  have h1s : 0 < 1 - s := by linarith
  have h2s : 0 < 2 - s := by linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (1 - s) / (8 * (2 - s)) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  have hcs : (2 - s) * c = (1 - s) / 8 := by rw [hc]; field_simp
  have hM0 : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  let w : ℕ → ℕ := fun k => ⌈c * ((2 ^ k * M : ℕ) : ℝ)⌉₊
  have hwle : ∀ k : ℕ, (w k : ℝ) < c * ((2 ^ k * M : ℕ) : ℝ) + 1 := fun k =>
    Nat.ceil_lt_add_one (by positivity)
  have hw : ∀ j : ℕ, (2 - s) * (w (j + 1) : ℝ) + E ≤ (1 - s) / 2 * ((2 ^ j * M : ℕ) : ℝ) := by
    intro j
    have h1 := hwle (j + 1)
    obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ((2 ^ j * M : ℕ) : ℝ) := ⟨_, rfl⟩
    have hXM : (M : ℝ) ≤ X := by
      rw [hX]; push_cast
      have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      nlinarith
    have h2 : ((2 ^ (j + 1) * M : ℕ) : ℝ) = 2 * X := by rw [hX]; push_cast; ring
    rw [h2] at h1
    rw [← hX]
    have h3 : (2 - s) * (w (j + 1) : ℝ) ≤ (2 - s) * (c * (2 * X) + 1) :=
      mul_le_mul_of_nonneg_left h1.le h2s.le
    have h4 : (2 - s) * (c * (2 * X) + 1) = (1 - s) / 4 * X + (2 - s) := by
      have : (2 - s) * (c * (2 * X)) = 2 * ((2 - s) * c) * X := by ring
      rw [mul_add, this, hcs]; ring
    have h5 : (1 - s) / 4 * (M : ℝ) ≤ (1 - s) / 4 * X :=
      mul_le_mul_of_nonneg_left hXM (by positivity)
    have h6 : (1 - s) / 16 * (M : ℝ) + 3 * (1 - s) / 32 * M ≤ (1 - s) / 4 * M := by
      have : (0 : ℝ) ≤ (1 - s) * M := by positivity
      linarith
    linarith
  have hK : (M : ℝ) + 2 * E < (1 - s) / 2 * (((2 ^ K - 1 : ℕ) : ℝ) * M) := by
    have hcast : (((2 ^ K - 1 : ℕ) : ℝ)) = 2 ^ K - 1 := by
      rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow]; norm_num
    rw [hcast]
    have h1 : (2 / (1 - s) + 2) * (M : ℝ) ≤ (2 ^ K - 1) * M :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : (1 - s) / 2 * ((2 / (1 - s) + 2) * (M : ℝ)) = M + (1 - s) * M := by
      field_simp
    have h3 : (1 - s) / 2 * ((2 / (1 - s) + 2) * (M : ℝ)) ≤ (1 - s) / 2 * ((2 ^ K - 1) * M) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h4 : 0 < (1 - s) * (M : ℝ) := by positivity
    linarith
  obtain ⟨j, hjK, h, hh1, hh2, hmin⟩ := halving_select G (K := K) (M := M) (s := s) (E := E)
    hs1 w hlip htop hbot hw hK
  refine ⟨h, 2 ^ (j + 1) * M, ?_, ?_, ?_, ?_, hmin⟩
  · exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hjK)
  · push_cast
    have h1 : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ (by norm_num)
    have h0 : (0 : ℝ) ≤ 2 ^ K * M := by positivity
    nlinarith
  · have : ((2 ^ j * M : ℕ) : ℝ) ≤ h := by exact_mod_cast hh1
    push_cast at this ⊢
    rw [pow_succ]
    linarith
  · have h1 : c * ((2 ^ (j + 1) * M : ℕ) : ℝ) ≤ w (j + 1) := Nat.le_ceil _
    have h2 : ((h + w (j + 1) : ℕ) : ℝ) ≤ ((2 ^ (j + 1) * M : ℕ) : ℝ) := by exact_mod_cast hh2
    push_cast at h2 h1 ⊢
    rw [← hc]
    linarith

/-! ### The top level -/

/-- **The high range from its leaves.** -/
theorem high_range_of_leaves {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hC : ConfigLeaf s) (hE : PremiseLeaf s) (hU : UniformityLeaf s) (hA : CaseALeaf s) :
    FixedKatzTaoAt s := by
  have h1s : 0 < 1 - s := by linarith
  have h2s : 0 < 2 - s := by linarith
  -- the window fraction and the number of halvings
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (1 - s) / (8 * (2 - s)) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈2 / (1 - s)⌉₊ + 2 := ⟨_, rfl⟩
  have hKs : (2 : ℝ) / (1 - s) + 3 ≤ 2 ^ K := by
    have h1 : K + 1 ≤ 2 ^ K := Nat.lt_two_pow_self
    have h2 := Nat.le_ceil (2 / (1 - s))
    have h3 : ((K + 1 : ℕ) : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast h1
    rw [hK] at h3
    push_cast at h3
    rw [hK]
    linarith
  have hL1 : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
  obtain ⟨d, εA, hd, hεA, NA, hA1⟩ := hA c (2 ^ K) hc0 hL1
  obtain ⟨eU, heU, NU, hU1⟩ := hU d hd
  obtain ⟨εP, hεP, NP, hE1⟩ := hE (eU / 2) (by positivity)
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = min (min ((1 - s) / (32 * 2 ^ K)) (eU / 8)) (d / 8) :=
    ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; exact lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have hθ1 : θ * 2 ^ K ≤ (1 - s) / 32 := by
    have h1 : θ ≤ (1 - s) / (32 * 2 ^ K) := by
      rw [hθ]; exact (min_le_left _ _).trans (min_le_left _ _)
    have h2 : (0 : ℝ) < 2 ^ K := by positivity
    calc θ * 2 ^ K ≤ (1 - s) / (32 * 2 ^ K) * 2 ^ K := mul_le_mul_of_nonneg_right h1 h2.le
      _ = (1 - s) / 32 := by field_simp
  have hθ2 : θ ≤ eU / 8 := by rw [hθ]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hθ3 : θ ≤ d / 8 := by rw [hθ]; exact min_le_right _ _
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = min (min εA εP) θ := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; exact lt_min (lt_min hεA hεP) hθ0
  have hκA : κ ≤ εA := by rw [hκ]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hκP : κ ≤ εP := by rw [hκ]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hκθ : κ ≤ θ := by rw [hκ]; exact min_le_right _ _
  obtain ⟨ε, hε0, hεκ, η₀, hη₀, hC1⟩ := hC κ hκ0
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = max (max (max NA NU) NP) (⌈32 / (1 - s)⌉₊ + 1) := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by rw [hM]; exact le_trans (by omega) (le_max_right _ _)
  have hMs : 32 / (1 - s) ≤ (M : ℝ) := by
    have h1 : ⌈32 / (1 - s)⌉₊ + 1 ≤ M := by rw [hM]; exact le_max_right _ _
    have h2 := Nat.le_ceil (32 / (1 - s))
    have h3 : ((⌈32 / (1 - s)⌉₊ + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast h1
    push_cast at h3
    linarith
  have hM2 : 2 ≤ (1 - s) / 16 * M := by
    have := mul_le_mul_of_nonneg_left hMs (by positivity : (0 : ℝ) ≤ (1 - s) / 16)
    have h32 : (1 - s) / 16 * (32 / (1 - s)) = 2 := by field_simp; ring
    linarith
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = 2 ^ K * M := ⟨_, rfl⟩
  have hMn : M ≤ n := by rw [hn]; exact Nat.le_mul_of_pos_left _ (by positivity)
  have hn0 : 0 < n := lt_of_lt_of_le (by omega) hMn
  have hNAM : NA ≤ M := by
    rw [hM]; exact le_max_of_le_left (le_max_of_le_left (le_max_left _ _))
  have hNUM : NU ≤ M := by
    rw [hM]; exact le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
  have hNPM : NP ≤ M := by
    rw [hM]; exact le_max_of_le_left (le_max_right _ _)
  have hNA : NA ≤ n := le_trans hNAM hMn
  have hNU : NU ≤ n := le_trans hNUM hMn
  have hNP : NP ≤ n := le_trans hNPM hMn
  obtain ⟨r₁C, hr₁C, hC2⟩ := hC1 n hn0
  obtain ⟨r₁A, hr₁A, hA2⟩ := hA1 n hNA
  obtain ⟨r₁P, hr₁P, hE2⟩ := hE1 n hNP
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ℝ, ε₀ = min (min η₀ εA) εP := ⟨_, rfl⟩
  have hε₀0 : 0 < ε₀ := by rw [hε₀]; exact lt_min (lt_min hη₀ hεA) hεP
  have hε₀η : ε₀ ≤ η₀ := by rw [hε₀]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hε₀A : ε₀ ≤ εA := by rw [hε₀]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hε₀P : ε₀ ≤ εP := by rw [hε₀]; exact min_le_right _ _
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : ℝ, r₀ = min (min (min r₁C r₁A)
      (min r₁P (Real.exp (-(Real.log 900 / θ))))) (1 / 2) := ⟨_, rfl⟩
  have hr₀0 : 0 < r₀ := by
    rw [hr₀]
    exact lt_min (lt_min (lt_min hr₁C hr₁A) (lt_min hr₁P (Real.exp_pos _))) (by norm_num)
  refine ⟨ε₀, ε₀, r₀, hε₀0, hε₀0, hr₀0, ?_⟩
  intro r hr hrr₀
  rw [hr₀] at hrr₀
  have hrC : r ≤ r₁C := hrr₀.trans ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hrA : r ≤ r₁A := hrr₀.trans ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hrP : r ≤ r₁P := hrr₀.trans ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hrL : r ≤ Real.exp (-(Real.log 900 / θ)) := hrr₀.trans ((min_le_left _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hr1 : r < 1 := by
    have : r ≤ 1 / 2 := hrr₀.trans (min_le_right _ _)
    linarith
  by_contra hfail
  obtain ⟨P, D, hPD⟩ := failData_of_not hr hfail
  obtain ⟨S, J₀, cls, J₁, tb, hcfg⟩ := hC2 r ε₀ ε₀ P D hr hrC hε₀0 hε₀η hε₀0 hε₀η hPD
  have hfS := hcfg.failS
  obtain ⟨p₀, hp₀⟩ := hfS.P_ne
  have hB : 1 < palBase r n := palBase_gt_one hr hr1 hn0
  -- the additive errors: everything is at most `T = θ n`
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = θ * n := ⟨_, rfl⟩
  have hl900 : Real.logb (palBase r n) 900 ≤ T := by
    rw [hT]; exact logb_palBase_le hr hr1 hn0 (by norm_num) hθ0 hrL
  have hl2 := logb_le_logb_900 hB (by norm_num : (0 : ℝ) < 2) (by norm_num)
  have hl4 := logb_le_logb_900 hB (by norm_num : (0 : ℝ) < 4) (by norm_num)
  have hl9 := logb_le_logb_900 hB (by norm_num : (0 : ℝ) < 9) (by norm_num)
  have hl36 := logb_le_logb_900 hB (by norm_num : (0 : ℝ) < 36) (by norm_num)
  have hl100 := logb_le_logb_900 hB (by norm_num : (0 : ℝ) < 100) (by norm_num)
  have hl2pos : 0 ≤ Real.logb (palBase r n) 2 := Real.logb_nonneg hB (by norm_num)
  have hεn : ε * n ≤ T := by
    rw [hT]; exact mul_le_mul_of_nonneg_right (hεκ.trans hκθ) hn'.le
  have hTU : 8 * T ≤ eU * n := by
    have := mul_le_mul_of_nonneg_right (by linarith : 8 * θ ≤ eU) hn'.le
    rw [hT]; linarith
  have hTd : 8 * T ≤ d * n := by
    have := mul_le_mul_of_nonneg_right (by linarith : 8 * θ ≤ d) hn'.le
    rw [hT]; linarith
  have hTM : 3 * T ≤ 3 * (1 - s) / 32 * M := by
    have h1 : T = θ * 2 ^ K * M := by rw [hT, hn]; push_cast; ring
    have h2 : (0 : ℝ) ≤ M := by positivity
    have h3 := mul_le_mul_of_nonneg_right hθ1 h2
    rw [h1]
    linarith
  -- the profiles
  have hQ : (S.image Prod.fst).Nonempty := hfS.P_ne
  have hbne := bushOf_nonempty hfS hp₀
  have hGlip : ∀ i j : ℕ, i ≤ j → ptProfile r n S j - ptProfile r n S i ≤
      2 * ((j : ℝ) - i) + T := fun i j hij => by
    have := cellProfile_lip hQ hB hij (Q := S.image Prod.fst)
    unfold ptProfile; linarith
  have hGle : ∀ t : ℕ, ptProfile r n S t ≤ 2 * (t : ℝ) + T := fun t => by
    have := cellProfile_le hQ hfS.P_norm hB t
    unfold ptProfile; linarith
  have hGge : ∀ t : ℕ, t ≤ n → (t : ℝ) - 3 * T ≤ ptProfile r n S t := fun t ht => by
    have := ptProfile_ge hfS hr1 hn0 ht
    linarith
  have hFmono : ∀ i j : ℕ, i ≤ j → bushProfile r n S p₀ i ≤ bushProfile r n S p₀ j + T :=
    fun i j hij => by
      have := cellProfile_mono' hbne hB hij
      unfold bushProfile; linarith
  have hFlip : ∀ i j : ℕ, i ≤ j → bushProfile r n S p₀ j - bushProfile r n S p₀ i ≤
      ((j : ℝ) - i) + T := fun i j hij => by
    have := cellProfile_circle_lip hbne (bushOf_unit hfS p₀) hB hij
    unfold bushProfile; linarith
  have hFge : ∀ t : ℕ, t ≤ n → s * t - 3 * T ≤ bushProfile r n S p₀ t := fun t ht => by
    have := bushProfile_ge hfS hr1 hn0 hs1.le hp₀ ht
    linarith
  have hFn : bushProfile r n S p₀ n ≤ s * n + 2 * T := by
    have := bushProfile_n_le hfS hr1 hn0 hs0.le hs1.le hp₀
    linarith
  -- the premise and near-uniform bushes
  have hprem := hE2 r ε₀ ε κ P D S J₀ cls J₁ tb hr hrP hε₀0 hε₀P hε0
    (hεκ.trans hκP) hκ0 hκP hcfg p₀ hp₀
  have hunif := hU1 n hNU (bushProfile r n S p₀) (ptProfile r n S)
    (by
      rw [abs_le]
      have := hFge n le_rfl
      constructor <;> linarith)
    (fun i j hij _ => by have := hFmono i j hij; linarith)
    (fun i j hij _ => by have := hFlip i j hij; linarith)
    (fun t ht => by have := hFge t ht; linarith)
    (fun t ht => by
      have h1 := hGge t ht
      have h2 := hGle t
      constructor <;> linarith)
    (fun h a hh hha han => by
      obtain ⟨y, hy1, hy2, hy3⟩ := hprem h a hh hha han
      exact ⟨y, hy1, hy2, by linarith⟩)
  -- the halving selection and case A
  have htop : ((2 ^ K * M : ℕ) : ℝ) - 3 * T ≤ ptProfile r n S (2 ^ K * M) := by
    have := hGge n le_rfl
    rw [← hn]
    exact this
  obtain ⟨h, a, han, hnLa, ha2h, hhca, hmin⟩ := halving_window (ptProfile r n S) (E := 3 * T)
    hs0.le hs1 hKs hM1 hM2 hTM (fun i j hij => by have := hGlip i j hij; linarith) htop
    (by have := hGle M; linarith)
  rw [← hn] at han hnLa
  rw [← hc] at hhca
  exact hA2 r ε₀ ε κ P D S J₀ cls J₁ tb hr hrA hε₀0 hε₀A hε0 (hεκ.trans hκA) hκ0 hκA hcfg p₀
    hp₀ h a han hnLa ha2h hhca hmin (fun t ht => by
      rw [abs_le]
      have h1 := hFge t ht
      have h2 := hunif t ht
      constructor <;> linarith)

end

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
