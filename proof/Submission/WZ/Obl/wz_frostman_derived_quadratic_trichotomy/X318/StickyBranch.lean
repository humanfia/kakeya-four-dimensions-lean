-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.StickyBranch.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.StickyAt
-- Copied from session x0338 (o070 branch, commit ec01e52, file StickyBranch.lean), namespace renamed.

/-!
# The sticky branch of the derived trichotomy

`stickyBranchStmt_holds : WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.StickyBranchStmt` proves x0305's statement of the sticky branch
(o038/x0305 `Branches.lean`, copied as `X305/Branches.lean`) exactly as stated.  The parameters:
`μ = min (min ω ξ) ζ₃`, `ν = μ / (1000 (Nmax + 1))` (the precision of x0318's `fibre_dichotomy`),
the threshold exponent `e = 2 (Nmax + 1) ν`, the Frostman exponent `ζF = min ζ₃ ξ / 8`, and the
retention `θ = ω / 2` of the flat exit.  All numerical hypotheses of `sticky_branch_at` have the
form `const ≤ δ^(-p)` with `p > 0` and hold for `δ` small (`eventually_le_rpow_neg`).
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy

/-- `A ≤ δ^(-p)` gives `A δ^p ≤ 1`. -/
lemma mul_rpow_le_one_of_le {A δ p : ℝ} (hδ : 0 < δ) (h : A ≤ δ ^ (-p)) : A * δ ^ p ≤ 1 := by
  have h1 : δ ^ (-p) * δ ^ p = 1 := by rw [← Real.rpow_add hδ]; simp
  calc A * δ ^ p ≤ δ ^ (-p) * δ ^ p := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hδ.le _)
    _ = 1 := h1

/-- `A ≤ δ^(-p)` gives `A δ^(-q) ≤ δ^(-(p + q))`. -/
lemma mul_rpow_neg_le_of_le {A δ p q : ℝ} (hδ : 0 < δ) (h : A ≤ δ ^ (-p)) :
    A * δ ^ (-q) ≤ δ ^ (-(p + q)) := by
  calc A * δ ^ (-q) ≤ δ ^ (-p) * δ ^ (-q) :=
        mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hδ.le _)
    _ = δ ^ (-(p + q)) := by rw [← Real.rpow_add hδ]; congr 1; ring

/-- **The sticky branch of the derived trichotomy** (x0305's `StickyBranchStmt`). -/
theorem stickyBranchStmt_holds : StickyBranchStmt := by
  intro ξ ζ₂ ζ₃ ω hζ₃ hζ₃₂ hζ₂ξ hω Nmax Cp
  have hζ₂ : 0 < ζ₂ := hζ₃.trans_le hζ₃₂
  have hξ : 0 < ξ := hζ₂.trans_le hζ₂ξ
  have hN1 : (1 : ℝ) ≤ (Nmax : ℝ) + 1 := by have := (Nat.cast_nonneg Nmax : (0 : ℝ) ≤ Nmax); linarith
  set N1 : ℝ := (Nmax : ℝ) + 1 with hN1def
  set μ : ℝ := min (min ω ξ) ζ₃ with hμdef
  have hμ : 0 < μ := lt_min (lt_min hω hξ) hζ₃
  have hμω : μ ≤ ω := (min_le_left _ _).trans (min_le_left _ _)
  have hμξ : μ ≤ ξ := (min_le_left _ _).trans (min_le_right _ _)
  have hμζ₃ : μ ≤ ζ₃ := min_le_right _ _
  set ν : ℝ := μ / (1000 * N1) with hνdef
  have hν : 0 < ν := by positivity
  have hνN1 : ν * N1 = μ / 1000 := by rw [hνdef]; field_simp
  have hνle : ν ≤ μ / 1000 := by
    rw [hνdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hνNmax : ν * Nmax ≤ μ / 1000 := by
    have : ν * Nmax ≤ ν * N1 := mul_le_mul_of_nonneg_left (by linarith) hν.le
    linarith
  set ζF : ℝ := min ζ₃ ξ / 8 with hζFdef
  have hζF : 0 < ζF := by positivity
  have hζFξ : ζF ≤ ξ / 8 := by
    rw [hζFdef]; have := min_le_right ζ₃ ξ; linarith
  have hζFζ₃ : ζF ≤ ζ₃ / 8 := by
    rw [hζFdef]; have := min_le_left ζ₃ ξ; linarith
  set θ : ℝ := ω / 2 with hθdef
  set e : ℝ := 2 * N1 * ν with hedef
  have he : e = μ / 500 := by rw [hedef]; linarith [hνN1]
  -- the exponents of the small-`δ` conditions
  have p4 : 0 < ξ - e := by rw [he]; linarith
  have p5 : 0 < e - ν * Nmax := by
    have : e - ν * Nmax = ν * (Nmax + 2) := by rw [hedef, hN1def]; ring
    rw [this]; positivity
  have p6 : 0 < ξ - ζF - ν * Nmax := by linarith
  have p7 : 0 < ξ / 2 - ζ₂ / 8 - ζ₂ / 200 - e - 2 * ν := by rw [he]; linarith
  have p8 : 0 < ω - ν * Nmax := by linarith
  have p10 : 0 < θ - 2 * ν := by rw [hθdef]; linarith
  have p11 : 0 < ζ₃ - (ζF + ν * ((Nmax : ℝ) + 1)) - 5 * (2 * ν) := by
    have : ν * ((Nmax : ℝ) + 1) = μ / 1000 := hνN1
    rw [this]; linarith
  have p13 : 0 < ω - θ - ν * Nmax := by rw [hθdef]; linarith
  -- thresholds
  obtain ⟨d₁, hd₁, hdich⟩ := fibreDich_of_le ν hν
  obtain ⟨d₂, hd₂, -, hpigE⟩ := flat_exit_pig_eventually ν (max Cp 1) hν (le_max_right _ _)
  obtain ⟨d₃, hd₃, h3⟩ := eventually_le_rpow_neg 2 hξ
  obtain ⟨d₄, hd₄, h4⟩ := eventually_le_rpow_neg 4 p4
  obtain ⟨d₅, hd₅, h5⟩ := eventually_le_rpow_neg (2 * 2 ^ Nmax * N1) p5
  obtain ⟨d₆, hd₆, h6⟩ := eventually_le_rpow_neg (2 * 2 ^ Nmax) p6
  obtain ⟨d₇, hd₇, h7⟩ := eventually_le_rpow_neg (1600 * (122 ^ 3 * 16 ^ 3) * 16) p7
  obtain ⟨d₈, hd₈, h8⟩ := eventually_le_rpow_neg (2 * 2 ^ Nmax) p8
  obtain ⟨d₉, hd₉, h9⟩ := eventually_le_rpow_neg 64 hν
  obtain ⟨d₁₀, hd₁₀, h10⟩ := eventually_le_rpow_neg 2 p10
  obtain ⟨d₁₁, hd₁₁, h11⟩ := eventually_le_rpow_neg localFlatLoss p11
  obtain ⟨d₁₂, hd₁₂, h12⟩ := eventually_le_rpow_neg (2 * 2 ^ Nmax) hν
  obtain ⟨d₁₃, hd₁₃, h13⟩ := eventually_le_rpow_neg (2 * 2 ^ Nmax) p13
  set δ₁ : ℝ := min (1 / 100) (min d₁ (min d₂ (min d₃ (min d₄ (min d₅ (min d₆ (min d₇
    (min d₈ (min d₉ (min d₁₀ (min d₁₁ (min d₁₂ d₁₃)))))))))))) with hδ₁def
  have hδ₁ : 0 < δ₁ := by
    simp only [hδ₁def, lt_min_iff]
    exact ⟨by norm_num, hd₁, hd₂, hd₃, hd₄, hd₅, hd₆, hd₇, hd₈, hd₉, hd₁₀, hd₁₁, hd₁₂, hd₁₃⟩
  refine ⟨ζF, hζF, δ₁, hδ₁, ?_⟩
  intro δ hδ hδδ₁ L top hL hLlow hLup htopN htop1 htop2 m x v S a hmCp hprep hst
  simp only [hδ₁def, le_min_iff] at hδδ₁
  obtain ⟨h100, hδd₁, hδd₂, hδd₃, hδd₄, hδd₅, hδd₆, hδd₇, hδd₈, hδd₉, hδd₁₀, hδd₁₁, hδd₁₂,
    hδd₁₃⟩ := hδδ₁
  have hδ1 : δ ≤ 1 := h100.trans (by norm_num)
  have hinv : (1 / δ) ^ (ξ / 2) = δ ^ (-(ξ / 2)) := by
    rw [one_div, Real.inv_rpow hδ.le, Real.rpow_neg hδ.le]
  refine sticky_branch_at (ξ := ξ) (ζ₂ := ζ₂) (ζ₃ := ζ₃) (ω := ω) (ν := ν) (ζF := ζF) (θ := θ)
    (e := e) (Nmax := Nmax) hξ hζ₂.le hζ₂ξ hν hζF.le hδ h100 (hdich δ hδ h100 hδd₁) hL hLup htopN
    htop1 htop2 x v S a hprep hst ?_ (h3 δ hδ hδd₃) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (h12 δ hδ hδd₁₂) ?_
  · -- the class-count bound of the flat exit
    intro n' hn'
    apply hpigE δ hδ hδd₂ n'
    have hm4 : (m : ℝ) ≤ Cp * δ ^ (-4 : ℝ) := by
      have h4pos : 0 < δ ^ (4 : ℝ) := Real.rpow_pos_of_pos hδ 4
      have hδ4 : δ ^ (4 : ℝ) = δ ^ 4 := by exact_mod_cast Real.rpow_natCast δ 4
      have hinv4 : δ ^ (-4 : ℝ) * δ ^ (4 : ℝ) = 1 := by rw [← Real.rpow_add hδ]; simp
      have : (m : ℝ) * δ ^ (4 : ℝ) ≤ Cp := by rw [hδ4]; exact hmCp
      calc (m : ℝ) = (m * δ ^ (4 : ℝ)) * δ ^ (-4 : ℝ) := by
            rw [mul_assoc, mul_comm (δ ^ (4 : ℝ)), hinv4, mul_one]
        _ ≤ Cp * δ ^ (-4 : ℝ) := mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hδ.le _)
    have hn'm : (n' : ℝ) ≤ m := by exact_mod_cast hn'
    calc (n' : ℝ) ≤ m := hn'm
      _ ≤ Cp * δ ^ (-4 : ℝ) := hm4
      _ ≤ max Cp 1 * δ ^ (-4 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hδ.le _)
  · -- hbalc
    have := mul_rpow_neg_le_of_le (q := e) hδ (h4 δ hδ hδd₄)
    rwa [show ξ - e + e = ξ by ring] at this
  · -- hsmall
    have h := mul_rpow_le_one_of_le hδ (h5 δ hδ hδd₅)
    calc 2 * (2 ^ Nmax * δ ^ (-(ν * Nmax))) * (((Nmax : ℝ) + 1) * δ ^ e)
        = (2 * 2 ^ Nmax * N1) * (δ ^ (-(ν * Nmax)) * δ ^ e) := by rw [hN1def]; ring
      _ = (2 * 2 ^ Nmax * N1) * δ ^ (e - ν * Nmax) := by
          rw [← Real.rpow_add hδ]; congr 2; ring
      _ ≤ 1 := h
  · -- hKM
    have h := mul_rpow_neg_le_of_le (q := ζF + ν * Nmax) hδ (h6 δ hδ hδd₆)
    calc 2 * δ ^ (-ζF) * (2 ^ Nmax * δ ^ (-(ν * Nmax)))
        = (2 * 2 ^ Nmax) * (δ ^ (-ζF) * δ ^ (-(ν * Nmax))) := by ring
      _ = (2 * 2 ^ Nmax) * δ ^ (-(ζF + ν * Nmax)) := by
          rw [← Real.rpow_add hδ]; congr 2; ring
      _ ≤ δ ^ (-(ξ - ζF - ν * Nmax + (ζF + ν * Nmax))) := h
      _ = δ ^ (-ξ) := by congr 1; ring
  · -- hcρ
    have h := mul_rpow_neg_le_of_le (q := ζ₂ / 8 + ν + ζ₂ / 200 + ξ / 2 + ν) hδ
      (h7 δ hδ hδd₇)
    rw [hinv]
    calc 1600 * (122 ^ 3 * 16 ^ 3) * δ ^ (-(ζ₂ / 8)) * (16 * δ ^ (-ν - ζ₂ / 200)) *
          δ ^ (-(ξ / 2)) * δ ^ (-ν)
        = (1600 * (122 ^ 3 * 16 ^ 3) * 16) *
            (δ ^ (-(ζ₂ / 8)) * δ ^ (-ν - ζ₂ / 200) * δ ^ (-(ξ / 2)) * δ ^ (-ν)) := by ring
      _ = (1600 * (122 ^ 3 * 16 ^ 3) * 16) * δ ^ (-(ζ₂ / 8 + ν + ζ₂ / 200 + ξ / 2 + ν)) := by
          rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
          congr 2; ring
      _ ≤ δ ^ (-(ξ / 2 - ζ₂ / 8 - ζ₂ / 200 - e - 2 * ν +
            (ζ₂ / 8 + ν + ζ₂ / 200 + ξ / 2 + ν))) := h
      _ = δ ^ (-ξ) * δ ^ e := by
          rw [← Real.rpow_add hδ]; congr 1; ring
  · -- hcountKT
    have h := mul_rpow_le_one_of_le hδ (h8 δ hδ hδd₈)
    calc 2 * (2 ^ Nmax * δ ^ (-(ν * Nmax))) * δ ^ ω
        = (2 * 2 ^ Nmax) * (δ ^ (-(ν * Nmax)) * δ ^ ω) := by ring
      _ = (2 * 2 ^ Nmax) * δ ^ (ω - ν * Nmax) := by
          rw [← Real.rpow_add hδ]; congr 2; ring
      _ ≤ 1 := h
  · -- h64
    have h := mul_rpow_le_one_of_le hδ (h9 δ hδ hδd₉)
    exact h
  · -- hretain
    exact mul_rpow_le_one_of_le hδ (h10 δ hδ hδd₁₀)
  · -- herror
    exact mul_rpow_le_one_of_le hδ (h11 δ hδ hδd₁₁)
  · -- hcountF
    have h := mul_rpow_neg_le_of_le (q := -(ω - ν * Nmax)) hδ (h13 δ hδ hδd₁₃)
    calc 2 * (2 ^ Nmax * δ ^ (-(ν * Nmax))) * δ ^ ω
        = (2 * 2 ^ Nmax) * (δ ^ (-(ν * Nmax)) * δ ^ ω) := by ring
      _ = (2 * 2 ^ Nmax) * δ ^ (-(-(ω - ν * Nmax))) := by
          rw [← Real.rpow_add hδ]; congr 2; ring
      _ ≤ δ ^ (-(ω - θ - ν * Nmax + -(ω - ν * Nmax))) := h
      _ = δ ^ θ := by congr 1; ring

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
