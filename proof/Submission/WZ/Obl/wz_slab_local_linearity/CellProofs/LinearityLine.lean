-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CellProofs.LinearityLine.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CellProofs.LinearityApply

/-!
# Dot-product triples and the dichotomy give a linear slope (sticky Lemma 5.3, end)

`DotTriples.exists_linear`: an instance of `LinearityDichotomy` at a scale `δ` adapted to the
cells produces a linear function within `ρ / 8` of `f` on `δ^{ε-1}` layers.
-/

namespace WangZahlLot.Obl.wz_slab_local_linearity.CellProofs

open Finset Set Metric
open scoped RealInnerProductSpace

noncomputable section

theorem abs_apply_le_norm2 (v : Plane) (i : Fin 2) : |v i| ≤ ‖v‖ := by
  have := PiLp.norm_apply_le v i
  rwa [Real.norm_eq_abs] at this

set_option maxHeartbeats 1000000 in
theorem DotTriples.exists_linear {ρ : ℝ} {M : ℕ} {κ σ K ε η δ : ℝ} {f : ℝ → ℝ}
    {A : ℤ → Set ℝ} {k0 w : ℤ} {Y g : ℤ → ℝ} {R : Finset ℤ} {T : Finset (ℤ × ℤ × ℤ)}
    (hT : DotTriples ρ M κ f A k0 w Y g R T)
    (hρ : 0 < ρ) (hM : 0 < M) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hf : ∀ z z', 0 ≤ z → z ≤ M * ρ → 0 ≤ z' → z' ≤ M * ρ → |f z - f z'| ≤ |z - z'|)
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hK : 0 ≤ K) (hA : Assouad ρ (1 - σ) K (A k0))
    (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hLD : LDInstance σ ε η δ) {N₀ : ℝ}
    (hN₀a : 8 * δ * (M * ρ) / ρ + 1 ≤ N₀) (hN₀b : 12 * δ / (κ / 8 * (M * ρ)) + 1 ≤ N₀)
    (n4 : 11 ≤ δ ^ (-η))
    (n5 : 12000 / κ ^ 2 ≤ δ ^ (-η))
    (n6 : 2 * (N₀ ^ 3 * δ ^ (η - 3)) ≤ #T)
    (n7 : κ / 8 * ρ / (M * ρ) ≤ δ)
    (n8 : 6 * K ≤ δ ^ (-η))
    (n10 : 48 * (M * ρ) * δ ≤ ρ) :
    ∃ a0 b0 : ℝ, |b0| ≤ 2 ∧ ∃ Ks : Finset ℤ, Ks ⊆ T.image (fun t => t.1) ∧ δ ^ (ε - 1) ≤ #Ks ∧
      ∀ k ∈ Ks, |f (ρ * k) - (a0 + b0 * (ρ * k))| ≤ ρ / 8 := by
  classical
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hs : 0 < (M : ℝ) * ρ := by positivity
  obtain ⟨e, he, Te, hTeT, hTecard, hTesign⟩ := exists_half T k0
  have he2 : e * e = 1 := by rcases he with rfl | rfl <;> norm_num
  have heabs : |e| = 1 := by rcases he with rfl | rfl <;> norm_num
  -- coordinates
  set s := (M : ℝ) * ρ with hsdef
  set μ := κ / 8 with hμ
  set x : ℤ → ℝ := fun k => (ρ * k - ρ * k0) / s with hx
  set y : ℤ → ℝ := fun k => (f (ρ * k) - f (ρ * k0)) / s with hy
  set a : ℤ → Plane := fun k => pt ((e * x k + y k) / 2) ((e * x k - y k) / 2) with ha
  set b : ℤ → Plane := fun j =>
    pt ((e * (-μ * g j) + μ * Y j) / 4 + 1 / 2) ((e * (-μ * g j) - μ * Y j) / 4 + 1 / 2) with hb
  set Ks := Te.image fun t => t.1 with hKs
  set lam := μ / (4 * s) with hlam
  set D := (fun z => lam * z + 0) '' {z | ∃ v ∈ A k0, |z - (v - w * ρ)| ≤ 4 * ρ} with hDdef
  -- layers of `Ks`
  have hKsmem : ∀ k ∈ Ks, (0 ≤ k ∧ k < M) ∧ 0 ≤ e * ((k : ℝ) - k0) := by
    intro k hk
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨(hT.T_mem t (hTeT ht)).1, hTesign t ht⟩
  have hk0 := hT.k0_mem
  have hheight : ∀ k : ℤ, 0 ≤ k → k < M → 0 ≤ ρ * k ∧ ρ * k ≤ M * ρ := by
    intro k h0 h1
    constructor
    · exact mul_nonneg hρ.le (by exact_mod_cast h0)
    · have : (k : ℝ) ≤ M := by exact_mod_cast h1.le
      nlinarith
  have hz0 := hheight k0 hk0.1 hk0.2
  -- basic facts on `x`, `y`
  have hxabs : ∀ k ∈ Ks, |x k| = e * x k ∧ |x k| ≤ 1 := by
    intro k hk
    obtain ⟨⟨h0, h1⟩, hsg⟩ := hKsmem k hk
    have hxk : x k = (k - k0 : ℝ) / M := by
      simp only [hx, hsdef]; field_simp
    have hnn : 0 ≤ e * x k := by
      rw [hxk, ← mul_div_assoc]; exact div_nonneg hsg hMpos.le
    constructor
    · rw [← abs_of_nonneg hnn, abs_mul, heabs, one_mul]
    · rw [hxk, abs_div, abs_of_pos hMpos, div_le_one hMpos]
      have : |k - k0| ≤ (M : ℤ) := by rw [abs_le]; constructor <;> omega
      have : |((k - k0 : ℤ) : ℝ)| ≤ (M : ℝ) := by exact_mod_cast this
      push_cast at this; exact this
  have hylip : ∀ k ∈ Ks, ∀ k' ∈ Ks, |y k - y k'| ≤ |x k - x k'| := by
    intro k hk k' hk'
    obtain ⟨⟨h0, h1⟩, -⟩ := hKsmem k hk
    obtain ⟨⟨h0', h1'⟩, -⟩ := hKsmem k' hk'
    have hzk := hheight k h0 h1
    have hzk' := hheight k' h0' h1'
    have := hf _ _ hzk.1 hzk.2 hzk'.1 hzk'.2
    have e1 : y k - y k' = (f (ρ * k) - f (ρ * k')) / s := by simp only [hy]; ring
    have e2 : x k - x k' = (ρ * k - ρ * k') / s := by simp only [hx]; ring
    rw [e1, e2, abs_div, abs_div, abs_of_pos hs]
    exact div_le_div_of_nonneg_right this hs.le
  have hyabs : ∀ k ∈ Ks, |y k| ≤ |x k| := by
    intro k hk
    obtain ⟨⟨h0, h1⟩, -⟩ := hKsmem k hk
    have hzk := hheight k h0 h1
    have := hf _ _ hzk.1 hzk.2 hz0.1 hz0.2
    simp only [hx, hy]
    rw [abs_div, abs_div, abs_of_pos hs]
    exact div_le_div_of_nonneg_right this hs.le
  -- the tilts and rows in `R`
  have hgμ : ∀ j ∈ R, |μ * g j| ≤ 1 := by
    intro j hj
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < μ)]
    have := hT.g_bound j hj
    calc μ * |g j| ≤ μ * (8 / κ) := by gcongr
      _ = 1 := by simp only [hμ]; field_simp
  have hYμ : ∀ j ∈ R, |μ * Y j| ≤ 1 := by
    intro j hj
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < μ)]
    have := hT.Y_bound j hj
    have hμ1 : μ ≤ 1 := by simp only [hμ]; linarith
    nlinarith [abs_nonneg (Y j)]
  -- the dichotomy hypotheses
  have hsq_a : ∀ k ∈ Ks, a k ∈ unitSquare := by
    intro k hk
    obtain ⟨h1, h2⟩ := hxabs k hk
    have h3 := hyabs k hk
    rw [abs_le] at h3
    intro i
    fin_cases i
    · simp only [ha, pt_zero, Fin.zero_eta, Fin.isValue]
      constructor <;> linarith
    · simp only [ha, pt_one, Fin.mk_one, Fin.isValue]
      constructor <;> linarith
  have hsq_b : ∀ j ∈ R, b j ∈ unitSquare := by
    intro j hj
    have h1 := hgμ j hj
    have h2 := hYμ j hj
    have h3 : |e * (-μ * g j)| ≤ 1 := by
      rw [abs_mul, heabs, one_mul, neg_mul, abs_neg]; exact h1
    rw [abs_le] at h2 h3
    intro i
    fin_cases i
    · simp only [hb, pt_zero, Fin.zero_eta, Fin.isValue]
      constructor <;> linarith
    · simp only [hb, pt_one, Fin.mk_one, Fin.isValue]
      constructor <;> linarith
  have hdist_a : ∀ k k' : ℤ, dist (a k) (a k') ^ 2 =
      ((x k - x k') ^ 2 + (y k - y k') ^ 2) / 2 := by
    intro k k'
    simp only [ha]
    rw [dist_pt_sq]
    have : e ^ 2 = 1 := by rw [sq]; exact he2
    nlinarith [this]
  have hdist_b : ∀ j j' : ℤ, dist (b j) (b j') ^ 2 =
      ((μ * g j - μ * g j') ^ 2 + (μ * Y j - μ * Y j') ^ 2) / 8 := by
    intro j j'
    simp only [hb]
    rw [dist_pt_sq]
    have : e ^ 2 = 1 := by rw [sq]; exact he2
    nlinarith [this]
  have hsepx : ∀ k ∈ Ks, ∀ k' ∈ Ks, k ≠ k' → ρ / s ≤ |x k - x k'| := by
    intro k hk k' hk' hne
    have e2 : x k - x k' = (ρ / s) * (k - k') := by simp only [hx]; ring
    rw [e2, abs_mul, abs_of_pos (by positivity : 0 < ρ / s)]
    have : (1 : ℝ) ≤ |((k - k' : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hne)
    push_cast at this
    nlinarith [div_pos hρ hs]
  have hmult_a : ∀ k ∈ Ks, (#(Ks.filter fun k' => dist (a k) (a k') ≤ 2 * δ) : ℝ) ≤ N₀ := by
    intro k hk
    set L := 4 * δ * s / ρ with hL
    have hsub : ∀ k' ∈ Ks.filter (fun k' => dist (a k) (a k') ≤ 2 * δ),
        (k : ℝ) - L ≤ (k' : ℝ) ∧ (k' : ℝ) ≤ (k : ℝ) - L + 2 * L := by
      intro k' hk'
      have hd := (Finset.mem_filter.mp hk').2
      have hsq := hdist_a k k'
      have hlow : |x k - x k'| / 2 ≤ dist (a k) (a k') := by
        have : (|x k - x k'| / 2) ^ 2 ≤ dist (a k) (a k') ^ 2 := by
          rw [hsq, div_pow, sq_abs]; nlinarith [sq_nonneg (y k - y k'), sq_nonneg (x k - x k')]
        exact (pow_le_pow_iff_left₀ (by positivity) dist_nonneg (by norm_num)).mp this
      have e2 : x k - x k' = (ρ / s) * (k - k') := by simp only [hx]; ring
      rw [e2, abs_mul, abs_of_pos (by positivity : 0 < ρ / s)] at hlow
      have h4 : (ρ / s) * |(k : ℝ) - k'| ≤ 4 * δ := by linarith
      have h5 : |(k : ℝ) - k'| ≤ L := by
        calc |(k : ℝ) - k'| = (ρ / s * |(k : ℝ) - k'|) * (s / ρ) := by field_simp
          _ ≤ (4 * δ) * (s / ρ) := by gcongr
          _ = L := by rw [hL]; ring
      obtain ⟨h5l, h5r⟩ := abs_le.mp h5
      exact ⟨by linarith, by linarith⟩
    have hL0 : 0 ≤ L := by positivity
    have := card_le_of_subset_Icc_int (by positivity) _ hsub
    have e8 : 2 * L = 8 * δ * (M * ρ) / ρ := by rw [hL, hsdef]; ring
    calc (#(Ks.filter fun k' => dist (a k) (a k') ≤ 2 * δ) : ℝ) ≤ 2 * L + 1 := this
      _ ≤ N₀ := by rw [e8]; exact hN₀a
  have hmult_b : ∀ j ∈ R, (#(R.filter fun j' => dist (b j) (b j') ≤ 2 * δ) : ℝ) ≤ N₀ := by
    intro j hj
    have hμ0 : 0 < μ := by positivity
    set L := 6 * δ / (μ * s) with hL
    have hsub : ∀ j' ∈ R.filter (fun j' => dist (b j) (b j') ≤ 2 * δ),
        (j : ℝ) - L ≤ (j' : ℝ) ∧ (j' : ℝ) ≤ (j : ℝ) - L + 2 * L := by
      intro j' hj'
      have hd := (Finset.mem_filter.mp hj').2
      have hsq := hdist_b j j'
      have hlow : μ * |Y j - Y j'| / 3 ≤ dist (b j) (b j') := by
        have : (μ * |Y j - Y j'| / 3) ^ 2 ≤ dist (b j) (b j') ^ 2 := by
          rw [hsq]
          have : (μ * |Y j - Y j'|) ^ 2 = (μ * Y j - μ * Y j') ^ 2 := by
            rw [mul_pow, sq_abs, ← mul_pow, mul_sub]
          nlinarith [sq_nonneg (μ * g j - μ * g j'), sq_nonneg (μ * Y j - μ * Y j')]
        exact (pow_le_pow_iff_left₀ (by positivity) dist_nonneg (by norm_num)).mp this
      rw [hT.Y_lin j j', abs_mul, abs_of_pos hs] at hlow
      have h4 : μ * (s * |(j : ℝ) - j'|) ≤ 6 * δ := by linarith
      have h5 : |(j : ℝ) - j'| ≤ L := by
        calc |(j : ℝ) - j'| = (μ * (s * |(j : ℝ) - j'|)) / (μ * s) := by field_simp
          _ ≤ (6 * δ) / (μ * s) := by gcongr
          _ = L := by rw [hL]
      obtain ⟨h5l, h5r⟩ := abs_le.mp h5
      exact ⟨by linarith, by linarith⟩
    have hL0 : 0 ≤ L := by positivity
    have := card_le_of_subset_Icc_int (by positivity) _ hsub
    have e12 : 2 * L = 12 * δ / (κ / 8 * (M * ρ)) := by rw [hL, hμ, hsdef]; ring
    calc (#(R.filter fun j' => dist (b j) (b j') ≤ 2 * δ) : ℝ) ≤ 2 * L + 1 := this
      _ ≤ N₀ := by rw [e12]; exact hN₀b
  -- AD of `a '' Ks`
  have hAD_a : ADset δ 1 (δ ^ (-η)) (a '' Ks) := by
    have h := adset_of_biLipschitz (X := a '' Ks) (u := fun p => e * (p 0 + p 1)) (L1 := 2)
      (L2 := 1) hδ (by norm_num) (by norm_num) ?_ ?_
    · exact h.mono_constant (by norm_num at h ⊢; linarith) hδ
    · rintro _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩
      have hu : ∀ m : ℤ, e * (a m 0 + a m 1) = x m := by
        intro m; simp only [ha, pt_zero, pt_one]
        have : e * (e * x m) = x m := by rw [← mul_assoc, he2, one_mul]
        linarith [this]
      simp only [hu]
      have hsq := hdist_a k k'
      have : (x k - x k') ^ 2 ≤ (2 * dist (a k) (a k')) ^ 2 := by
        rw [mul_pow, hsq]; nlinarith [sq_nonneg (y k - y k')]
      have h0 : 0 ≤ 2 * dist (a k) (a k') := by positivity
      rw [← sq_abs (x k - x k')] at this
      exact (pow_le_pow_iff_left₀ (abs_nonneg _) h0 (by norm_num)).mp this
    · rintro _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩
      have hu : ∀ m : ℤ, e * (a m 0 + a m 1) = x m := by
        intro m; simp only [ha, pt_zero, pt_one]
        have : e * (e * x m) = x m := by rw [← mul_assoc, he2, one_mul]
        linarith [this]
      simp only [hu, one_mul]
      have hsq := hdist_a k k'
      have hl := hylip k hk k' hk'
      have : dist (a k) (a k') ^ 2 ≤ |x k - x k'| ^ 2 := by
        rw [hsq, sq_abs]
        have : (y k - y k') ^ 2 ≤ (x k - x k') ^ 2 := by
          rw [← sq_abs (y k - y k'), ← sq_abs (x k - x k')]
          exact pow_le_pow_left₀ (abs_nonneg _) hl 2
        linarith
      exact (pow_le_pow_iff_left₀ dist_nonneg (abs_nonneg _) (by norm_num)).mp this
  -- AD of `b '' R`
  have hAD_b : ADset δ 1 (δ ^ (-η)) (b '' R) := by
    have hL2 : 0 < 1401 / κ ^ 2 := by positivity
    have h := adset_of_biLipschitz (X := b '' R) (u := fun p => p 0 - p 1) (L1 := 2)
      (L2 := 1401 / κ ^ 2) hδ (by norm_num) hL2 ?_ ?_
    · apply h.mono_constant _ hδ
      have hinv : 1 ≤ 1 / κ ^ 2 := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      have e1 : 4 * 2 * (1401 / κ ^ 2) + 3 = 11208 * (1 / κ ^ 2) + 3 := by ring
      have e2 : 12000 / κ ^ 2 = 12000 * (1 / κ ^ 2) := by ring
      have hn5 := n5
      rw [e2] at hn5
      rw [e1]
      linarith
    · rintro _ ⟨j, hj, rfl⟩ _ ⟨j', hj', rfl⟩
      have hu : ∀ m : ℤ, b m 0 - b m 1 = μ * Y m / 2 := by
        intro m; simp only [hb, pt_zero, pt_one]; ring
      simp only [hu]
      have hsq := hdist_b j j'
      have : |μ * Y j / 2 - μ * Y j' / 2| ^ 2 ≤ (2 * dist (b j) (b j')) ^ 2 := by
        rw [sq_abs, mul_pow, hsq]; nlinarith [sq_nonneg (μ * g j - μ * g j')]
      exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) (by norm_num)).mp this
    · rintro _ ⟨j, hj, rfl⟩ _ ⟨j', hj', rfl⟩
      have hu : ∀ m : ℤ, b m 0 - b m 1 = μ * Y m / 2 := by
        intro m; simp only [hb, pt_zero, pt_one]; ring
      simp only [hu]
      have hsq := hdist_b j j'
      have hgl := hT.g_lip j hj j' hj'
      have hμ0 : 0 < μ := by positivity
      -- `|μ g j - μ g j'| ≤ (1400/κ²) |μ Y j - μ Y j'|`
      have hg' : |μ * g j - μ * g j'| ≤ 1400 / κ ^ 2 * |μ * Y j - μ * Y j'| := by
        rw [← mul_sub, ← mul_sub, abs_mul, abs_mul, abs_of_pos hμ0]
        calc μ * |g j - g j'| ≤ μ * (1400 / κ ^ 2 * |Y j - Y j'|) := by gcongr
          _ = 1400 / κ ^ 2 * (μ * |Y j - Y j'|) := by ring
      have hκ2 : 1 ≤ 1 / κ ^ 2 := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      set A1 := |μ * Y j - μ * Y j'|
      set A0 := |μ * g j - μ * g j'|
      have hd2 : dist (b j) (b j') ^ 2 ≤ ((1401 / κ ^ 2) * (A1 / 2)) ^ 2 := by
        rw [hsq, ← sq_abs (μ * g j - μ * g j'), ← sq_abs (μ * Y j - μ * Y j')]
        have hA0 : A0 ≤ 1400 / κ ^ 2 * A1 := hg'
        have hA0' : 0 ≤ A0 := abs_nonneg _
        have hA1' : 0 ≤ A1 := abs_nonneg _
        have hsq0 : A0 ^ 2 ≤ (1400 / κ ^ 2 * A1) ^ 2 := pow_le_pow_left₀ hA0' hA0 2
        have hc : (1400 / κ ^ 2) ^ 2 + 1 ≤ 2 * (1401 / κ ^ 2) ^ 2 := by
          have e1 : (1400 / κ ^ 2) = 1400 * (1 / κ ^ 2) := by ring
          have e2 : (1401 / κ ^ 2) = 1401 * (1 / κ ^ 2) := by ring
          rw [e1, e2]; nlinarith
        have hA1sq : 0 ≤ A1 ^ 2 := sq_nonneg A1
        calc (A0 ^ 2 + A1 ^ 2) / 8 ≤ ((1400 / κ ^ 2 * A1) ^ 2 + A1 ^ 2) / 8 := by linarith
          _ = ((1400 / κ ^ 2) ^ 2 + 1) * A1 ^ 2 / 8 := by ring
          _ ≤ (2 * (1401 / κ ^ 2) ^ 2) * A1 ^ 2 / 8 := by gcongr
          _ = ((1401 / κ ^ 2) * (A1 / 2)) ^ 2 := by ring
      have : |μ * Y j / 2 - μ * Y j' / 2| = A1 / 2 := by
        simp only [A1]
        rw [show μ * Y j / 2 - μ * Y j' / 2 = (μ * Y j - μ * Y j') / 2 by ring, abs_div]
        norm_num
      rw [this]
      exact (pow_le_pow_iff_left₀ dist_nonneg (by positivity) (by norm_num)).mp hd2
  -- the triples
  have hTsub : Te ⊆ Ks ×ˢ R ×ˢ R := by
    intro t ht
    obtain ⟨-, h1, h2⟩ := hT.T_mem t (hTeT ht)
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ ht, Finset.mem_product.mpr ⟨h1, h2⟩⟩
  have hTecard' : N₀ ^ 3 * δ ^ (η - 3) ≤ #Te := by linarith
  have hDass : Assouad δ (1 - σ) (δ ^ (-η)) D := by
    apply assouad_dotSet hρ (by linarith) (by linarith) hK hA (by positivity) _ (by linarith) hδ
    simp only [hlam, hμ, hsdef]
    calc κ / 8 / (4 * (M * ρ)) * (4 * ρ) = κ / 8 * ρ / (M * ρ) := by field_simp
      _ ≤ δ := n7
  have hdot : ∀ t ∈ Te, ⟪a t.1, b t.2.1 - b t.2.2⟫ ∈ D := by
    intro t ht
    obtain ⟨v, hv, hvt⟩ := hT.dot_mem t (hTeT ht)
    refine ⟨_, ⟨v, hv, hvt⟩, ?_⟩
    have he2' : e ^ 2 = 1 := by rw [sq]; exact he2
    have key : ∀ X Y' Δ0 Δ1 : ℝ, ((e * X + Y') / 2) * ((e * Δ0 + Δ1) / 4) +
        ((e * X - Y') / 2) * ((e * Δ0 - Δ1) / 4) = (X * Δ0 + Y' * Δ1) / 4 := by
      intro X Y' Δ0 Δ1
      linear_combination (X * Δ0 / 4) * he2'
    have hbsub : b t.2.1 - b t.2.2 = pt ((e * (-μ * (g t.2.1 - g t.2.2)) + μ * (Y t.2.1 - Y t.2.2)) / 4)
        ((e * (-μ * (g t.2.1 - g t.2.2)) - μ * (Y t.2.1 - Y t.2.2)) / 4) := by
      simp only [hb, pt_sub]; congr 1 <;> ring
    rw [hbsub]
    simp only [ha]
    rw [inner_pt, key]
    simp only [hx, hy, hlam]
    field_simp
    ring
  -- apply the dichotomy
  obtain ⟨p, d, hd, hcount⟩ := hLD Ks R a b Te D hsq_a hsq_b N₀ (by nlinarith [div_nonneg (show 0 ≤ 8 * δ * (M * ρ) by positivity) hρ.le]) hmult_a hmult_b hAD_a hAD_b hTsub
    hTecard' hDass hdot
  set S := Ks.filter fun k => a k ∈ thickening δ (lineThrough p d) with hS
  -- back to the coordinates `(x, y)`
  set P0 := e * (p 0 + p 1)
  set P1 := p 0 - p 1
  set d0 := e * (d 0 + d 1)
  set d1 := d 0 - d 1
  have hnear : ∀ k ∈ S, ∃ t : ℝ, |x k - (P0 + t * d0)| < 2 * δ ∧ |y k - (P1 + t * d1)| < 2 * δ := by
    intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    obtain ⟨q, ⟨t, rfl⟩, hq⟩ := Metric.mem_thickening_iff.mp hk'
    refine ⟨t, ?_, ?_⟩
    · have h0 := abs_apply_le_norm2 (a k - (p + t • d)) 0
      have h1 := abs_apply_le_norm2 (a k - (p + t • d)) 1
      rw [← dist_eq_norm] at h0 h1
      have hxk : x k = e * (a k 0 + a k 1) := by
        simp only [ha, pt_zero, pt_one]
        have : e * (e * x k) = x k := by rw [← mul_assoc, he2, one_mul]
        linarith [this]
      have e1 : x k - (P0 + t * d0) = e * ((a k - (p + t • d)) 0 + (a k - (p + t • d)) 1) := by
        rw [hxk]; simp only [P0, d0, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        ring
      rw [e1, abs_mul, heabs, one_mul]
      calc |(a k - (p + t • d)) 0 + (a k - (p + t • d)) 1|
          ≤ |(a k - (p + t • d)) 0| + |(a k - (p + t • d)) 1| := abs_add_le _ _
        _ < δ + δ := add_lt_add (lt_of_le_of_lt h0 hq) (lt_of_le_of_lt h1 hq)
        _ = 2 * δ := by ring
    · have h0 := abs_apply_le_norm2 (a k - (p + t • d)) 0
      have h1 := abs_apply_le_norm2 (a k - (p + t • d)) 1
      rw [← dist_eq_norm] at h0 h1
      have hyk : y k = a k 0 - a k 1 := by
        simp only [ha, pt_zero, pt_one]; ring
      have e1 : y k - (P1 + t * d1) = (a k - (p + t • d)) 0 - (a k - (p + t • d)) 1 := by
        rw [hyk]; simp only [P1, d1, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        ring
      rw [e1]
      calc |(a k - (p + t • d)) 0 - (a k - (p + t • d)) 1|
          ≤ |(a k - (p + t • d)) 0| + |(a k - (p + t • d)) 1| := abs_sub _ _
        _ < δ + δ := add_lt_add (lt_of_le_of_lt h0 hq) (lt_of_le_of_lt h1 hq)
        _ = 2 * δ := by ring
  have hdd : d0 ≠ 0 ∨ d1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h0, h1⟩ := hcon
    apply hd
    have hs0 : d 0 + d 1 = 0 := by
      have : e * (d 0 + d 1) = 0 := h0
      rcases he with rfl | rfl <;> linarith
    have hs1 : d 0 - d 1 = 0 := h1
    ext i; fin_cases i
    · simp; linarith
    · simp; linarith
  have hS1 : 1 < #S := by
    have : (1 : ℝ) < δ ^ (ε - 1) := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hδ hδ1 (by linarith)
    exact_mod_cast lt_of_lt_of_le this hcount
  have hδsep : 12 * δ ≤ ρ / s := by
    rw [le_div_iff₀ hs]; nlinarith
  obtain ⟨hd0, hm, hlin⟩ := line_analysis (S := S) (x := x) (y := y)
    (fun k hk k' hk' hne => hsepx k (Finset.mem_filter.mp hk).1 k' (Finset.mem_filter.mp hk').1 hne)
    (fun k hk k' hk' => hylip k (Finset.mem_filter.mp hk).1 k' (Finset.mem_filter.mp hk').1)
    hnear hdd hδsep hS1
  refine ⟨f (ρ * k0) + s * P1 - d1 / d0 * (ρ * k0) - s * (d1 / d0) * P0, d1 / d0, hm, S,
    (Finset.filter_subset _ _).trans (Finset.image_subset_image hTeT), hcount, ?_⟩
  intro k hk
  have h1 := hlin k hk
  have e1 : f (ρ * k) - (f (ρ * k0) + s * P1 - d1 / d0 * (ρ * k0) - s * (d1 / d0) * P0 +
      d1 / d0 * (ρ * k)) = s * (y k - (P1 + d1 / d0 * (x k - P0))) := by
    simp only [hx, hy]; field_simp; ring
  rw [e1, abs_mul, abs_of_pos hs]
  calc s * |y k - (P1 + d1 / d0 * (x k - P0))| ≤ s * (6 * δ) := by gcongr
    _ ≤ ρ / 8 := by nlinarith

end

end WangZahlLot.Obl.wz_slab_local_linearity.CellProofs
