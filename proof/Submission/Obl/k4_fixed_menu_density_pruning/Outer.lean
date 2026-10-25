-- `finite_common_power_tail`, `gain_menu_index_lt`, `prob_fixed_depth_upper_tails` and the
-- shape of `statement_of_sampleClean` are adapted from this LOT tree, o194, session x0672,
-- commit 69d09a7b, Submission/Obl/k4_greedy_cover_graph_atlas/FiniteTails.lean,
-- FixedDepths.lean and Outer.lean (there adapted from o173, session x0598, commit
-- 6ded8016fe11, Submission/Obl/k4_quadratic_cover_to_analytical_atlas/FiniteTails.lean and
-- FixedDepths.lean).

import Submission.Obl.k4_fixed_menu_density_pruning.SampleClean

/-!
# The outer layer of o209

`statement_of_sampleClean : SampleClean → Statement`. The finite menu of fixed depths (the
candidate depths `menuDepth L (s i) (gain + z ρ gain) δ₀` for `i < m`, `z < Z`, the old depths
`menuDepth L (s i) 0 δ₀` for `i < m`, and the terminal depth `L`) is fixed before the sample;
the problem's pure-density tails on it have a common decay power `c₀`. We take
`ε₀ = min 1 (c₀ / 2)`, `σ₀ = 1` and a late-sample cutoff past which `48 ≤ N ^ (c₀ / 2)` and
all menu tails are at most `N ^ (-c₀)`. At a sample, the greedy cover's `i` and `h` pick three
menu entries, whose tails are then at most `N ^ (-ε) / 48`, and `SampleClean` applies.
-/

namespace Submission.Obl.k4_fixed_menu_density_pruning

open MeasureTheory Filter Set

/-- Finitely many fixed menu depths have one common positive power-decay exponent and one
common late-sample cutoff. -/
theorem finite_common_power_tail {ι : Type*} [Fintype ι]
    (N : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (err : ι → ℕ → ENNReal)
    (h : ∀ i, ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, err i k ≤ ENNReal.ofReal (N k ^ (-c))) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, ∀ i, err i k ≤ ENNReal.ofReal (N k ^ (-c)) := by
  classical
  choose c hc ht using h
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
    exact ⟨1, by norm_num, Filter.Eventually.of_forall fun _ i => isEmptyElim i⟩
  | inr hnonempty =>
    obtain ⟨i, _, hmin⟩ := (Finset.univ : Finset ι).exists_min_image c Finset.univ_nonempty
    refine ⟨c i, hc i, ?_⟩
    filter_upwards [Filter.eventually_all.mpr ht] with k hk j
    exact (hk j).trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le (hN k) (neg_le_neg (hmin j (Finset.mem_univ j)))))

theorem menuDepth_mem {L s h δ₀ : ℝ} (hL : 0 ≤ L) : menuDepth L s h δ₀ ∈ Icc 0 L :=
  ⟨le_min hL (le_max_left _ _), min_le_left _ _⟩

/-- The frozen gain menu has a fixed finite range independent of the sample. -/
theorem gain_menu_index_lt {gain step : ℝ} {z : ℕ}
    (hgain : 0 ≤ gain) (hstep : 0 < step)
    (hgainmax : gain + (z : ℝ) * step ≤ 1 / 8) :
    z < ⌈(1 / 8 : ℝ) / step⌉₊ + 1 := by
  have hz : (z : ℝ) ≤ (1 / 8 : ℝ) / step := (le_div_iff₀ hstep).mpr (by linarith)
  have hzceil := hz.trans (Nat.le_ceil ((1 / 8 : ℝ) / step))
  exact Nat.lt_succ_of_le (by exact_mod_cast hzceil)

/-- The frozen problem's upper pure-density tails have a common positive decay power at
every entry of any fixed finite depth menu. -/
theorem prob_fixed_depth_upper_tails {ι : Type*} [Fintype ι]
    {N K : ℕ → ℝ} {L d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))}
    {E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ →
      ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}
    (hp : prob N K L d S η W ω ν E P B f g G)
    (q : ι → ℝ) (hq : ∀ i, q i ∈ Icc 0 L) {τ : ℝ} (hτ : 0 < τ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, ∀ i,
      upperTail (N k) (W k) (ω k) (ν k) (E k) (B k) f (g k) τ (q i) ≤
        ENNReal.ofReal (N k ^ (-c)) := by
  rcases hp with ⟨hN, _, _, _, _, _, _, _, _, _, _, _, htail, _⟩
  apply finite_common_power_tail N (fun k => le_trans (by norm_num) (hN k))
  intro i
  obtain ⟨c, hc, ht⟩ := htail (q i) τ (hq i).1 (hq i).2 hτ
  refine ⟨c, hc, ht.mono ?_⟩
  intro k hk
  refine le_trans ?_ hk
  unfold upperTail
  apply Finset.sum_le_sum
  intro w _
  exact mul_le_mul' le_rfl (measure_mono (fun _ hp => Or.inr hp))

theorem rpow_neg_le_div {N c ε K : ℝ} (hN : 1 ≤ N) (hεc : ε ≤ c / 2) (hK : 0 < K)
    (hNK : K ≤ N ^ (c / 2)) : N ^ (-c) ≤ N ^ (-ε) / K := by
  have hN0 : 0 < N := by linarith
  have e : N ^ (c / 2) * N ^ (-c) = N ^ (-(c / 2)) := by
    rw [← Real.rpow_add hN0]; ring_nf
  have h1 : N ^ (-(c / 2)) ≤ N ^ (-ε) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have h2 : K * N ^ (-c) ≤ N ^ (c / 2) * N ^ (-c) :=
    mul_le_mul_of_nonneg_right hNK (Real.rpow_nonneg hN0.le _)
  rw [e] at h2
  rw [le_div_iff₀ hK]
  linarith

/-- The finite menu of fixed depths: candidate depths, old depths and the terminal depth. -/
noncomputable def depthMenu (L : ℝ) (m : ℕ) (s : ℕ → ℝ) (gain ρ δ₀ : ℝ) (Z : ℕ) :
    (Fin m × Fin Z) ⊕ (Fin m ⊕ Unit) → ℝ
  | Sum.inl iz => menuDepth L (s iz.1) (gain + ((iz.2 : ℕ) : ℝ) * (ρ * gain)) δ₀
  | Sum.inr (Sum.inl i) => menuDepth L (s i) 0 δ₀
  | Sum.inr (Sum.inr _) => L

theorem depthMenu_mem {L : ℝ} (hL : 0 ≤ L) (m : ℕ) (s : ℕ → ℝ) (gain ρ δ₀ : ℝ) (Z : ℕ)
    (e : (Fin m × Fin Z) ⊕ (Fin m ⊕ Unit)) : depthMenu L m s gain ρ δ₀ Z e ∈ Icc 0 L := by
  rcases e with iz | i | u
  · exact menuDepth_mem hL
  · exact menuDepth_mem hL
  · exact ⟨hL, le_rfl⟩

/-- **The outer layer.** o209 follows from the per-sample cleaning statement. -/
theorem statement_of_sampleClean (hsc : SampleClean) : Statement := by
  intro d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hρ4 hdρ m s gain δ₀ hgrid hgain hgain1 hδ₀ hδρ
    N K L d W ω ν E P B f g G hprob Mp Dp Mg Dg τ hτ
  have hL : 0 < L := hprob.2.2.2.1
  have hN2 : ∀ k, 2 ≤ N k := hprob.1
  have hNt : Tendsto N atTop atTop := hprob.2.1
  obtain ⟨Mpr, Dpr, hpr⟩ := hprob.2.2.2.2.2.2.2.2.1
  have hglaw := hprob.2.2.2.2.2.2.2.2.2.1
  -- the common tail power on the finite menu
  set Z : ℕ := ⌈(1 / 8 : ℝ) / (ρ * gain)⌉₊ + 1 with hZ
  obtain ⟨c₀, hc₀, htails⟩ := prob_fixed_depth_upper_tails hprob
    (depthMenu L m s gain ρ δ₀ Z) (depthMenu_mem hL.le m s gain ρ δ₀ Z) hτ
  set ε₀ : ℝ := min 1 (c₀ / 2) with hε₀
  have hε₀pos : 0 < ε₀ := lt_min one_pos (by linarith)
  have hε₀1 : ε₀ ≤ 1 := min_le_left _ _
  have hε₀c : ε₀ ≤ c₀ / 2 := min_le_right _ _
  -- the late-sample cutoff
  have hev : ∀ᶠ k in atTop, (48 : ℝ) ≤ N k ^ (c₀ / 2) ∧ ∀ e,
      upperTail (N k) (W k) (ω k) (ν k) (E k) (B k) f (g k) τ (depthMenu L m s gain ρ δ₀ Z e) ≤
        ENNReal.ofReal (N k ^ (-c₀)) := by
    have h48 : ∀ᶠ k in atTop, (48 : ℝ) ≤ N k ^ (c₀ / 2) :=
      ((tendsto_rpow_atTop (by positivity)).comp hNt).eventually_ge_atTop 48
    exact h48.and htails
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hev
  refine ⟨ε₀, 1, hε₀pos, hε₀1, one_pos, le_rfl, k₀, ?_⟩
  intro k hk ε σ hε hεε₀ hσ hσ1 r T nw κ C lev par γ j c u Q R A F lst hpath hcover
  obtain ⟨h48, htk⟩ := hk₀ k hk
  obtain ⟨i, h, n, old, R', A', V, hbody⟩ :=
    (greedyCover_iff_gcBody _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mp hcover
  have hNk1 : 1 ≤ N k := by linarith [hN2 k]
  have hsmall : ENNReal.ofReal (N k ^ (-c₀)) ≤ ENNReal.ofReal (N k ^ (-ε) / 48) :=
    ENNReal.ofReal_le_ofReal (rpow_neg_le_div hNk1 (hεε₀.trans hε₀c) (by norm_num) h48)
  -- the menu entries of the sample
  have hi : i < m := hbody.1
  obtain ⟨z, hz⟩ := hbody.2.2.2.1
  have hzlt : z < Z := gain_menu_index_lt hgain.le (by positivity)
    (by rw [← hz]; exact hbody.2.2.1)
  have hcand := htk (Sum.inl (⟨i, hi⟩, ⟨z, hzlt⟩))
  have hold := htk (Sum.inr (Sum.inl ⟨i, hi⟩))
  have hterm := htk (Sum.inr (Sum.inr ()))
  have hqc : depthMenu L m s gain ρ δ₀ Z (Sum.inl (⟨i, hi⟩, ⟨z, hzlt⟩)) =
      menuDepth L (s i) h δ₀ := by
    show menuDepth L (s i) (gain + (z : ℝ) * (ρ * gain)) δ₀ = _
    rw [← hz]
  rw [hqc] at hcand
  have hsd := hpr k
  exact hsc (N k) L (W k) (ω k) (ν k) (E k) (B k) f (g k) d₁ κ₁ ρ gain δ₀ τ ε σ m s Mp Dp Mg Dg
    r T nw κ C lev par γ j c u Q R A F lst i h n old R' A' V (hN2 k) hL hd₁ hd₁1 hρ hρ4 hgain
    hgain1 hδ₀ hδρ hτ hε hsd.2.1 hsd.2.2.1
    (fun w => ⟨(hsd.2.2.2.1 w).1, (hsd.2.2.2.1 w).2.1, (hsd.2.2.2.1 w).2.2.2.2.2.2.2.1,
      (hsd.2.2.2.1 w).2.2.2.2.2.2.2.2.1⟩)
    (fun w q hq0 hqL => hglaw k w q hq0 hqL) hpath hbody
    (hcand.trans hsmall) (hold.trans hsmall) (hterm.trans hsmall)

end Submission.Obl.k4_fixed_menu_density_pruning
