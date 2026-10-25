-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_polynomial_grains_partition.Grains.Main.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_polynomial_grains_partition.Grains.Select
import Submission.WZ.ChallengeDeps
/-!
# The grains decomposition in the frozen form of o176

`D = 2^p` with `20 ≤ D^(ε/8)`; levels `t ≤ T`, `T` the first level whose cubes have side
`≤ 50 D δ`, so `20^T ≤ δ^(-ε/8)`. Pigeonhole a level: either the leaves of a level `t < T`
or the nodes of level `T` (which lie in the `100δ`-thickening of their grid planes) carry a
`1/(T+1)` share of `E`; select a dyadic class there (`SelectAux.select`) and conclude with
`SelectAux.finish`, `K = 2000 (3p+2) 2^p`.
-/

namespace WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod
namespace Grains

open MeasureTheory

namespace MainAux

theorem exists_p {ε : ℝ} (hε : 0 < ε) : ∃ p : ℕ, 1 ≤ p ∧ (20 : ℝ) ≤ ((2 : ℝ) ^ p) ^ ε := by
  refine ⟨⌈5 / ε⌉₊ + 1, by omega, ?_⟩
  have h1 : ((5 : ℕ) : ℝ) ≤ ((⌈5 / ε⌉₊ + 1 : ℕ) : ℝ) * ε := by
    have h2 := Nat.le_ceil (5 / ε)
    have h3 : 5 / ε * ε = 5 := by field_simp
    push_cast
    nlinarith
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  calc (20 : ℝ) ≤ 2 ^ ((5 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1

theorem pow_le_rpow_neg {ε δ D : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hD : 1 ≤ D) (h20 : 20 ≤ D ^ ε)
    (T : ℕ) (hT : D ^ T ≤ 1 / δ) : (20 : ℝ) ^ T ≤ δ ^ (-ε) := by
  calc (20 : ℝ) ^ T ≤ (D ^ ε) ^ T := pow_le_pow_left₀ (by norm_num) h20 T
    _ = (D ^ T) ^ ε := Real.rpow_pow_comm (by linarith) ε T
    _ ≤ (1 / δ) ^ ε := Real.rpow_le_rpow (by positivity) hT hε.le
    _ = δ ^ (-ε) := by rw [Real.rpow_neg hδ.le, one_div, Real.inv_rpow hδ.le]

/-- Pigeonholing a level. -/
theorem level_pigeon (T : ℕ) (f : ℕ → ENNReal) :
    ∃ t ∈ Finset.range (T + 1),
      ∑ t' ∈ Finset.range (T + 1), f t' ≤ ((T + 1 : ℕ) : ENNReal) * f t := by
  by_contra h
  push Not at h
  have := ENNReal.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.2 (Nat.succ_pos T)⟩ h
  rw [Finset.sum_const, Finset.card_range, ← Finset.mul_sum, nsmul_eq_mul] at this
  exact lt_irrefl _ this

theorem succ_le_two_pow (T : ℕ) : ((T : ℝ) + 1) ≤ 2 ^ T := by
  have : T + 1 ≤ 2 ^ T := Nat.lt_two_pow_self
  exact_mod_cast this

/-- `k₀ N ≤ (3p+2) 20^T` for `k₀ = 3T + 3p + 2`, `N = T + 1`. -/
theorem k0N_le (p T : ℕ) (hp : 1 ≤ p) :
    ((3 * T + 3 * p + 2 : ℕ) : ℝ) * ((T + 1 : ℕ) : ℝ) ≤ (3 * p + 2) * 20 ^ T := by
  have h1 := succ_le_two_pow T
  have h2 : ((3 * T + 3 * p + 2 : ℕ) : ℝ) ≤ (3 * p + 2) * ((T : ℝ) + 1) := by
    have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have h0 : (0 : ℝ) ≤ (T : ℝ) * (3 * p - 1) := mul_nonneg (by positivity) (by linarith)
    push_cast
    nlinarith
  have h3 : ((T : ℝ) + 1) * ((T : ℝ) + 1) ≤ 20 ^ T := by
    calc ((T : ℝ) + 1) * ((T : ℝ) + 1) ≤ 2 ^ T * 2 ^ T := by
          have : (0 : ℝ) ≤ T + 1 := by positivity
          exact mul_le_mul h1 h1 this (by positivity)
      _ = 4 ^ T := by rw [← mul_pow]; norm_num
      _ ≤ 20 ^ T := pow_le_pow_left₀ (by norm_num) (by norm_num) T
  push_cast
  calc ((3 * (T : ℝ) + 3 * p + 2)) * ((T : ℝ) + 1)
      ≤ ((3 * p + 2) * ((T : ℝ) + 1)) * ((T : ℝ) + 1) := by
        have := h2; push_cast at this
        exact mul_le_mul_of_nonneg_right this (by positivity)
    _ = (3 * p + 2) * (((T : ℝ) + 1) * ((T : ℝ) + 1)) := by ring
    _ ≤ (3 * p + 2) * 20 ^ T := by gcongr

/-- `2^k₀` dominates the dyadic range: `2 · 4^t · 8^p · (T+1) ≤ 2^(3T+3p+2)` for `t ≤ T`. -/
theorem two_pow_k0 (p t T : ℕ) (ht : t ≤ T) :
    2 * (4 : ℝ) ^ t * 8 ^ p * ((T + 1 : ℕ) : ℝ) ≤ 2 ^ (3 * T + 3 * p + 2) := by
  have h1 := succ_le_two_pow T
  have h2 : (4 : ℝ) ^ t ≤ 4 ^ T := pow_le_pow_right₀ (by norm_num) ht
  have e : (2 : ℝ) ^ (3 * T + 3 * p + 2) = 4 * (4 ^ T * 2 ^ T) * 8 ^ p := by
    rw [pow_add, pow_add, pow_mul, pow_mul, show (2 : ℝ) ^ 3 = 8 by norm_num,
      show (8 : ℝ) ^ T = 4 ^ T * 2 ^ T by rw [← mul_pow]; norm_num]
    ring
  rw [e]
  push_cast
  have : (0 : ℝ) ≤ 8 ^ p := by positivity
  have h3 : (4 : ℝ) ^ t * ((T : ℝ) + 1) ≤ 4 ^ T * 2 ^ T :=
    mul_le_mul h2 h1 (by positivity) (by positivity)
  have h4 := mul_le_mul_of_nonneg_right h3 this
  have h5 : (0 : ℝ) ≤ 4 ^ T * 2 ^ T * 8 ^ p := by positivity
  nlinarith

end MainAux

set_option maxHeartbeats 1000000 in
open MainAux SplitAux StepAux RecAux SelectAux in
theorem grains_frozen : ∀ε:ℝ,0<ε→∃K:ℝ,1≤K∧∀δ:ℝ,0<δ→δ≤1→∀E:Set LeanEval.Analysis.WangZahlKakeya.Space,MeasurableSet E→ E⊆Metric.ball (0:LeanEval.Analysis.WangZahlKakeya.Space) 1→∃(L:ℕ)(Q:Fin L→ MvPolynomial (Fin 3) ℝ)(z:Fin L→ LeanEval.Analysis.WangZahlKakeya.Space)(G:Fin L→ Set LeanEval.Analysis.WangZahlKakeya.Space),(∀j,Q j≠0∧((Q j).totalDegree:ℝ)≤K∧MeasurableSet (G j)∧G j⊆E∧G j⊆Metric.thickening (100*δ) {p:LeanEval.Analysis.WangZahlKakeya.Space|MvPolynomial.eval (fun i=>p i) (Q j)=0}∧G j⊆Metric.closedBall (z j) (K*δ^(-ε)*(L:ℝ)^(-(1/3:ℝ))))∧(∀j j',j≠j'→ Disjoint (G j) (G j'))∧ENNReal.ofReal (K⁻¹*δ^ε)*MeasureTheory.volume E≤∑j,MeasureTheory.volume (G j)∧(∀j,ENNReal.ofReal (K⁻¹*δ^ε/L)*MeasureTheory.volume E≤MeasureTheory.volume (G j)∧MeasureTheory.volume (G j)≤ENNReal.ofReal (K*δ^(-ε)/L)*MeasureTheory.volume E)∧∀p u:LeanEval.Analysis.WangZahlKakeya.Space,‖u‖=1→(({j|(Metric.thickening δ (segment ℝ p (p+u))∩G j).Nonempty}.ncard:ℝ)≤K*δ^(-ε)*(L:ℝ)^(1/3:ℝ)) := by
  classical
  intro ε hε
  have hε8 : 0 < ε / 8 := by positivity
  obtain ⟨p, hp1, h20⟩ := exists_p hε8
  set D : ℝ := (2 : ℝ) ^ p with hDdef
  have hD1 : (1 : ℝ) ≤ D := one_le_pow₀ (by norm_num)
  have hD0 : (0 : ℝ) < D := by positivity
  have h83 : (8 : ℝ) ^ p = D ^ 3 := by
    rw [hDdef, ← pow_mul, mul_comm p 3, pow_mul]; norm_num
  set K : ℝ := 2000 * (3 * p + 2) * D with hKdef
  have hp3 : (5 : ℝ) ≤ 3 * p + 2 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp1
    linarith
  have hK1 : (10000 : ℝ) ≤ K := by
    rw [hKdef]
    have : (10000 : ℝ) * 1 ≤ 2000 * (3 * p + 2) * D := by
      have h1 : (10000 : ℝ) ≤ 2000 * (3 * p + 2) := by linarith
      exact mul_le_mul h1 hD1 (by norm_num) (by positivity)
    linarith
  have hKpos : 0 < K := by linarith
  refine ⟨K, by linarith, ?_⟩
  intro δ hδ hδ1 E hE hEball
  have hEfin : volume E ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ball_lt_top (x := (0 : Space)) (r := 1)).ne
      (measure_mono hEball)
  -- the null case
  by_cases hE0 : volume E = 0
  · refine ⟨0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0,
      fun j => j.elim0, by simp [hE0], fun j => j.elim0, ?_⟩
    intro x u _
    have : {j : Fin 0 | (Metric.thickening δ (segment ℝ x (x + u)) ∩
        (fun j : Fin 0 => j.elim0 : Fin 0 → Set Space) j).Nonempty}.ncard = 0 := by
      rw [Set.ncard_eq_zero]
      ext j
      exact j.elim0
    rw [this, Nat.cast_zero, Real.zero_rpow (by norm_num), mul_zero]
  have H : Hyp p δ E := ⟨hp1, hδ, hE, hEball.trans ball_subset_box⟩
  -- the number `T` of levels
  have hex : ∃ t : ℕ, scale p t ≤ 50 * 2 ^ p * δ := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 / (50 * 2 ^ p * δ))
      (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (by omega : p ≠ 0))
    refine ⟨n, ?_⟩
    unfold scale
    rw [div_lt_iff₀ (by positivity)] at hn
    rw [div_le_iff₀ (by positivity)]
    linarith
  set T := Nat.find hex with hT_def
  have hT : scale p T ≤ 50 * 2 ^ p * δ := Nat.find_spec hex
  have hTmin : ∀ t < T, 50 * 2 ^ p * δ < scale p t := fun t ht =>
    not_le.1 (Nat.find_min hex ht)
  have hDT : ((2 : ℝ) ^ p) ^ T ≤ 1 / δ := by
    rcases Nat.eq_zero_or_pos T with h0 | hpos
    · rw [h0, pow_zero, le_div_iff₀ hδ]
      linarith
    · have h1 := hTmin (T - 1) (by omega)
      unfold scale at h1
      rw [lt_div_iff₀ (by positivity)] at h1
      have hDT' : ((2 : ℝ) ^ p) ^ T = 2 ^ p * ((2 : ℝ) ^ p) ^ (T - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [le_div_iff₀ hδ, hDT']
      have : (0 : ℝ) ≤ 2 ^ p * ((2 : ℝ) ^ p) ^ (T - 1) * δ := by positivity
      nlinarith
  set B : ℝ := δ ^ (-(ε / 8)) with hBdef
  have h20T : (20 : ℝ) ^ T ≤ B := pow_le_rpow_neg hε8 hδ hD1 h20 T hDT
  have hB1 : 1 ≤ B := le_trans (one_le_pow₀ (by norm_num)) h20T
  have hB8 : δ ^ (-ε) = B ^ 8 := by
    rw [hBdef, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    congr 1
    push_cast
    ring
  have hX : K * δ ^ (-ε) = K * B ^ 8 := by rw [hB8]
  have hδs : ∀ t < T, δ ≤ scale p (t + 1) := by
    intro t ht
    have h1 := hTmin t ht
    rw [scale_succ, le_div_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ 2 ^ p * δ := by positivity
    nlinarith
  -- pigeonholing a level
  have hmassT := mass_eq H T
  obtain ⟨t, ht, hft⟩ := level_pigeon T (fun t => if t < T then
    ∑ σ : Fin t → I p, ∑ q, volume (leaf p δ E t σ q)
    else ∑ σ : Fin T → I p, volume (node p δ E T σ).1)
  have hsumf : ∑ t' ∈ Finset.range (T + 1), (if t' < T then
      ∑ σ : Fin t' → I p, ∑ q, volume (leaf p δ E t' σ q)
      else ∑ σ : Fin T → I p, volume (node p δ E T σ).1) = volume E := by
    rw [Finset.sum_range_succ, ite_eq_right (lt_irrefl T),
      Finset.sum_congr rfl (fun t' ht' => ite_eq_left (Finset.mem_range.1 ht')), hmassT,
      add_comm]
  rw [hsumf] at hft
  have htT' : t ≤ T := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
  -- common numeric facts
  set e : ℝ := (volume E).toReal with he
  have he0 : 0 < e := ENNReal.toReal_pos hE0 hEfin
  set k₀ : ℕ := 3 * T + 3 * p + 2 with hk₀
  have hk1 : 1 ≤ k₀ := by omega
  have hN : 1 ≤ T + 1 := by omega
  have hk0N := k0N_le p T hp1
  have hmassK : 4 * (k₀ : ℝ) * ((T + 1 : ℕ) : ℝ) ≤ K * δ ^ (-ε) := by
    rw [hX]
    have h1 : (3 * p + 2) * (20 : ℝ) ^ T ≤ (3 * p + 2) * B :=
      mul_le_mul_of_nonneg_left h20T (by positivity)
    have h2 : B ≤ B ^ 8 := le_self_pow₀ hB1 (by norm_num)
    have h3 : 4 * ((3 * (p : ℝ) + 2) * B) ≤ K * B ^ 8 := by
      rw [hKdef]
      have : 4 * (3 * (p : ℝ) + 2) ≤ 2000 * (3 * p + 2) * D := by
        have : 4 * (3 * (p : ℝ) + 2) * 1 ≤ 2000 * (3 * p + 2) * D :=
          mul_le_mul (by linarith) hD1 (by norm_num) (by positivity)
        linarith
      calc 4 * ((3 * (p : ℝ) + 2) * B) = (4 * (3 * p + 2)) * B := by ring
        _ ≤ (2000 * (3 * p + 2) * D) * B ^ 8 :=
          mul_le_mul this h2 (by positivity) (by positivity)
    calc 4 * (k₀ : ℝ) * ((T + 1 : ℕ) : ℝ) = 4 * ((k₀ : ℝ) * ((T + 1 : ℕ) : ℝ)) := by ring
      _ ≤ 4 * ((3 * p + 2) * 20 ^ T) := by gcongr
      _ ≤ 4 * ((3 * p + 2) * B) := by gcongr
      _ ≤ K * B ^ 8 := h3
  have htwo : 2 ≤ K * δ ^ (-ε) := by
    rw [hX]
    have : (1 : ℝ) ≤ B ^ 8 := one_le_pow₀ hB1
    nlinarith
  have hXpos : 0 < K * δ ^ (-ε) := by positivity
  -- `2^t ≤ B`, `20^(3t) 2^t ≤ B^4`
  have h2t : ∀ s ≤ T, (2 : ℝ) ^ s ≤ B := fun s hs =>
    le_trans (pow_le_pow_left₀ (by norm_num) (by norm_num) s)
      (le_trans (pow_le_pow_right₀ (by norm_num) hs) h20T)
  have h20t : ∀ s ≤ T, (20 : ℝ) ^ s ≤ B := fun s hs =>
    le_trans (pow_le_pow_right₀ (by norm_num) hs) h20T
  have hdiamK : ∀ s ≤ T, 64 * (2 : ℝ) ^ s ≤ (K * δ ^ (-ε)) ^ 3 := by
    intro s hs
    rw [hX]
    have h1 := h2t s hs
    have h2 : B ≤ (B ^ 8) ^ 3 := by
      rw [← pow_mul]; exact le_self_pow₀ hB1 (by norm_num)
    have h3 : (64 : ℝ) ≤ K ^ 3 := by
      have : (4 : ℝ) ≤ K := by linarith
      have h4 := pow_le_pow_left₀ (by norm_num) this 3
      norm_num at h4
      linarith
    rw [mul_pow]
    calc 64 * (2 : ℝ) ^ s ≤ 64 * B := by gcongr
      _ ≤ K ^ 3 * (B ^ 8) ^ 3 := mul_le_mul h3 h2 (by positivity) (by positivity)
  by_cases htT : t < T
  · -- the leaves of level `t`
    rw [ite_eq_left htT] at hft
    have hδt : δ ≤ scale p (t + 1) := hδs t htT
    set M : ℝ := 2 ^ t * e / (D ^ 3) ^ t with hM
    have hMpos : 0 < M := by rw [hM]; positivity
    have hmax : ∀ y : (Fin t → I p) × Q p, volume (leaf p δ E t y.1 y.2) ≤ ENNReal.ofReal M := by
      intro y
      refine le_trans (measure_mono (leaf_props H t y.1 y.2).2.1) ?_
      have h1 := (node_props H t y.1).2.2.2
      have hfin : volume (node p δ E t y.1).1 ≠ ⊤ :=
        ne_top_of_le_ne_top hEfin (measure_mono (node_props H t y.1).2.2.1)
      rw [← ENNReal.ofReal_toReal hfin]
      apply ENNReal.ofReal_le_ofReal
      have h2 := ENNReal.toReal_mono (by
        exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) hEfin) h1
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
        ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ← he] at h2
      rw [hM, le_div_iff₀ (by positivity)]
      have : ((2 : ℝ) ^ p) ^ 3 = D ^ 3 := by rw [hDdef]
      rw [this] at h2
      linarith
    have hcount := leaf_count H t
    have htube : ∀ x v : Space, ‖v‖ ≤ 1 →
        ({y : (Fin t → I p) × Q p | (Metric.thickening δ (segment ℝ x (x + v)) ∩
          leaf p δ E t y.1 y.2).Nonempty}.ncard : ℝ) ≤ (20 * 2 ^ p) ^ t * (400 * 2 ^ p) :=
      fun x v hv => leaf_tube H x v hv t hδt
    have hk₀' : 2 * ((2 * 8 ^ p) ^ t * 8 ^ p) * M * ((T + 1 : ℕ) : ℝ) ≤ 2 ^ k₀ * e := by
      have e1 : 2 * ((2 * (8 : ℝ) ^ p) ^ t * 8 ^ p) * M * ((T + 1 : ℕ) : ℝ) =
          (2 * (4 : ℝ) ^ t * 8 ^ p * ((T + 1 : ℕ) : ℝ)) * e := by
        rw [hM, h83, mul_pow, show (4 : ℝ) ^ t = 2 ^ t * 2 ^ t by rw [← mul_pow]; norm_num]
        field_simp
      rw [e1]
      exact mul_le_mul_of_nonneg_right (two_pow_k0 p t T htT') he0.le
    obtain ⟨L, Q, z, G, m, hm, hLc, hLm, hEL, hmM, hG, hdisj, hmasses, hsum, htubeG⟩ :=
      select (ι := (Fin t → I p) × Q p)
        (fun y => leaf p δ E t y.1 y.2)
        (fun y => WithLp.toLp 2 (subc p (node p δ E t y.1).2 (scale p t) y.2))
        (fun y => leafPoly p δ E t y.1)
        (E := E) (δ := δ) (r := 2 * scale p (t + 1)) (M := M)
        (Nt := (20 * 2 ^ p) ^ t * (400 * 2 ^ p)) (Kd := 18 * 2 ^ p)
        (Nc := (2 * 8 ^ p) ^ t * 8 ^ p) (k₀ := k₀) (N := T + 1)
        (fun y => (leaf_props H t y.1 y.2).1)
        (fun y => (leaf_props H t y.1 y.2).2.1.trans (node_props H t y.1).2.2.1)
        (fun y => (leaf_props H t y.1 y.2).2.2.1.trans
          (box_subset_closedBall _ (scale_pos p (t + 1)).le))
        (fun y => by
          obtain ⟨-, -, -, h1, h2, h3⟩ := leaf_props H t y.1 y.2
          exact ⟨h1, by exact_mod_cast h2, h3⟩)
        (leaf_disj H t) hmax hcount htube hEfin hE0
        (by rw [Fintype.sum_prod_type]; exact hft) hk₀' hk1
    refine ⟨L, Q, z, G, finish Q z G hδ hKpos (by have := scale_pos p (t + 1); positivity)
      (Kd := 18 * 2 ^ p) (by rw [hKdef, hDdef]; nlinarith [hp3, hD1])
      ?_ hmassK htwo ?_ hk1 hN hEfin hE0 (by positivity) hm hLc hLm hEL hmM hG hdisj hmasses
      hsum htubeG⟩
    · -- diameter: `r^3 Nc = 64 · 2^t`
      have e1 : (2 * scale p (t + 1)) ^ 3 * ((2 * 8 ^ p) ^ t * 8 ^ p) = 64 * (2 : ℝ) ^ t := by
        unfold scale
        rw [h83, mul_pow, ← hDdef]
        field_simp
        ring
      rw [e1]
      exact hdiamK t htT'
    · -- tube: `Nt^3 · 4 k₀ N M ≤ X^3 e`
      have e1 : ((20 * 2 ^ p) ^ t * (400 * 2 ^ p)) ^ 3 * (4 * k₀ * ((T + 1 : ℕ) : ℝ) * M) =
          (20 : ℝ) ^ (3 * t) * 2 ^ t * (400 ^ 3 * D ^ 3) * (4 * k₀ * ((T + 1 : ℕ) : ℝ)) * e := by
        rw [hM, ← hDdef]
        field_simp
        ring
      rw [e1, hX]
      have h1 : (20 : ℝ) ^ (3 * t) * 2 ^ t ≤ B ^ 4 := by
        rw [pow_mul', show B ^ 4 = B ^ 3 * B by ring]
        exact mul_le_mul (pow_le_pow_left₀ (by positivity) (h20t t htT') 3) (h2t t htT')
          (by positivity) (by positivity)
      have h2 : 4 * (k₀ : ℝ) * ((T + 1 : ℕ) : ℝ) ≤ 4 * (3 * p + 2) * B := by
        have := hk0N
        have h3 : (3 * (p : ℝ) + 2) * 20 ^ T ≤ (3 * p + 2) * B :=
          mul_le_mul_of_nonneg_left h20T (by positivity)
        nlinarith
      have h4 : (400 : ℝ) ^ 3 * D ^ 3 * (4 * (3 * p + 2)) ≤ K ^ 3 := by
        have ha : (3 * (p : ℝ) + 2) ≤ (3 * p + 2) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
        have hD3 : (0 : ℝ) ≤ D ^ 3 := by positivity
        calc (400 : ℝ) ^ 3 * D ^ 3 * (4 * (3 * p + 2)) = 256000000 * ((3 * p + 2) * D ^ 3) := by
              ring
          _ ≤ 8000000000 * ((3 * p + 2) ^ 3 * D ^ 3) :=
              mul_le_mul (by norm_num) (mul_le_mul_of_nonneg_right ha hD3) (by positivity)
                (by norm_num)
          _ = K ^ 3 := by rw [hKdef]; ring
      have hB5 : B ^ 5 ≤ (B ^ 8) ^ 3 := by
        rw [← pow_mul]; exact pow_le_pow_right₀ hB1 (by norm_num)
      have hY : (0 : ℝ) ≤ 400 ^ 3 * D ^ 3 := by positivity
      have hZ : (0 : ℝ) ≤ 4 * (k₀ : ℝ) * ((T + 1 : ℕ) : ℝ) := by positivity
      calc (20 : ℝ) ^ (3 * t) * 2 ^ t * (400 ^ 3 * D ^ 3) * (4 * k₀ * ((T + 1 : ℕ) : ℝ)) * e
          ≤ B ^ 4 * (400 ^ 3 * D ^ 3) * (4 * (3 * p + 2) * B) * e :=
            mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_right h1 hY) h2 hZ
              (by positivity)) he0.le
        _ = ((400 : ℝ) ^ 3 * D ^ 3 * (4 * (3 * p + 2))) * B ^ 5 * e := by ring
        _ ≤ K ^ 3 * (B ^ 8) ^ 3 * e :=
            mul_le_mul_of_nonneg_right (mul_le_mul h4 hB5 (by positivity) (by positivity)) he0.le
        _ = (K * B ^ 8) ^ 3 * e := by ring
  · -- the nodes of the last level `T`
    rw [ite_eq_right htT] at hft
    have htT2 : t = T := le_antisymm htT' (not_lt.1 htT)
    set M : ℝ := 2 ^ T * e / (D ^ 3) ^ T with hM
    have hMpos : 0 < M := by rw [hM]; positivity
    have hmax : ∀ σ : Fin T → I p, volume (node p δ E T σ).1 ≤ ENNReal.ofReal M := by
      intro σ
      have h1 := (node_props H T σ).2.2.2
      have hfin : volume (node p δ E T σ).1 ≠ ⊤ :=
        ne_top_of_le_ne_top hEfin (measure_mono (node_props H T σ).2.2.1)
      rw [← ENNReal.ofReal_toReal hfin]
      apply ENNReal.ofReal_le_ofReal
      have h2 := ENNReal.toReal_mono (by
        exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) hEfin) h1
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
        ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ← he] at h2
      rw [hM, le_div_iff₀ (by positivity)]
      have : ((2 : ℝ) ^ p) ^ 3 = D ^ 3 := by rw [hDdef]
      rw [this] at h2
      linarith
    have hcount := node_count H T
    have htube : ∀ x v : Space, ‖v‖ ≤ 1 →
        ({σ : Fin T → I p | (Metric.thickening δ (segment ℝ x (x + v)) ∩
          (node p δ E T σ).1).Nonempty}.ncard : ℝ) ≤ (20 * 2 ^ p) ^ T :=
      fun x v hv => node_tube H x v hv T
    have hk₀' : 2 * (2 * 8 ^ p) ^ T * M * ((T + 1 : ℕ) : ℝ) ≤ 2 ^ k₀ * e := by
      have e1 : 2 * (2 * (8 : ℝ) ^ p) ^ T * M * ((T + 1 : ℕ) : ℝ) =
          (2 * (4 : ℝ) ^ T * ((T + 1 : ℕ) : ℝ)) * e := by
        rw [hM, h83, mul_pow, show (4 : ℝ) ^ T = 2 ^ T * 2 ^ T by rw [← mul_pow]; norm_num]
        field_simp
      rw [e1]
      have h1 := two_pow_k0 p T T le_rfl
      have h2 : (1 : ℝ) ≤ 8 ^ p := one_le_pow₀ (by norm_num)
      have h3 : 2 * (4 : ℝ) ^ T * ((T + 1 : ℕ) : ℝ) ≤ 2 ^ k₀ := by
        have : 0 ≤ 2 * (4 : ℝ) ^ T * ((T + 1 : ℕ) : ℝ) := by positivity
        nlinarith
      exact mul_le_mul_of_nonneg_right h3 he0.le
    -- the nodes of level `T` lie near their grid planes
    have hspacing : scale p T / ((2 ^ p : ℕ) : ℝ) < 100 * δ := by
      rw [div_lt_iff₀ (by positivity)]
      push_cast
      have : (0 : ℝ) < 2 ^ p * δ := by positivity
      nlinarith
    obtain ⟨L, Q, z, G, m, hm, hLc, hLm, hEL, hmM, hG, hdisj, hmasses, hsum, htubeG⟩ :=
      select (ι := Fin T → I p)
        (fun σ => (node p δ E T σ).1)
        (fun σ => WithLp.toLp 2 (node p δ E T σ).2)
        (fun σ => gridPoly (node p δ E T σ).2 (scale p T / ((2 ^ p : ℕ) : ℝ)) (2 ^ p))
        (E := E) (δ := δ) (r := 2 * scale p T) (M := M)
        (Nt := (20 * 2 ^ p) ^ T) (Kd := 18 * 2 ^ p)
        (Nc := (2 * 8 ^ p) ^ T) (k₀ := k₀) (N := T + 1)
        (fun σ => (node_props H T σ).1)
        (fun σ => (node_props H T σ).2.2.1)
        (fun σ => (node_props H T σ).2.1.trans
          (box_subset_closedBall _ (scale_pos p T).le))
        (fun σ => by
          refine ⟨gridPoly_ne_zero _ _ _, ?_, ?_⟩
          · have h1 := totalDegree_gridPoly_le (node p δ E T σ).2
              (scale p T / ((2 ^ p : ℕ) : ℝ)) (2 ^ p)
            have h2 : 3 * (2 ^ p + 1) ≤ 18 * 2 ^ p := by
              have : 1 ≤ 2 ^ p := Nat.one_le_two_pow
              omega
            exact_mod_cast h1.trans h2
          · have h1 := box_subset_thickening_planes (node p δ E T σ).2 (scale_pos p T)
              (D := 2 ^ p) (by positivity) hspacing
            rw [← zeroSet_gridPoly] at h1
            exact (node_props H T σ).2.1.trans h1)
        (node_disj H T) hmax hcount htube hEfin hE0 hft hk₀' hk1
    refine ⟨L, Q, z, G, finish Q z G hδ hKpos (by have := scale_pos p T; positivity)
      (Kd := 18 * 2 ^ p) (by rw [hKdef, hDdef]; nlinarith [hp3, hD1])
      ?_ hmassK htwo ?_ hk1 hN hEfin hE0 (by positivity) hm hLc hLm hEL hmM hG hdisj hmasses
      hsum htubeG⟩
    · have e1 : (2 * scale p T) ^ 3 * (2 * 8 ^ p) ^ T = 64 * (2 : ℝ) ^ T := by
        unfold scale
        rw [h83, mul_pow, ← hDdef]
        field_simp
        ring
      rw [e1]
      exact hdiamK T le_rfl
    · have e1 : ((20 * 2 ^ p) ^ T) ^ 3 * (4 * k₀ * ((T + 1 : ℕ) : ℝ) * M) =
          (20 : ℝ) ^ (3 * T) * 2 ^ T * (4 * k₀ * ((T + 1 : ℕ) : ℝ)) * e := by
        rw [hM, ← hDdef]
        field_simp
        ring
      rw [e1, hX]
      have h1 : (20 : ℝ) ^ (3 * T) * 2 ^ T ≤ B ^ 4 := by
        rw [pow_mul', show B ^ 4 = B ^ 3 * B by ring]
        exact mul_le_mul (pow_le_pow_left₀ (by positivity) h20T 3) (h2t T le_rfl)
          (by positivity) (by positivity)
      have h2 : 4 * (k₀ : ℝ) * ((T + 1 : ℕ) : ℝ) ≤ 4 * (3 * p + 2) * B := by
        have := hk0N
        have h3 : (3 * (p : ℝ) + 2) * 20 ^ T ≤ (3 * p + 2) * B :=
          mul_le_mul_of_nonneg_left h20T (by positivity)
        nlinarith
      have h4 : 4 * (3 * (p : ℝ) + 2) ≤ K ^ 3 := by
        have : (4 : ℝ) * (3 * p + 2) ≤ K := by
          rw [hKdef]
          have : 4 * (3 * (p : ℝ) + 2) * 1 ≤ 2000 * (3 * p + 2) * D :=
            mul_le_mul (by linarith) hD1 (by norm_num) (by positivity)
          linarith
        have h5 : K ≤ K ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
        linarith
      have hB5 : B ^ 5 ≤ (B ^ 8) ^ 3 := by
        rw [← pow_mul]; exact pow_le_pow_right₀ hB1 (by norm_num)
      have hZ : (0 : ℝ) ≤ 4 * (k₀ : ℝ) * ((T + 1 : ℕ) : ℝ) := by positivity
      calc (20 : ℝ) ^ (3 * T) * 2 ^ T * (4 * k₀ * ((T + 1 : ℕ) : ℝ)) * e
          ≤ B ^ 4 * (4 * (3 * p + 2) * B) * e :=
            mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 hZ (by positivity)) he0.le
        _ = (4 * (3 * p + 2)) * B ^ 5 * e := by ring
        _ ≤ K ^ 3 * (B ^ 8) ^ 3 * e :=
            mul_le_mul_of_nonneg_right (mul_le_mul h4 hB5 (by positivity) (by positivity)) he0.le
        _ = (K * B ^ 8) ^ 3 * e := by ring

end Grains
end WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod
