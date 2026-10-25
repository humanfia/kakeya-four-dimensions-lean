-- Adapted from this LOT tree o194, session x0672, commit 69d09a7b8755,
-- Submission/Obl/k4_greedy_cover_graph_atlas/Prepare.lean. Earlier attributions follow.

-- Adapted from this LOT tree, o173, session x0581, commit 793edcb4e591,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/Prepare.lean.

import Submission.Obl.k4_clean_cover_graph_atlas.Core
import Submission.Obl.k4_clean_cover_graph_atlas.Certificates

/-!
# `Preparation` from the analytic core

Quantifier bookkeeping and polynomial counting: the analytic core supplies bins, representatives,
lists and covered incidences; `graphAtlas_of_entries` assembles the graph atlas. The complexity
exponent is `M = Mp + Mpr + 2 Mg + 4 Mc + 20`, where `Mpr` is the problem's own exponent.
-/

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory MvPolynomial Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets

theorem card_entry (n s₀ K : ℕ) :
    Fintype.card (Entry n s₀ K) = n * (2 ^ s₀ * ((2 * K + 2) ^ 2 * (2 * 2))) := by
  simp [Entry, Fintype.card_prod, Fintype.card_fin, Fintype.card_pi, Fintype.card_bool]

theorem card_label (C s₀ K : ℕ) (Λ : Type) [Fintype Λ] :
    Fintype.card ((Fin C × Fin (2 ^ s₀) × (Fin 2 → Fin (2 * K + 2)) × Bool) × Λ) =
      C * (2 ^ s₀ * ((2 * K + 2) ^ 2 * 2)) * Fintype.card Λ := by
  simp [Fintype.card_prod, Fintype.card_fin, Fintype.card_pi, Fintype.card_bool]

/-- `2 K + 2 ≤ 4 N^a` when `K ≤ N^a` and `N ≥ 1`. -/
theorem two_mul_add_two_le {Nk : ℝ} (hN : 1 ≤ Nk) {K a : ℕ} (hK : (K : ℝ) ≤ Nk ^ a) :
    ((2 * K + 2 : ℕ) : ℝ) ≤ 4 * Nk ^ a := by
  have h1 : (1 : ℝ) ≤ Nk ^ a := one_le_pow₀ hN
  push_cast
  linarith

theorem le_pow_of_le_two_pow {Nk : ℝ} (hN : 2 ≤ Nk) {c : ℝ} {e : ℕ} (hc : c ≤ 2 ^ e) :
    c ≤ Nk ^ e :=
  hc.trans (pow_le_pow_left₀ (by norm_num) hN e)

theorem pow_le_pow_add {Nk : ℝ} (hN : 1 ≤ Nk) {a b : ℕ} (h : a ≤ b) : Nk ^ a ≤ Nk ^ b :=
  pow_le_pow_right₀ hN h

theorem cu_bound {Nk κ : ℝ} (hNk2 : 2 ≤ Nk) (hκ0 : 0 ≤ κ) (hκN : κ ≤ Nk) {Mp M : ℕ}
    (hM : Mp + 4 ≤ M) : Nk ^ Mp + κ * (κ + 1) ≤ Nk ^ M := by
  have hNk0 : 0 < Nk := by linarith
  have hNk1 : 1 ≤ Nk := by linarith
  have h1 : κ * (κ + 1) ≤ Nk * (2 * Nk) :=
    mul_le_mul hκN (by linarith) (by linarith) hNk0.le
  have h2 : Nk * (2 * Nk) ≤ Nk ^ 3 := by
    have e : Nk ^ 3 = Nk * (Nk * Nk) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hNk2 hNk0.le) hNk0.le
  have h3 : Nk ^ Mp ≤ Nk ^ (Mp + 3) := pow_le_pow_add hNk1 (by omega)
  have h3' : Nk ^ 3 ≤ Nk ^ (Mp + 3) := pow_le_pow_add hNk1 (by omega)
  have h4 : 2 * Nk ^ (Mp + 3) ≤ Nk ^ (Mp + 4) := by
    have e : Nk ^ (Mp + 4) = Nk ^ (Mp + 3) * Nk := pow_succ Nk (Mp + 3)
    rw [e]
    have := mul_le_mul_of_nonneg_left hNk2 (pow_pos hNk0 (Mp + 3)).le
    linarith
  have h5 : Nk ^ (Mp + 4) ≤ Nk ^ M := pow_le_pow_add hNk1 hM
  linarith

theorem fmt_bound {Nk : ℝ} (hNk2 : 2 ≤ Nk) {n s₀ K' Mg Mc Mpr M : ℕ} (hn : (n : ℝ) ≤ Nk ^ Mg)
    (hs₀ : (2 : ℝ) ^ s₀ ≤ Nk ^ Mc) (hK' : (K' : ℝ) ≤ Nk ^ Mc)
    (hM : Mpr + 2 * Mg + 3 * Mc + 11 ≤ M) :
    Nk ^ Mpr + (Fintype.card (Entry n s₀ K') : ℝ) * (Nk ^ Mg + 6) + 11 + 3 ≤ Nk ^ M := by
  have hNk0 : 0 < Nk := by linarith
  have hNk1 : 1 ≤ Nk := by linarith
  rw [card_entry]
  push_cast
  have hb : (2 : ℝ) * K' + 2 ≤ 4 * Nk ^ Mc := by
    have := one_le_pow₀ (n := Mc) hNk1; linarith
  have hb2 : ((2 : ℝ) * K' + 2) ^ 2 ≤ 16 * Nk ^ (2 * Mc) := by
    calc ((2 : ℝ) * K' + 2) ^ 2 ≤ (4 * Nk ^ Mc) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hb 2
      _ = 16 * Nk ^ (2 * Mc) := by rw [mul_pow, ← pow_mul]; norm_num; ring_nf
  have e1 : (n : ℝ) * (2 ^ s₀ * ((2 * K' + 2) ^ 2 * (2 * 2))) ≤
      Nk ^ Mg * (Nk ^ Mc * (16 * Nk ^ (2 * Mc) * (2 * 2))) := by
    gcongr
  have e2 : Nk ^ Mg + 6 ≤ 7 * Nk ^ Mg := by
    have := one_le_pow₀ (n := Mg) hNk1; linarith
  set X := Nk ^ (2 * Mg + 3 * Mc) with hX
  have e3 : Nk ^ Mg * (Nk ^ Mc * (16 * Nk ^ (2 * Mc) * (2 * 2))) * (7 * Nk ^ Mg) = 448 * X := by
    rw [hX]; ring
  have e4 : (448 : ℝ) ≤ Nk ^ 9 := (by norm_num : (448 : ℝ) ≤ 2 ^ 9).trans
    (pow_le_pow_left₀ (by norm_num) hNk2 9)
  have hXpos : 0 ≤ X := by positivity
  have e5 : 448 * X ≤ Nk ^ (2 * Mg + 3 * Mc + 9) := by
    have e : Nk ^ (2 * Mg + 3 * Mc + 9) = X * Nk ^ 9 := by rw [hX, ← pow_add]
    rw [e, mul_comm]
    exact mul_le_mul_of_nonneg_left e4 hXpos
  have hmul : (n : ℝ) * (2 ^ s₀ * ((2 * K' + 2) ^ 2 * (2 * 2))) * (Nk ^ Mg + 6) ≤
      Nk ^ (2 * Mg + 3 * Mc + 9) := by
    calc (n : ℝ) * (2 ^ s₀ * ((2 * K' + 2) ^ 2 * (2 * 2))) * (Nk ^ Mg + 6)
        ≤ Nk ^ Mg * (Nk ^ Mc * (16 * Nk ^ (2 * Mc) * (2 * 2))) * (7 * Nk ^ Mg) :=
          mul_le_mul e1 e2 (by positivity) (by positivity)
      _ = 448 * X := e3
      _ ≤ _ := e5
  set Y := Nk ^ (Mpr + 2 * Mg + 3 * Mc + 9) with hY
  have a1 : Nk ^ Mpr ≤ Y := pow_le_pow_add hNk1 (by omega)
  have a2 : Nk ^ (2 * Mg + 3 * Mc + 9) ≤ Y := pow_le_pow_add hNk1 (by omega)
  have a3 : (14 : ℝ) ≤ Y := by
    have : (14 : ℝ) ≤ Nk ^ 9 := (by norm_num : (14 : ℝ) ≤ 2 ^ 9).trans
      (pow_le_pow_left₀ (by norm_num) hNk2 9)
    exact this.trans (pow_le_pow_add hNk1 (by omega))
  have a4 : 3 * Y ≤ Nk ^ (Mpr + 2 * Mg + 3 * Mc + 11) := by
    have e : Nk ^ (Mpr + 2 * Mg + 3 * Mc + 11) = Y * Nk ^ 2 := by rw [hY, ← pow_add]
    rw [e]
    have h4 : (3 : ℝ) ≤ Nk ^ 2 := by nlinarith
    have hY0 : 0 ≤ Y := by positivity
    nlinarith
  have a5 : Nk ^ (Mpr + 2 * Mg + 3 * Mc + 11) ≤ Nk ^ M := pow_le_pow_add hNk1 hM
  linarith

theorem card_bound {Nk : ℝ} (hNk2 : 2 ≤ Nk) {C s₀ K' Mp Mc M : ℕ} {Λ : Type} [Fintype Λ]
    (hC : (C : ℝ) ≤ Nk ^ Mp) (hs₀ : (2 : ℝ) ^ s₀ ≤ Nk ^ Mc) (hK' : (K' : ℝ) ≤ Nk ^ Mc)
    (hΛ : (Fintype.card Λ : ℝ) ≤ Nk ^ Mc) (hM : Mp + 4 * Mc + 5 ≤ M) :
    (Fintype.card ((Fin C × Fin (2 ^ s₀) × (Fin 2 → Fin (2 * K' + 2)) × Bool) × Λ) : ℝ)
      ≤ Nk ^ M := by
  have hNk0 : 0 < Nk := by linarith
  have hNk1 : 1 ≤ Nk := by linarith
  rw [card_label]
  push_cast
  have hb : (2 : ℝ) * K' + 2 ≤ 4 * Nk ^ Mc := by
    have := one_le_pow₀ (n := Mc) hNk1; linarith
  have hb2 : ((2 : ℝ) * K' + 2) ^ 2 ≤ 16 * Nk ^ (2 * Mc) := by
    calc ((2 : ℝ) * K' + 2) ^ 2 ≤ (4 * Nk ^ Mc) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hb 2
      _ = 16 * Nk ^ (2 * Mc) := by rw [mul_pow, ← pow_mul]; norm_num; ring_nf
  set X := Nk ^ (Mp + 4 * Mc) with hX
  calc (C : ℝ) * (2 ^ s₀ * ((2 * K' + 2) ^ 2 * 2)) * (Fintype.card Λ : ℝ)
      ≤ Nk ^ Mp * (Nk ^ Mc * (16 * Nk ^ (2 * Mc) * 2)) * Nk ^ Mc := by
        gcongr
    _ = 32 * X := by rw [hX]; ring
    _ ≤ Nk ^ 5 * X := mul_le_mul_of_nonneg_right ((by norm_num : (32 : ℝ) ≤ 2 ^ 5).trans
        (pow_le_pow_left₀ (by norm_num) hNk2 5)) (by positivity)
    _ = Nk ^ (Mp + 4 * Mc + 5) := by rw [hX, ← pow_add]; ring_nf
    _ ≤ Nk ^ M := pow_le_pow_add hNk1 hM

/-- Finite label-system construction gives the exact finite atlas statement.
All polynomial exponents are fixed before `β`; only numerical thresholds are enlarged. -/
theorem finiteConstruction_of_core (hcore : FiniteCore) : FiniteConstruction := by
  intro hgraph hsheets hremez d₁ κ₁ hd₁ hd₁1 hκ₁ hκ₁1
  obtain ⟨θ, ρ, hθ, hθ1, hρ, hρ4, hdρ, hc⟩ := hcore hgraph hsheets hremez d₁ κ₁ hd₁ hd₁1 hκ₁ hκ₁1
  refine ⟨θ, ρ, hθ, hθ1, hρ, hρ4, hdρ, ?_⟩
  intro L m s gain δ₀ hL hgrid hgain hgain1 hδ₀ hδρ Mp Dp Mg Dg Mpr Dpr
  obtain ⟨Mc, hMc⟩ := hc L m s gain δ₀ hL hgrid hgain hgain1 hδ₀ hδρ Mp Dp Mg Dg Mpr Dpr
  refine ⟨Mp + Mpr + 2 * Mg + 4 * Mc + 20, max Dpr (max Dg 4), ?_⟩
  intro β hβ hβ1
  obtain ⟨τ, ε₀, σ₀, hτ, hε₀, hε₀1, hσ₀, hσ₀1, hσ₀β, N₀, hN₀2, hk₀⟩ := hMc β hβ hβ1
  have hev : ∀ᶠ Nk : ℝ in Filter.atTop, (2 : ℝ) ≤ Nk ^ (β / 2) :=
    (tendsto_rpow_atTop (by positivity : 0 < β / 2)).eventually_ge_atTop 2
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨τ, ε₀, σ₀, hτ, hε₀, hε₀1, hσ₀, hσ₀1, max N₀ N₁, hN₀2.trans (le_max_left _ _), ?_⟩
  intro Nk hNk W ω ν E B f hpr hlin ε σ hε hεbound hεβ hσ hσbound
    r T nw κ C lev par γ j c u Q R A F lst hpath hcover
  obtain ⟨i, h, n, old, R', A', s₀, K', hi, hgh, hh, hmargin, hn, hA', hA'disj, htime, hs₀, hK',
    hout⟩ := hk₀ Nk ((le_max_left _ _).trans hNk) W ω ν E B f hpr hlin ε σ hε hεbound hεβ hσ
      hσbound r T nw κ C lev par γ j c u Q R A F lst hpath hcover
  obtain ⟨Λ, hΛ, hΛd, binOf, Prep, sc, m₀, lst₂, cov, hcardΛ, hP, hPcoef, hs, hm₀, hcurv, hcov,
    hclose, hlst, hlstm, hsucc⟩ := hout
  have hNk2 : 2 ≤ Nk := hN₀2.trans ((le_max_left _ _).trans hNk)
  have hNk1 : 1 ≤ Nk := by linarith
  have hNk0 : 0 < Nk := by linarith
  have hβ2 : 2 ≤ Nk ^ (β / 2) := hN₁ Nk ((le_max_right _ _).trans hNk)
  obtain ⟨hκ1, hκσ, hC, -, -, -, hAdisj, hcharts⟩ := hpath
  set M := Mp + Mpr + 2 * Mg + 4 * Mc + 20 with hMdef
  have hpowle : ∀ a b : ℕ, a ≤ b → Nk ^ a ≤ Nk ^ b := fun a b hab => pow_le_pow_right₀ hNk1 hab
  have hB0 : ∀ w, 0 < B w := fun w => (hpr.2.2.2 w).2.1
  have hold : ∀ a, gchart Nk Mp Dp κ (T i) (j (old a) : ℝ) (r i) (B (γ (old a)))
      (E (γ (old a))) (c (old a)) (u (old a)) (Q (old a)) (R (old a)) (A (old a)) (F (old a))
      True := by
    intro a
    have h := (hcharts (old a)).2.2
    rw [(hA' a).1] at h
    exact gchart_mono h hNk1 le_rfl le_rfl (by linarith) le_rfl (hB0 _).le (fun _ => trivial)
  have hjlt : ∀ a, j (old a) < 2 ^ T i := by
    intro a
    have h := (hcharts (old a)).2.1
    rw [(hA' a).1] at h
    exact h
  have hR : ∀ b, (R b).totalDegree ≤ 2 := fun b => (hcharts b).2.2.2.2.2.2.1
  have hB : ∀ w, 0 < B w ∧ B w ≤ Nk ^ M ∧ (B w)⁻¹ ≤ Nk ^ M := by
    intro w
    obtain ⟨-, h1, h2, h3, -⟩ := hpr.2.2.2 w
    exact ⟨h1, h2.trans (hpowle _ _ (by omega)), h3.trans (hpowle _ _ (by omega))⟩
  have hE : ∀ w q, gfmt 7 (Nk ^ Mpr) Dpr
      {x₁ : Fin 7 → ℝ | ((q, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ E w} := by
    intro w q
    exact (hpr.2.2.2 w).2.2.2.2.2 q
  have hκ0 : 0 ≤ κ := by linarith
  have hκβ : κ + 1 ≤ Nk ^ β := by
    have h1 : κ ≤ Nk ^ (β / 2) :=
      hκσ.trans (Real.rpow_le_rpow_of_exponent_le hNk1 (hσbound.trans hσ₀β))
    have h2 : Nk ^ β = Nk ^ (β / 2) * Nk ^ (β / 2) := by
      rw [← Real.rpow_add hNk0]; ring_nf
    rw [h2]
    nlinarith
  have hκN : κ ≤ Nk := by
    calc κ ≤ Nk ^ (β / 2) := hκσ.trans
          (Real.rpow_le_rpow_of_exponent_le hNk1 (hσbound.trans hσ₀β))
      _ ≤ Nk ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNk1 (by linarith)
      _ = Nk := Real.rpow_one Nk
  have hcu : Nk ^ Mp + κ * (κ + 1) ≤ Nk ^ M := cu_bound hNk2 hκ0 hκN (by omega)
  have hside : (side s₀)⁻¹ = (2 : ℝ) ^ s₀ := by unfold side; rw [inv_inv]
  have hfr : (side s₀)⁻¹ * Nk ^ Mp ≤ Nk ^ M := by
    rw [hside]
    calc (2 : ℝ) ^ s₀ * Nk ^ Mp ≤ Nk ^ Mc * Nk ^ Mp :=
          mul_le_mul_of_nonneg_right hs₀ (by positivity)
      _ = Nk ^ (Mc + Mp) := by rw [pow_add]
      _ ≤ Nk ^ M := hpowle _ _ (by omega)
  have hfmtM : Nk ^ Mpr + (Fintype.card (Entry n s₀ K') : ℝ) * (Nk ^ Mg + 6) + 11 + 3 ≤ Nk ^ M :=
    fmt_bound hNk2 hn hs₀ hK' (by omega)
  have hcard := card_bound (Λ := Λ) hNk2 hC hs₀ hK' hcardΛ (M := M) (by omega)
  have hDle : max Dpr (max (max Dg 2) 4) ≤ max Dpr (max Dg 4) := by
    refine max_le (le_max_left _ _) (max_le (max_le ((le_max_left _ _).trans (le_max_right _ _))
      ?_) ((le_max_right _ _).trans (le_max_right _ _)))
    exact (by norm_num : (2 : ℕ) ≤ 4).trans ((le_max_right Dg 4).trans (le_max_right _ _))
  obtain ⟨C₂, γ₃, j₃, c₃, u₃, Q₃, P₃, s₃, A₃, F₃, lst₃, hatlas⟩ :=
    graphAtlas_of_entries (lev := lev) (i := i) (Mg := Mg) (Dg := Dg) (ex := fun _ => True) binOf Prep sc m₀ lst₂ cov hNk1 hB hE
      hold (fun a => (hA' a).1) hjlt hAdisj (fun a => (hA' a).2.2.1) hA'disj
      (fun a => (hA' a).2.2.2) (fun a => (hA' a).2.1) hR hP
      (fun ℓ e => (hPcoef ℓ e).trans (hpowle _ _ (by omega)))
      (fun ℓ => ⟨(hs ℓ).1, (hs ℓ).2.1.trans (hpowle _ _ (by omega)),
        (hs ℓ).2.2.trans (hpowle _ _ (by omega))⟩) hm₀ hcurv hcov hclose hlst hlstm hsucc
      hκβ (by omega) hcu hfr hfmtM hDle hcard
  exact ⟨i, h, T i + s₀, C₂, γ₃, j₃, c₃, u₃, Q₃, P₃, s₃, A₃, F₃, lst₃, hi, hgh, hh, hmargin,
    htime, hatlas⟩

end Submission.Obl.k4_clean_cover_graph_atlas
