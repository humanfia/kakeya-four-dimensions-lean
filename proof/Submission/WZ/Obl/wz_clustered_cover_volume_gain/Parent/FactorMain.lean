-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.FactorMain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FactorGreedy
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FactorCore
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FactorDyadic

/-!
# WZ Proposition 4.6 (factoring convex sets) for a family of unit `ρ`-tubes

For `N > 0` unit `ρ`-tubes in `ball 0 R` (`0 < ρ ≤ 1 ≤ R`) there are a subfamily `U` with
`N ≤ K #U` and congruent boxes `box A B (2R) (z i) (e i)` (`ρ ≤ A ≤ B ≤ 2R`) such that, with
`m ≥ KT U` (`m > 0`):
* every convex set `W` contains at most `m vol W / ρ²` tubes of `U`;
* each box contains at least `m vol(box) / (K ρ²)` tubes of `U` (WZ (4.5), so the cover is
  `K`-balanced);
* every tube of `U` lies in at least one and at most `K` boxes (`K`-almost partitioning cover);
* the boxes obey the Katz–Tao convex bound with error `K`;
* inside each box the tubes of `U` obey the Frostman convex bound with error `K`;
with `K = Kc R N ρ = 16·3456³ R³ (⌊log₂(2R/ρ)⌋₊ + 1)² e^{6√(log 384N) + 3}`.
-/

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open scoped Classical

noncomputable section

variable {N : ℕ} {R ρ : ℝ} {y w : Fin N → Space}

/-- The constant of Proposition 4.6. -/
def Kc (R : ℝ) (N : ℕ) (ρ : ℝ) : ℝ :=
  16 * 3456 ^ 3 * R ^ 3 * ((dyExp (2 * R) ρ : ℝ) + 1) ^ 2 * Real.exp (6 * lam N + 3)

theorem Kc_pos {R : ℝ} (hR : 0 < R) (N : ℕ) (ρ : ℝ) : 0 < Kc R N ρ := by unfold Kc; positivity

/-- Reindexing a finset of `Fin J` by `Fin s.card` preserves filtered cardinalities. -/
theorem card_filter_reindex {J : ℕ} (s : Finset (Fin J)) (P : Fin J → Prop) :
    (Finset.univ.filter fun i : Fin s.card => P (s.equivFin.symm i).1).card =
      (s.filter P).card := by
  refine Finset.card_bij (fun i _ => (s.equivFin.symm i).1) ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_filter.mpr ⟨(s.equivFin.symm i).2, (Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ hij
    exact s.equivFin.symm.injective (Subtype.ext hij)
  · intro a ha
    obtain ⟨has, hPa⟩ := Finset.mem_filter.mp ha
    refine ⟨s.equivFin ⟨a, has⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · simpa using hPa
    · simp

set_option maxHeartbeats 1000000 in
theorem Fam.factor (hF : Fam R ρ y w) (hR : 1 ≤ R) (hN : 0 < N) :
    ∃ (U : Finset (Fin N)) (m A B : ℝ) (L : ℕ) (z : Fin L → Space)
      (e : Fin L → Space ≃ₗᵢ[ℝ] Space),
      (N : ℝ) ≤ Kc R N ρ * U.card ∧ 0 < m ∧ ρ ≤ A ∧ A ≤ B ∧ B ≤ 2 * R ∧
      (∀ W, Convex ℝ W → ENNReal.ofReal (((sub ρ y w U W).card : ℝ) * ρ ^ 2) ≤
        ENNReal.ofReal m * volume W) ∧
      (∀ i, m * (A * B * (2 * R)) ≤
        Kc R N ρ * (((sub ρ y w U (box A B (2 * R) (z i) (e i))).card : ℝ) * ρ ^ 2)) ∧
      (∀ k ∈ U, 1 ≤ (Finset.univ.filter fun i => tube ρ y w k ⊆ box A B (2 * R) (z i) (e i)).card ∧
        ((Finset.univ.filter fun i => tube ρ y w k ⊆ box A B (2 * R) (z i) (e i)).card : ℝ) ≤
          Kc R N ρ) ∧
      (∀ V, Convex ℝ V → ENNReal.ofReal
        (((Finset.univ.filter fun i => box A B (2 * R) (z i) (e i) ⊆ V).card : ℝ) * (A * B * (2 * R))) ≤
          ENNReal.ofReal (Kc R N ρ) * volume V) ∧
      (∀ i V, Convex ℝ V → ENNReal.ofReal
        (((sub ρ y w U (box A B (2 * R) (z i) (e i) ∩ V)).card : ℝ) * (A * B * (2 * R))) ≤
          ENNReal.ofReal (Kc R N ρ * (sub ρ y w U (box A B (2 * R) (z i) (e i))).card) * volume V) := by
  have hρ := hF.pos
  have hρ2 : 0 < ρ ^ 2 := pow_pos hρ 2
  have huniv : (Finset.univ : Finset (Fin N)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩
  -- Step 1
  obtain ⟨U₀, -, hU₀ne, hU₀card, hrob⟩ := hF.exists_robust huniv
  rw [Finset.card_univ, Fintype.card_fin] at hU₀card hrob
  set Λ := lam N with hΛ
  set τ₀ := Real.exp (-(2 * Λ + 1)) with hτ₀
  have hτ₀pos : 0 < τ₀ := Real.exp_pos _
  set m := KT ρ y w U₀ with hm
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) (hF.KT_lower hU₀ne)
  -- Step 2
  obtain ⟨J, S, Rm, hprop, hdisj, hsum⟩ := hF.greedy hU₀ne hrob U₀ subset_rfl
  have hsumR : (U₀.card : ℝ) < 2 * ∑ j, ((Rm j).card : ℝ) := by
    have : U₀.card < 2 * ∑ j, (Rm j).card := by omega
    exact_mod_cast this
  -- Step 3: boxes
  have hSne : ∀ j, ∃ k, k ∈ S j := fun j => (hprop j).1
  choose kS hkS using hSne
  have hρR2 : ρ ≤ 2 * R := by linarith [hF.le_one]
  have hbox := fun j => box_approx_cap hρ hρR2 (hF.unit (kS j))
    (hull_convex (ρ := ρ) (y := y) (w := w) (S j))
    (hF.hull_subset_ball (S j)) (tube_subset_hull (hkS j))
  choose a b z e hab using hbox
  -- dyadic classes
  have hR0 : 0 < R := by linarith
  have hR4 : 0 < 2 * R := by linarith
  set D := dyExp (2 * R) ρ with hD
  set T : Finset (ℕ × ℕ) := Finset.range (D + 1) ×ˢ Finset.range (D + 1) with hT
  let cl : Fin J → ℕ × ℕ := fun j => (dyExp (2 * R) (a j), dyExp (2 * R) (b j))
  have hcl : ∀ j ∈ (Finset.univ : Finset (Fin J)), cl j ∈ T := by
    intro j _
    obtain ⟨h1, h2, h3, -, -⟩ := hab j
    simp only [hT, Finset.mem_product, Finset.mem_range, cl]
    exact ⟨Nat.lt_succ_of_le (dyExp_le hR4 hρ h1), Nat.lt_succ_of_le (dyExp_le hR4 hρ (h1.trans h2))⟩
  have hTcard : (T.card : ℝ) = ((D : ℝ) + 1) ^ 2 := by
    simp [hT, Finset.card_product, Finset.card_range]; ring
  have hTne : T.Nonempty := ⟨(0, 0), by simp [hT]⟩
  have hfib := Finset.sum_fiberwise_of_maps_to hcl (fun j => ((Rm j).card : ℝ))
  obtain ⟨c, hcT, hc⟩ := Finset.exists_le_of_sum_le hTne
    (f := fun _ => (∑ j, ((Rm j).card : ℝ)) / T.card)
    (g := fun c => ∑ j ∈ Finset.univ.filter (fun j => cl j = c), ((Rm j).card : ℝ)) (by
      rw [hfib, Finset.sum_const, nsmul_eq_mul]
      rw [mul_div_cancel₀ _ (by positivity)])
  set Jc := Finset.univ.filter fun j => cl j = c with hJc
  set A : ℝ := 2 * R / 2 ^ c.1 with hA
  set B : ℝ := 2 * R / 2 ^ c.2 with hB
  have hJcA : ∀ j ∈ Jc, dyUp (2 * R) (a j) = A := by
    intro j hj
    have := (Finset.mem_filter.mp hj).2
    simp only [cl, Prod.ext_iff] at this
    simp [dyUp, hA, this.1]
  have hJcB : ∀ j ∈ Jc, dyUp (2 * R) (b j) = B := by
    intro j hj
    have := (Finset.mem_filter.mp hj).2
    simp only [cl, Prod.ext_iff] at this
    simp [dyUp, hB, this.2]
  have hapos : ∀ j, 0 < a j := fun j => hρ.trans_le (hab j).1
  have hbpos : ∀ j, 0 < b j := fun j => (hapos j).trans_le (hab j).2.1
  have ha4 : ∀ j, a j ≤ 2 * R := fun j => (hab j).2.1.trans (hab j).2.2.1
  have hAge : ∀ j ∈ Jc, a j ≤ A := fun j hj => hJcA j hj ▸ le_dyUp (hapos j) (ha4 j)
  have hAlt : ∀ j ∈ Jc, A < 2 * a j := fun j hj => hJcA j hj ▸ dyUp_lt (hapos j) hR4
  have hBge : ∀ j ∈ Jc, b j ≤ B := fun j hj => hJcB j hj ▸ le_dyUp (hbpos j) (hab j).2.2.1
  have hBlt : ∀ j ∈ Jc, B < 2 * b j := fun j hj => hJcB j hj ▸ dyUp_lt (hbpos j) hR4
  -- the class carries a `1/(D+1)²` share of the removed tubes
  have htotal_pos : 0 < ∑ j, ((Rm j).card : ℝ) := by
    have : (0 : ℝ) < U₀.card := by exact_mod_cast hU₀ne.card_pos
    linarith
  have hJcsum : (∑ j, ((Rm j).card : ℝ)) / ((D : ℝ) + 1) ^ 2 ≤ ∑ j ∈ Jc, ((Rm j).card : ℝ) := by
    rw [← hTcard]; exact hc
  have hJcne : Jc.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hJcsum
    have : 0 < (∑ j, ((Rm j).card : ℝ)) / ((D : ℝ) + 1) ^ 2 :=
      div_pos htotal_pos (by positivity)
    linarith
  obtain ⟨j₀, hj₀⟩ := hJcne
  have hAρ : ρ ≤ A := (hab j₀).1.trans (hAge j₀ hj₀)
  have hAB : A ≤ B := by
    rw [← hJcA j₀ hj₀, ← hJcB j₀ hj₀]
    exact dyUp_le_dyUp hR4.le (dyExp_le hR4 (hapos j₀) (hab j₀).2.1)
  have hBρ : ρ ≤ B := ((hab j₀).1.trans (hab j₀).2.1).trans (hBge j₀ hj₀)
  have hB8 : B ≤ 2 * R := hJcB j₀ hj₀ ▸ dyUp_le hR4.le
  have hApos : 0 < A := hρ.trans_le hAρ
  have hBpos : 0 < B := hρ.trans_le hBρ
  set V₀ := A * B * (2 * R) with hV₀
  have hV₀pos : 0 < V₀ := by positivity
  set Bx : Fin J → Set Space := fun j => box A B (2 * R) (z j) (e j) with hBx
  set θ := τ₀ / (3456 * R) with hθ
  have hθpos : 0 < θ := by positivity
  -- the hypotheses of the core
  have hRsub : ∀ j ∈ Jc, Rm j ⊆ sub ρ y w U₀ (Bx j) := by
    intro j hj k hk
    obtain ⟨-, -, hRU, hRhull, -⟩ := hprop j
    refine mem_sub.mpr ⟨hRU hk, ?_⟩
    exact ((hRhull k hk).trans (hab j).2.2.2.1).trans
      (box_mono (hAge j hj) (hBge j hj) le_rfl _ _)
  have hRlarge : ∀ j ∈ Jc, θ * m * V₀ ≤ (Rm j).card * ρ ^ 2 := by
    intro j hj
    obtain ⟨-, -, -, -, hlarge⟩ := hprop j
    have hvolfin : volume (hull ρ y w (S j)) ≠ ⊤ := (hF.hull_volume_lt_top _).ne
    have hab432 : a j * b j ≤ 432 * (volume (hull ρ y w (S j))).toReal := by
      have h := (hab j).2.2.2.2
      rw [← ENNReal.ofReal_toReal hvolfin, ← ENNReal.ofReal_ofNat 432,
        ← ENNReal.ofReal_mul (by norm_num)] at h
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
    have hV₀le : V₀ ≤ 3456 * R * (volume (hull ρ y w (S j))).toReal := by
      have h1 : A * B ≤ 4 * (a j * b j) := by
        nlinarith [hAlt j hj, hBlt j hj, hapos j, hbpos j]
      simp only [hV₀]
      nlinarith
    calc θ * m * V₀ = τ₀ * m * (V₀ / (3456 * R)) := by rw [hθ]; field_simp
      _ ≤ τ₀ * m * (volume (hull ρ y w (S j))).toReal := by
          gcongr
          rw [div_le_iff₀ (by positivity)]
          linarith
      _ ≤ (Rm j).card * ρ ^ 2 := hlarge
  have hRdisj : ∀ i ∈ Jc, ∀ j ∈ Jc, i ≠ j → Disjoint (Rm i) (Rm j) :=
    fun i _ j _ hij => hdisj i j hij
  have hBvol : ∀ j ∈ Jc, volume (Bx j) = ENNReal.ofReal V₀ := fun j _ =>
    box_volume hApos.le hBpos.le (by positivity) _ _
  obtain ⟨U', hU'U₀, J', hJ'Jc, hcore1, hcore2, hcore3, hcore4, hcore5⟩ :=
    hF.factor_core le_rfl hm0 hθpos hV₀pos ⟨j₀, hj₀⟩ (fun j => box_convex _ _ _ _ _) hBvol
      hRsub hRlarge hRdisj
  -- constants
  have hD1 : (1 : ℝ) ≤ ((D : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ D := Nat.cast_nonneg _
    nlinarith
  have hR3 : R ≤ R ^ 3 := le_self_pow₀ hR (by norm_num)
  have hR23 : R ^ 2 ≤ R ^ 3 := pow_le_pow_right₀ hR (by norm_num)
  have hΛ0 := lam_nonneg N
  have hKc1 : 2 / θ ≤ Kc R N ρ := by
    have h1 : 2 / θ = 6912 * R * Real.exp (2 * Λ + 1) := by
      rw [hθ, hτ₀, Real.exp_neg]; field_simp; ring
    rw [h1, Kc, ← hΛ]
    have hexp : Real.exp (2 * Λ + 1) ≤ Real.exp (6 * Λ + 3) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have he := Real.exp_pos (2 * Λ + 1)
    calc 6912 * R * Real.exp (2 * Λ + 1) ≤ 16 * 3456 ^ 3 * R ^ 3 * 1 * Real.exp (6 * Λ + 3) := by
          have : 6912 * R ≤ 16 * 3456 ^ 3 * R ^ 3 := by nlinarith
          calc 6912 * R * Real.exp (2 * Λ + 1) ≤ 16 * 3456 ^ 3 * R ^ 3 * Real.exp (2 * Λ + 1) := by
                gcongr
            _ ≤ 16 * 3456 ^ 3 * R ^ 3 * 1 * Real.exp (6 * Λ + 3) := by
                rw [mul_one]; gcongr
      _ ≤ 16 * 3456 ^ 3 * R ^ 3 * ((D : ℝ) + 1) ^ 2 * Real.exp (6 * Λ + 3) := by gcongr
  have hKc2 : 8 / θ ^ 2 ≤ Kc R N ρ := by
    have h1 : 8 / θ ^ 2 = 8 * 3456 ^ 2 * R ^ 2 * Real.exp (4 * Λ + 2) := by
      rw [hθ, hτ₀, div_pow, Real.exp_neg, inv_pow, ← Real.exp_nat_mul]
      field_simp
      push_cast; ring_nf
    rw [h1, Kc, ← hΛ]
    have hexp : Real.exp (4 * Λ + 2) ≤ Real.exp (6 * Λ + 3) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have he := Real.exp_pos (4 * Λ + 2)
    have h2 : 8 * 3456 ^ 2 * R ^ 2 ≤ 16 * 3456 ^ 3 * R ^ 3 := by nlinarith
    calc 8 * 3456 ^ 2 * R ^ 2 * Real.exp (4 * Λ + 2)
        ≤ 16 * 3456 ^ 3 * R ^ 3 * Real.exp (6 * Λ + 3) := by gcongr
      _ = 16 * 3456 ^ 3 * R ^ 3 * 1 * Real.exp (6 * Λ + 3) := by ring
      _ ≤ 16 * 3456 ^ 3 * R ^ 3 * ((D : ℝ) + 1) ^ 2 * Real.exp (6 * Λ + 3) := by gcongr
  have hKc3 : 16 / θ ^ 3 ≤ Kc R N ρ := by
    have h1 : 16 / θ ^ 3 = 16 * 3456 ^ 3 * R ^ 3 * Real.exp (6 * Λ + 3) := by
      rw [hθ, hτ₀, div_pow, Real.exp_neg, inv_pow, ← Real.exp_nat_mul]
      field_simp
      push_cast; ring_nf
    rw [h1, Kc, ← hΛ]
    calc 16 * 3456 ^ 3 * R ^ 3 * Real.exp (6 * Λ + 3)
        = 16 * 3456 ^ 3 * R ^ 3 * 1 * Real.exp (6 * Λ + 3) := by ring
      _ ≤ 16 * 3456 ^ 3 * R ^ 3 * ((D : ℝ) + 1) ^ 2 * Real.exp (6 * Λ + 3) := by gcongr
  have hKc0 : 16 * 3456 * R * ((D : ℝ) + 1) ^ 2 * Real.exp (3 * Λ + 1) ≤ Kc R N ρ := by
    rw [Kc, ← hΛ]
    have hexp : Real.exp (3 * Λ + 1) ≤ Real.exp (6 * Λ + 3) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h2 : 16 * 3456 * R ≤ 16 * 3456 ^ 3 * R ^ 3 := by nlinarith
    calc 16 * 3456 * R * ((D : ℝ) + 1) ^ 2 * Real.exp (3 * Λ + 1)
        ≤ 16 * 3456 ^ 3 * R ^ 3 * ((D : ℝ) + 1) ^ 2 * Real.exp (3 * Λ + 1) := by gcongr
      _ ≤ 16 * 3456 ^ 3 * R ^ 3 * ((D : ℝ) + 1) ^ 2 * Real.exp (6 * Λ + 3) := by gcongr
  -- reindex the boxes of `J'`
  let idx : Fin J'.card → Fin J := fun i => (J'.equivFin.symm i).1
  have hidx : ∀ i, idx i ∈ J' := fun i => (J'.equivFin.symm i).2
  refine ⟨U', m, A, B, J'.card, fun i => z (idx i), fun i => e (idx i), ?_, hm0, hAρ, hAB,
    hB8, ?_, ?_, ?_, ?_, ?_⟩
  · -- (i)
    have h1 : (N : ℝ) ≤ Real.exp Λ * U₀.card := hU₀card
    have h2 : (U₀.card : ℝ) ≤ 2 * ((D : ℝ) + 1) ^ 2 * (8 / θ * U'.card) := by
      have h3 := hJcsum.trans hcore1
      rw [div_le_iff₀ (by positivity)] at h3
      nlinarith
    have h4 : Real.exp Λ * (2 * ((D : ℝ) + 1) ^ 2 * (8 / θ * U'.card)) =
        16 * 3456 * R * ((D : ℝ) + 1) ^ 2 * Real.exp (3 * Λ + 1) * U'.card := by
      rw [show 3 * Λ + 1 = Λ + (2 * Λ + 1) by ring, Real.exp_add, hθ, hτ₀, Real.exp_neg]
      field_simp
      ring
    calc (N : ℝ) ≤ Real.exp Λ * U₀.card := h1
      _ ≤ Real.exp Λ * (2 * ((D : ℝ) + 1) ^ 2 * (8 / θ * U'.card)) := by gcongr
      _ = 16 * 3456 * R * ((D : ℝ) + 1) ^ 2 * Real.exp (3 * Λ + 1) * U'.card := h4
      _ ≤ Kc R N ρ * U'.card := by gcongr
  · -- the Katz–Tao bound for `U'`
    intro W hW
    exact hF.count_le_ennreal U' hW (KT_mono hU'U₀) hm0
  · -- (4.5)
    intro i
    exact (hcore2 _ (hidx i)).trans (by gcongr)
  · -- cover, almost partitioning
    intro k hk
    have hc := card_filter_reindex J' (fun j => tube ρ y w k ⊆ Bx j)
    simp only [hBx] at hc
    rw [hc]
    exact ⟨(hcore3 k hk).1, (hcore3 k hk).2.trans hKc1⟩
  · -- Katz–Tao for the boxes
    intro V hV
    by_cases hVt : volume V = ⊤
    · rw [hVt, ENNReal.mul_top (by simpa using Kc_pos hR0 N ρ)]; exact le_top
    have hc := card_filter_reindex J' (fun j => Bx j ⊆ V)
    simp only [hBx] at hc
    rw [hc, ← ENNReal.ofReal_toReal hVt, ← ENNReal.ofReal_mul (Kc_pos hR0 N ρ).le]
    apply ENNReal.ofReal_le_ofReal
    exact (hcore4 V hV hVt).trans (by gcongr)
  · -- Frostman below
    intro i V hV
    by_cases hVt : volume V = ⊤
    · by_cases h0 : (sub ρ y w U' (box A B (2 * R) (z (idx i)) (e (idx i)))).card = 0
      · have hsub : sub ρ y w U' (box A B (2 * R) (z (idx i)) (e (idx i)) ∩ V) = ∅ := by
          rw [Finset.card_eq_zero] at h0
          exact Finset.subset_empty.mp (h0 ▸ sub_mono subset_rfl Set.inter_subset_left)
        rw [hsub]; simp
      · rw [hVt, ENNReal.mul_top]; exact le_top
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact mul_pos (Kc_pos hR0 N ρ) (by exact_mod_cast Nat.pos_of_ne_zero h0)
    rw [← ENNReal.ofReal_toReal hVt,
      ← ENNReal.ofReal_mul (mul_nonneg (Kc_pos hR0 N ρ).le (Nat.cast_nonneg _))]
    apply ENNReal.ofReal_le_ofReal
    refine (hcore5 _ (hidx i) V hV hVt).trans ?_
    gcongr

end

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor
