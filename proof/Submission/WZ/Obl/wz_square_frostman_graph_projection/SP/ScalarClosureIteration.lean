-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.ScalarClosureIteration.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.ScalarClosureNumerics
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.ScalarCountPower
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.ScalarGrowth

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products
open scoped Pointwise

/-- Iterating bounded scalar algebra rules out a small-projection family
with positive nonconcentration, regardless of its cardinality relative to A. -/
theorem no_small_scalar_family (ε b β : ℝ) (hε : 0 < ε) (hb : 0 < b)
    (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ ζ δ₀ : ℝ, 0 < ζ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ σ α : ℝ, 0 < δ → δ ≤ δ₀ → b ≤ σ →
        0 ≤ α → α ≤ 1 - ε →
        ∀ A S : Finset ℝ, A.Nonempty → S.Nonempty →
          RealFiniteFrostman δ (δ ^ (-ζ)) σ A →
          RealFiniteFrostman δ (δ ^ (-ζ)) β S →
          (∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → δ ≤ dist a a') →
          (A.card : ℝ) ≤ δ ^ (-α - ζ) →
          (∀ s ∈ S, δ ^ ζ ≤ s ∧ s ≤ 1) →
          SmallScalarProjection δ A (δ ^ (-ζ)) 1 →
          (∀ s ∈ S, SmallScalarProjection δ A (δ ^ (-ζ)) s) → False := by
  classical
  obtain ⟨η, g, r₀, hη, hg, hr₀, hr₀1, hgrow⟩ := scalar_enlargement_grows ε β hε hβ hβ1
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / g)
  have hNg : 2 < (N : ℝ) * g := (div_lt_iff₀ hg).mp hN
  let D : ℝ := 100 ^ N
  let E : ℝ := 3 + 4 / b
  have hD : 0 < D := by dsimp [D]; positivity
  have hD1 : 1 ≤ D := one_le_pow₀ (by norm_num)
  have hE : 0 < E := by dsimp [E]; positivity
  let ζ := min (g / 2) (min (η / (2 * E * D)) (b / (8 * D)))
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hζg : ζ ≤ g := (min_le_left _ _).trans (by linarith)
  have hζη : ζ ≤ η / (2 * E * D) := (min_le_right _ _).trans (min_le_left _ _)
  have hζb : ζ ≤ b / (8 * D) := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨rC, hrC, hrC1, hcut⟩ := exists_power_bound 1000 hζ
  refine ⟨ζ, min r₀ (min rC (1 / 4)), hζ, by positivity,
    (min_le_right _ _).trans ((min_le_right _ _).trans (by norm_num)), ?_⟩
  intro δ σ α hδ hδs hσ hα0 hα A S hA hS hAF hSF hAsep hAc hSb hbase hgood
  have hδr : δ ≤ r₀ := hδs.trans (min_le_left _ _)
  have hδC : δ ≤ rC := hδs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδq : δ ≤ 1 / 4 := hδs.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ1 : δ ≤ 1 := by linarith
  have hconst : 1000 ≤ δ ^ (-ζ) := hcut δ hδ hδC
  let d (n : ℕ) : ℝ := 100 ^ n * ζ
  have hd (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  have hdζ (n : ℕ) : ζ ≤ d n := by
    have hh : (1 : ℝ) ≤ 100 ^ n := one_le_pow₀ (by norm_num)
    dsimp [d]
    nlinarith
  have hdD (n : ℕ) (hn : n ≤ N) : d n ≤ D * ζ := by
    dsimp [d, D]
    gcongr
    norm_num
  have hdη (n : ℕ) (hn : n ≤ N) : E * d n ≤ η := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * E * D)).mp hζη
    have hh' := mul_le_mul_of_nonneg_left (hdD n hn) hE.le
    nlinarith
  have hdb (n : ℕ) (hn : n ≤ N) : 4 * d n / b ≤ 1 := by
    apply (div_le_one hb).mpr
    have hh := (le_div_iff₀ (by positivity : 0 < 8 * D)).mp hζb
    have hh' := hdD n hn
    nlinarith
  have hweaken (n : ℕ) : δ ^ (-ζ) ≤ δ ^ (-(d n)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith [hdζ n])
  have hbase' (n : ℕ) : SmallScalarProjection δ A (δ ^ (-(d n))) 1 :=
    hbase.weaken (hweaken n)
  have hgood' (n : ℕ) (s : ℝ) (hs : s ∈ S) : SmallScalarProjection δ A (δ ^ (-(d n))) s :=
    (hgood s hs).weaken (hweaken n)
  have hSFg : RealFiniteFrostman δ (δ ^ (-g)) β S := hSF.weaken hδ
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  have hbuild : ∀ n : ℕ, n ≤ N → ∃ R : Finset ℝ, R.Nonempty ∧
      (∀ t ∈ R, δ ^ (d n) ≤ t ∧ t ≤ 1) ∧
      (∀ t ∈ R, ∀ u ∈ R, t ≠ u → δ ≤ dist t u) ∧
      (∀ t ∈ R, SmallScalarProjection δ A (δ ^ (-(d n))) t) ∧
      δ ^ (-((n : ℝ) * g)) ≤ (R.card : ℝ) := by
    intro n
    induction n with
    | zero =>
      intro hn
      refine ⟨{1}, by simp, ?_, ?_, ?_, ?_⟩
      · intro t ht
        have ht1 : t = 1 := Finset.mem_singleton.mp ht
        subst t
        exact ⟨Real.rpow_le_one hδ.le hδ1 (hd 0).le, le_rfl⟩
      · simp
      · intro t ht
        have ht1 : t = 1 := Finset.mem_singleton.mp ht
        subst t
        exact hbase' 0
      · simp
    | succ n ih =>
      intro hn
      have hnN : n ≤ N := by omega
      obtain ⟨R, hR, hRb, hRsep, hgoodR, hRc⟩ := ih hnN
      have hdp := hd n
      have hconstn : 1000 ≤ δ ^ (-(d n)) := hconst.trans (hweaken n)
      have hRcard : (R.card : ℝ) ≤ δ ^ (-α - η) := by
        have hAc' : (A.card : ℝ) ≤ δ ^ (-α - d n) := hAc.trans
          (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith [hdζ n]))
        have hh := small_scalar_card_power A R hδ hδ1 hdp hb hσ (hdb n hnN)
          (by linarith) (Real.rpow_nonneg hδ.le _) (hweaken n) hA hAF hAsep hAc' hRsep hgoodR
        exact hh.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by
          have := hdη n hnN
          dsimp [E] at this
          linarith))
      have hSbn (s : ℝ) (hs : s ∈ S) : δ ^ (d n) ≤ s ∧ s ≤ 1 :=
        ⟨(Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (hdζ n)).trans (hSb s hs).1, (hSb s hs).2⟩
      obtain ⟨U, hU, hUb, hUsep, hgoodU, hsum, hprod⟩ := scalar_closure_net A R S hδ
        (Real.rpow_pos_of_pos hδ _) (Real.rpow_le_one hδ.le hδ1 hdp.le)
        (by linarith) hA hR hAsep hRb hSbn (hbase' n) hgoodR (hgood' n)
      have hUcard := hgrow δ α hδ hδr hα0 hα R S U hR hS
        (fun t ht => ⟨(Real.rpow_nonneg hδ.le _).trans (hRb t ht).1, (hRb t ht).2⟩)
        hRsep hRcard hSFg hsum hprod
      have hdsucc : d (n + 1) = 100 * d n := by dsimp [d]; rw [pow_succ]; ring
      refine ⟨U, hU, ?_, hUsep, ?_, ?_⟩
      · intro u hu
        refine ⟨?_, (hUb u hu).2⟩
        apply le_trans _ (hUb u hu).1
        rw [hdsucc, ← Real.rpow_mul_natCast hδ.le]
        apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
        norm_num
        linarith
      · intro u hu
        apply (hgoodU u hu).weaken
        rw [hdsucc]
        exact scalar_closure_rpow_bound hδ hδ1 hdp hconstn
      · calc
          δ ^ (-(((n + 1 : ℕ) : ℝ) * g)) = δ ^ (-g) * δ ^ (-((n : ℝ) * g)) := by
            rw [← Real.rpow_add hδ]
            congr 1
            push_cast
            ring
          _ ≤ δ ^ (-g) * (R.card : ℝ) := mul_le_mul_of_nonneg_left hRc (Real.rpow_nonneg hδ.le _)
          _ ≤ _ := hUcard
  obtain ⟨R, hR, hRb, hRsep, hgoodR, hRcard⟩ := hbuild N le_rfl
  have hpack := real_separated_ball_card hδ (by norm_num : (0 : ℝ) ≤ 1 / 2) R hRsep
    (c := 1 / 2) (fun t ht => by
      rw [Real.dist_eq]
      apply abs_le.mpr
      constructor <;> linarith [(hRb t ht).2, (Real.rpow_pos_of_pos hδ (d N)).trans_le (hRb t ht).1])
  have hcard2 : δ ^ (-2 : ℝ) ≤ (R.card : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)).trans hRcard
  have hmul := mul_le_mul_of_nonneg_right hcard2 (sq_nonneg δ)
  have hid : δ ^ (-2 : ℝ) * δ ^ 2 = 1 := by
    rw [Real.rpow_neg hδ.le, Real.rpow_two]
    exact inv_mul_cancel₀ (pow_ne_zero _ hδ.ne')
  rw [hid] at hmul
  have hupper := mul_le_mul_of_nonneg_right hpack hδ.le
  nlinarith

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
