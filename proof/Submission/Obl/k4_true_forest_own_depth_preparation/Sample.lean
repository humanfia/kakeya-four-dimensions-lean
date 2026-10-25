import Submission.Obl.k4_true_forest_own_depth_preparation.Prepared
import Submission.Obl.k4_true_forest_own_depth_preparation.CommonCutFormat
import Submission.Obl.k4_true_forest_own_depth_preparation.Cleanup
import Submission.Obl.k4_true_forest_own_depth_preparation.ForestEnumeration
import Submission.Obl.k4_true_forest_own_depth_preparation.IncidenceBudget
import Submission.Obl.k4_true_forest_own_depth_preparation.ChartRestriction
import Submission.Obl.k4_true_forest_own_depth_preparation.HeavyPrior
import Submission.Obl.k4_true_forest_own_depth_preparation.Numerics
import Submission.Obl.k4_quadratic_atlas_normalization.MassSelection

namespace Submission.Obl.k4_true_forest_own_depth_preparation

open MeasureTheory Set Classical
open Submission.Obl.k4_coarsened_outer_horizon_composition

/-- At one sample, small layer deletions and a small heavy-prior budget give
all clauses of the prepared forest, with one fixed output format. -/
theorem prepare_sample
    {N K : ℕ → ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ} {ν : (k : ℕ) → Fin (W k) → Measure Line}
    {E : (k : ℕ) → Fin (W k) → Set Inc} {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {M D M₁ D₁ k m C : ℕ} {r : ℕ → ℝ} {T : ℕ → ℕ} {κ θ κ' : ℝ}
    {lev : Fin C → ℕ} {par : Fin C → Fin C} {γ : Fin C → Fin (W k)} {j : Fin C → ℕ}
    {c u : Fin C → E2} {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ}
    {R : Fin C → MvPolynomial (Fin 4) ℝ} {A : Fin C → Set Line} {F : Fin C → Set Inc}
    (hN : 2 ≤ N k) (hν : ∀ w, IsProbabilityMeasure (ν k w))
    (hE : ∀ w, E k w ⊆ univ ×ˢ Icc (0 : ℝ) 1) (hB : ∀ w, 0 < B k w)
    (hM : M ≤ M₁) (hD : D ≤ D₁) (hκθ : κ ≤ θ) (hθκ' : θ ≤ κ') (hdouble : 2 * κ ≤ κ')
    (hc : Core N K W ω ν E B f M D k m r T κ C lev par γ j c u Q R A F)
    (H : Fin C → Set Inc) (lst : ℕ → Fin (W k) → Obs → Finset (Fin C))
    (hlist : ∀ i w o, ((lst i w o).card : ℝ) ≤ θ)
    (hH : ∀ b, chart (N k) M₁ D₁ θ (T (lev b)) (j b : ℝ) (r (lev b))
      (B k (γ b)) (E k (γ b)) (c b) (u b) (Q b) (R b) (A b) (H b)
      (∀ p ∈ H b, b ∈ lst (lev b) (γ b) (obs (B k (γ b)) (δ (N k) (r (lev b))) p)))
    (cutLoss heavyLoss : ENNReal)
    (hcut : (∑ b, ENNReal.ofReal (ω k (γ b)) * ((ν k (γ b)).prod volume) (F b \ H b)) ≤ cutLoss)
    (hheavy : (∑ b, if ¬ν k (γ b) (A b) ≤
      ENNReal.ofReal (κ' * N k ^ (-f (r (lev b))) * |(Q b).det|) then
        ENNReal.ofReal (ω k (γ b)) * ((ν k (γ b)).prod volume) (F b) else 0) ≤ heavyLoss)
    (hloss : (2 + 4 * (m : ENNReal)) * cutLoss + heavyLoss ≤ ENNReal.ofReal (κ⁻¹ / 2)) :
    PreparedAt N K W ω ν E B f (M + M₁ + 2) D₁ k m r T κ'
      C lev par γ j c u Q R A F := by
  rcases hc with ⟨hκ, hKκ, hC, hlayers, hdisj, hnodes⟩
  have hκ0 : 0 < κ := by linarith
  have hθ0 : 0 < θ := hκ0.trans_le hκθ
  have hκ'0 : 0 < κ' := hθ0.trans_le hθκ'
  have hN1 : 1 ≤ N k := by linarith
  have hN0 : 0 < N k := by linarith
  let μ : Fin (W k) → Measure Inc := fun w => (ν k w).prod volume
  let wt : Fin (W k) → ENNReal := fun w => ENNReal.ofReal (ω k w)
  let G₀ := commonGood γ F H
  let G := fun b => F b ∩ G₀ (γ b)
  let sat := fun b => ν k (γ b) (A b) ≤
    ENNReal.ofReal (κ' * N k ^ (-f (r (lev b))) * |(Q b).det|)
  let good := fun b => sat b ∧ μ (γ b) (F b) ≤ 2 * μ (γ b) (G b)
  have hlev (b) : lev b < m := (hnodes b).1
  have hFm (b) : MeasurableSet (F b) := by
    rcases (hnodes b).2.2.1 with ⟨_, _, _, _, _, _, _, hm, _⟩
    exact hm
  have hHm (b) : MeasurableSet (H b) := by
    rcases hH b with ⟨_, _, _, _, _, _, _, hm, _⟩
    exact hm
  have hG₀m (w) : MeasurableSet (G₀ w) := measurableSet_commonGood γ F H hFm hHm w
  have hGm (b) : MeasurableSet (G b) := (hFm b).inter (hG₀m (γ b))
  have hsel (b) (p) (hp : p ∈ F b) : p.1 ∈ A b ∧
      p.2 ∈ Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b))
        (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b)) := by
    rcases (hnodes b).2.2.1 with ⟨_, _, _, _, _, _, _, _, _, _, hsel, _⟩
    exact ⟨(hsel p hp).2.1, (hsel p hp).2.2.1⟩
  have hFfin (b) : μ (γ b) (F b) ≠ ⊤ := by
    have hsub : F b ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
      intro p hp
      rcases (hnodes b).2.2.1 with ⟨_, _, _, _, _, _, _, _, _, _, hsel, _⟩
      exact hE _ (hsel p hp).1
    letI := hν (γ b)
    have hle : μ (γ b) (F b) ≤ 1 := by
      apply (measure_mono hsub).trans_eq
      dsimp only [μ]
      rw [Measure.prod_prod]
      simp
    exact ne_top_of_le_ne_top (by norm_num) hle
  have hGfin (b) : μ (γ b) (G b) ≠ ⊤ :=
    ne_top_of_le_ne_top (hFfin b) (measure_mono inter_subset_left)
  have hparlev (b) (hb : 0 < lev b) : lev (par b) + 1 = lev b :=
    ((hnodes b).2.2.2 hb).1
  have hparμ (b) (hb : 0 < lev b) :
      lev (par b) + 1 = lev b ∧ γ (par b) = γ b ∧ F b ⊆ F (par b) := by
    rcases (hnodes b).2.2.2 hb with ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, h4⟩
  have hbudget := forest_child_budget (ν k) wt T lev par γ j A F hFm hdisj hsel hparμ
  have hmult (i) (hi : i < m) (w) (p) :
      (∑ b ∈ Finset.univ.filter (fun b => lev b = i ∧ γ b = w),
        (F b).indicator (1 : Inc → ENNReal) p) ≤ 2 := by
    let S := Finset.univ.filter (fun b => lev b = i)
    have heq (b) (hb : b ∈ S) : lev b = i := (Finset.mem_filter.mp hb).2
    have h := layer_multiplicity_le_two S γ j
      (fun b hb => by simpa only [heq b hb] using (hnodes b).2.1) A F
      (fun b hb b' hb' hne hγ hj => hdisj b b' hne ((heq b hb).trans (heq b' hb').symm) hγ hj)
      (fun b hb p hp => by simpa only [heq b hb] using hsel b p hp) w p
    simpa only [S, Finset.filter_filter] using h
  have hcoverage := common_cut_forest_cleanup μ wt lev par γ F H sat hFm hHm
    hFfin hlev hparlev hbudget hmult cutLoss heavyLoss hcut hheavy
  obtain ⟨C', emb, par', hC', hkept, hparent, hsum⟩ := enumerate_kept lev par good hparlev
  let F' : Fin C' → Set Inc := fun b => G (emb b)
  let lst' : ℕ → Fin (W k) → Obs → Finset (Fin C') := fun i w o => restrictedList emb (lst i w o)
  have hGsubH (b) : G b ⊆ H b := commonGood_subset γ F H b
  have hGfmt (b i) : fmt 7 (N k ^ (M + M₁ + 2)) D₁
      {z : Fin 7 → ℝ | ((i, fun e : Fin 6 => z e.castSucc), z 6) ∈ G b} := by
    apply format_common_selection hN hC γ F H
    · intro a i
      rcases (hnodes a).2.2.1 with ⟨_, _, _, _, _, _, _, _, hf, _⟩
      exact Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono (hf i).2
        (pow_le_pow_right₀ hN1 hM) hD
    · intro a i
      rcases hH a with ⟨_, _, _, _, _, _, _, _, hf, _⟩
      exact (hf i).2
  have hhalf (b : Fin C') : μ (γ (emb b)) (F (emb b)) ≤ 2 * μ (γ (emb b)) (G (emb b)) :=
    (kept_good (hkept b)).2
  have hinv : κ'⁻¹ ≤ κ⁻¹ / 2 := by
    calc
      _ ≤ (2 * κ)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le (by positivity : 0 < 2 * κ) hdouble
      _ = _ := by ring
  have hnewcharts (b : Fin C') : chart (N k) (M + M₁ + 2) D₁ κ' (T (lev (emb b)))
      (j (emb b) : ℝ) (r (lev (emb b))) (B k (γ (emb b))) (E k (γ (emb b)))
      (c (emb b)) (u (emb b)) (Q (emb b)) (R (emb b)) (A (emb b)) (F' b)
      (ENNReal.ofReal (N k ^ (-f (r (lev (emb b)))) * |(Q (emb b)).det| /
        ((2 : ℝ) ^ T (lev (emb b)) * κ')) ≤ μ (γ (emb b)) (F' b)) := by
    have hlarge := Submission.Obl.k4_quadratic_atlas_normalization.chart_mono hN1
      (show M₁ ≤ M + M₁ + 2 by omega) le_rfl hθ0 hθκ' (hB _).le (hH (emb b))
      (fun _ => True.intro)
    apply chart_restrict hlarge (hGsubH (emb b)) (hGm (emb b)) (hGfmt (emb b))
    have hold := (hnodes (emb b)).2.2.1
    rcases hold with ⟨_, _, _, _, _, _, _, _, _, _, _, hfloor⟩
    exact restore_chart_floor hκ0 hdouble
      (mul_nonneg (Real.rpow_pos_of_pos hN0 _).le (abs_nonneg _)) (by positivity)
      hfloor (hhalf b)
  have hnewpar (b : Fin C') (hb : 0 < lev (emb b)) :
      lev (emb (par' b)) + 1 = lev (emb b) ∧ γ (emb (par' b)) = γ (emb b) ∧
      A (emb b) ⊆ A (emb (par' b)) ∧ F' b ⊆ F' (par' b) ∧
      (j (emb (par' b)) : ℝ) / (2 : ℝ) ^ T (lev (emb (par' b))) ≤
        (j (emb b) : ℝ) / (2 : ℝ) ^ T (lev (emb b)) ∧
      ((j (emb b) : ℝ) + 1) / (2 : ℝ) ^ T (lev (emb b)) ≤
        ((j (emb (par' b)) : ℝ) + 1) / (2 : ℝ) ^ T (lev (emb (par' b))) := by
    dsimp only [F']
    rw [hparent b hb]
    rcases (hnodes (emb b)).2.2.2 hb with ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, h3, commonGood_nested γ F H h2 h4, h5, h6⟩
  have hcoreout : Core N K W ω ν E B f (M + M₁ + 2) D₁ k m r T κ' C'
      (fun b => lev (emb b)) par' (fun b => γ (emb b)) (fun b => j (emb b))
      (fun b => c (emb b)) (fun b => u (emb b)) (fun b => Q (emb b))
      (fun b => R (emb b)) (fun b => A (emb b)) F' := by
    refine ⟨hκ.trans (hκθ.trans hθκ'), hKκ.trans (hκθ.trans hθκ'), ?_, ?_, ?_, ?_⟩
    · have hcast : (C' : ℝ) ≤ C := by exact_mod_cast hC'
      exact (hcast.trans hC).trans (pow_le_pow_right₀ hN1 (by omega))
    · intro i hi
      have hc := hcoverage i hi
      have hret := Submission.Obl.k4_quadratic_atlas_normalization.retain_half_mass
        _ _ _ κ⁻¹ (by positivity) (hlayers i hi) hc hloss
      have hs := hsum (fun b => wt (γ b) * μ (γ b) (G b)) i
      change (∑ b, if lev b = i ∧ Kept lev par good b then wt (γ b) * μ (γ b) (G b) else 0) = _ at hs
      rw [hs] at hret
      exact (ENNReal.ofReal_le_ofReal hinv).trans hret
    · intro b b' hne hl hγ hj
      exact hdisj (emb b) (emb b') (fun h => hne (emb.injective h)) hl hγ hj
    · intro b
      exact ⟨hlev (emb b), (hnodes (emb b)).2.1, hnewcharts b, hnewpar b⟩
  refine ⟨C', emb, par', F', lst', hC', hcoreout, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    exact ⟨inter_subset_left, hparent b⟩
  · intro i w o
    have hcard : ((lst' i w o).card : ℝ) ≤ (lst i w o).card := by
      exact_mod_cast restrictedList_card emb (lst i w o)
    exact hcard.trans ((hlist i w o).trans hθκ')
  · intro b
    refine ⟨(kept_good (hkept b)).1, ?_⟩
    intro p hp
    have h := hH (emb b)
    rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, hknows⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hknows p (hGsubH (emb b) hp)⟩
  · intro b
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hGfin (emb b))
  · apply forest_child_budget (ν k) wt T (fun b => lev (emb b)) par'
      (fun b => γ (emb b)) (fun b => j (emb b)) (fun b => A (emb b)) F'
      (fun b => hGm (emb b))
    · exact hcoreout.2.2.2.2.1
    · intro b p hp
      rcases hnewcharts b with ⟨_, _, _, _, _, _, _, _, _, _, hs, _⟩
      exact ⟨(hs p hp).2.1, (hs p hp).2.2.1⟩
    · intro b hb
      exact ⟨(hnewpar b hb).1, (hnewpar b hb).2.1, (hnewpar b hb).2.2.2.1⟩

end Submission.Obl.k4_true_forest_own_depth_preparation
