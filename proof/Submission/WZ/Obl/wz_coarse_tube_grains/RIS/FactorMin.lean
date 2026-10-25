-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.FactorMin.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.FactorKT

/-!
# Step 1 of WZ Proposition 4.6: a large subfamily with a robust Katz–Tao constant

Minimising `exp[(log(#U/#U₀))²] · KT U₀` over the nonempty subfamilies `U₀ ⊆ U` gives a subfamily
with `#U ≤ e^Λ #U₀` (WZ (4.7)) whose Katz–Tao constant drops by at most `e^{-(2Λ+1)}` on every
subfamily of at least half its size (WZ (4.8)); here `Λ = √(log(384 #U))`.
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Factor

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

noncomputable section

variable {N : ℕ} {R ρ : ℝ} {y w : Fin N → Space}

/-- The logarithmic loss parameter `Λ = √(log(384 n))`. -/
def lam (n : ℕ) : ℝ := Real.sqrt (Real.log (384 * n))

theorem lam_nonneg (n : ℕ) : 0 ≤ lam n := Real.sqrt_nonneg _

theorem Fam.exists_robust (hF : Fam R ρ y w) {U : Finset (Fin N)} (hU : U.Nonempty) :
    ∃ U₀ ⊆ U, U₀.Nonempty ∧ (U.card : ℝ) ≤ Real.exp (lam U.card) * U₀.card ∧
      ∀ U'' ⊆ U₀, (U₀.card : ℝ) ≤ 2 * U''.card →
        Real.exp (-(2 * lam U.card + 1)) * KT ρ y w U₀ ≤ KT ρ y w U'' := by
  classical
  set n : ℝ := (U.card : ℝ) with hn
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast hU.card_pos
  let L : Finset (Fin N) → ℝ := fun V => Real.log (n / V.card)
  let Φ : Finset (Fin N) → ℝ := fun V => Real.exp (L V ^ 2) * KT ρ y w V
  have hcand : (U.powerset.filter Finset.Nonempty).Nonempty :=
    ⟨U, Finset.mem_filter.mpr ⟨Finset.mem_powerset_self U, hU⟩⟩
  obtain ⟨U₀, hU₀mem, hmin⟩ := Finset.exists_min_image _ Φ hcand
  obtain ⟨hU₀U, hU₀ne⟩ := Finset.mem_filter.mp hU₀mem
  rw [Finset.mem_powerset] at hU₀U
  have hn₀pos : (0 : ℝ) < U₀.card := by exact_mod_cast hU₀ne.card_pos
  have hn₀le : (U₀.card : ℝ) ≤ n := by rw [hn]; exact_mod_cast Finset.card_le_card hU₀U
  have hL₀nonneg : 0 ≤ L U₀ := Real.log_nonneg (by rw [le_div_iff₀ hn₀pos]; linarith)
  -- (4.7)
  have hΦU : Φ U = KT ρ y w U := by
    simp only [Φ, L, ← hn, div_self hnpos.ne', Real.log_one]
    norm_num
  have hΦ₀ : Φ U₀ ≤ n := by
    have := hmin U (Finset.mem_filter.mpr ⟨Finset.mem_powerset_self U, hU⟩)
    rw [hΦU] at this
    exact this.trans (hF.KT_upper U)
  have hexpL : Real.exp (L U₀ ^ 2) ≤ 384 * n := by
    have hKT := hF.KT_lower hU₀ne
    have hpos := Real.exp_pos (L U₀ ^ 2)
    have : Real.exp (L U₀ ^ 2) * (1 / 384) ≤ Φ U₀ := by
      simp only [Φ]; gcongr
    linarith
  have hL₀ : L U₀ ≤ lam U.card := by
    have h1 : L U₀ ^ 2 ≤ Real.log (384 * n) := by
      rw [← Real.exp_le_exp, Real.exp_log (by positivity)]
      exact hexpL
    rw [lam, ← hn]
    exact Real.le_sqrt_of_sq_le h1
  refine ⟨U₀, hU₀U, hU₀ne, ?_, ?_⟩
  · have h1 : n / U₀.card ≤ Real.exp (lam U.card) := by
      rw [← Real.exp_log (by positivity : 0 < n / U₀.card)]
      exact Real.exp_le_exp.mpr hL₀
    rw [div_le_iff₀ hn₀pos] at h1
    linarith
  · -- (4.8)
    intro U'' hU'' hhalf
    have hn''pos : (0 : ℝ) < U''.card := by
      have : (0 : ℝ) < 2 * U''.card := hn₀pos.trans_le hhalf
      linarith
    have hU''ne : U''.Nonempty := Finset.card_pos.mp (by exact_mod_cast hn''pos)
    have hn''le : (U''.card : ℝ) ≤ U₀.card := by exact_mod_cast Finset.card_le_card hU''
    have hmin'' := hmin U'' (Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (hU''.trans hU₀U), hU''ne⟩)
    have hL''lo : L U₀ ≤ L U'' := by
      apply Real.log_le_log (by positivity)
      exact div_le_div_of_nonneg_left hnpos.le hn''pos hn''le
    have hL''hi : L U'' ≤ L U₀ + Real.log 2 := by
      have h2 : n / U''.card ≤ 2 * (n / U₀.card) := by
        rw [div_le_iff₀ hn''pos]
        rw [show 2 * (n / U₀.card) * U''.card = n * (2 * U''.card) / U₀.card by ring]
        rw [le_div_iff₀ hn₀pos]
        nlinarith
      calc L U'' = Real.log (n / U''.card) := rfl
        _ ≤ Real.log (2 * (n / U₀.card)) := Real.log_le_log (by positivity) h2
        _ = Real.log 2 + L U₀ := by rw [Real.log_mul (by norm_num) (by positivity)]
        _ = L U₀ + Real.log 2 := by ring
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hlog2' : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hsq : L U'' ^ 2 ≤ L U₀ ^ 2 + (2 * lam U.card + 1) := by
      have h3 : L U'' ^ 2 ≤ (L U₀ + Real.log 2) ^ 2 := by
        have : 0 ≤ L U'' := hL₀nonneg.trans hL''lo
        nlinarith
      nlinarith [lam_nonneg U.card]
    -- `Φ U₀ ≤ Φ U''`
    have hKT0 := KT_nonneg (ρ := ρ) (y := y) (w := w) U₀
    have hKT'' := KT_nonneg (ρ := ρ) (y := y) (w := w) U''
    have key : Real.exp (L U₀ ^ 2) * KT ρ y w U₀ ≤ Real.exp (L U'' ^ 2) * KT ρ y w U'' :=
      hmin''
    have hexp : Real.exp (L U'' ^ 2) ≤ Real.exp (L U₀ ^ 2) * Real.exp (2 * lam U.card + 1) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr hsq
    have hpos₀ := Real.exp_pos (L U₀ ^ 2)
    have hposl := Real.exp_pos (2 * lam U.card + 1)
    rw [Real.exp_neg]
    rw [inv_mul_le_iff₀ hposl]
    have : Real.exp (L U₀ ^ 2) * KT ρ y w U₀ ≤
        Real.exp (L U₀ ^ 2) * (Real.exp (2 * lam U.card + 1) * KT ρ y w U'') := by
      calc Real.exp (L U₀ ^ 2) * KT ρ y w U₀ ≤ Real.exp (L U'' ^ 2) * KT ρ y w U'' := key
        _ ≤ Real.exp (L U₀ ^ 2) * Real.exp (2 * lam U.card + 1) * KT ρ y w U'' := by gcongr
        _ = _ := by ring
    exact le_of_mul_le_mul_left this hpos₀

end

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Factor
