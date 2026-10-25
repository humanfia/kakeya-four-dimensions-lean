-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory
open LeanEval.Analysis.WangZahlKakeya

abbrev Tube (d : ℝ) (p q : Space) : Set Space :=
  Metric.thickening d (segment ℝ p (p + q))

def KatzTao (d L : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ W, Convex ℝ W →
    ENNReal.ofReal ((Set.ncard {i | Tube d (x i) (v i) ⊆ W} : ℝ) * d ^ 2) ≤
      ENNReal.ofReal L * volume W

def Frostman (d L : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ (u : Space) (t r : ℝ), ‖u‖ = 1 → 0 < r →
    ENNReal.ofReal (Set.ncard {i | Tube d (x i) (v i) ⊆
      Metric.ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r}} : ℝ) ≤
        ENNReal.ofReal (L * n) * volume (Metric.ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r})

def Admissible (d η M L : ℝ) (n : ℕ) (x v : Fin n → Space)
    (Y : Fin n → Set Space) : Prop :=
  0 < n ∧
    (∀ i, ‖v i‖ = 1 ∧ Tube d (x i) (v i) ⊆ Metric.ball 0 1 ∧
      MeasurableSet (Y i) ∧ Y i ⊆ Tube d (x i) (v i)) ∧
    (∀ i j, i ≠ j → volume (Tube d (x i) (v i) ∩ Tube d (x j) (v j)) ≤
      1 / 2 * volume (Tube d (x i) (v i))) ∧
    ENNReal.ofReal (d ^ η * n * d ^ 2) ≤ ∑ i, volume (Y i) ∧
    KatzTao d M n x v ∧ Frostman d L n x v

def Tower (b : Bool) (d L g : ℝ) (B n : ℕ) (x v : Fin n → Space) : Prop :=
  ∃ J : ℕ, 1 ≤ J ∧ J ≤ B ∧ ∃ (r : ℕ → ℝ) (N : ℕ → ℕ)
    (y w : ∀ j, Fin (N j) → Space) (f : ∀ j, Fin (N (j + 1)) → Fin (N j)),
    r 0 = 1 ∧ r J = d ∧ N 0 = 1 ∧
    (∃ u : Fin n ≃ Fin (N J), ∀ i, y J (u i) = x i ∧ w J (u i) = v i) ∧
    (∀ j, j ≤ J → ∀ k, ‖w j k‖ = 1) ∧
    (∀ j, j < J → 0 < r (j + 1) ∧ r (j + 1) < r j ∧ d ^ g * r j ≤ r (j + 1) ∧
      ∀ i, Tube (r (j + 1)) (y (j + 1) i) (w (j + 1) i) ⊆
        Tube (r j) (y j (f j i)) (w j (f j i))) ∧
    (if b then ∀ j, j ≤ J → KatzTao (r j) L (N j) (y j) (w j)
    else ∀ j, j < J → ∀ k W, Convex ℝ W →
      ENNReal.ofReal ((Set.ncard {i | f j i = k ∧
        Tube (r (j + 1)) (y (j + 1) i) (w (j + 1) i) ⊆ W} : ℝ) * (r (j + 1)) ^ 2) ≤
          ENNReal.ofReal L * volume W)

def VolumeBound (σ ω κ α d : ℝ) (n : ℕ) (Y : Fin n → Set Space) : Prop :=
  ENNReal.ofReal (κ * d ^ (ω - α) * (n * d ^ 2) * (n * d) ^ (-σ)) ≤ volume (⋃ i, Y i)

def Endpoint (σ ω : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ m l : ℝ, 1 ≤ m → 1 ≤ l →
    ∀ n x v Y, Admissible δ η m l n x v Y →
      ENNReal.ofReal (a * δ ^ (ω + ε) * m⁻¹ * (n * δ ^ 2) *
        (m ^ (-(3 / 2 : ℝ)) * l * (n * δ)) ^ (-σ)) ≤ volume (⋃ i, Y i)

theorem KatzTao.mono {d L L' : ℝ} {n : ℕ} {x v : Fin n → Space}
    (h : KatzTao d L n x v) (hL : L ≤ L') : KatzTao d L' n x v := by
  intro W hW
  exact (h W hW).trans (by gcongr)

theorem Frostman.mono {d L L' : ℝ} {n : ℕ} {x v : Fin n → Space}
    (h : Frostman d L n x v) (hL : L ≤ L') : Frostman d L' n x v := by
  intro u t r hu hr
  exact (h u t r hu hr).trans (by gcongr)

theorem Admissible.mono {d η η' M M' L L' : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (h : Admissible d η M L n x v Y)
    (hd : 0 < d) (hd1 : d ≤ 1) (hη : η ≤ η') (hM : M ≤ M') (hL : L ≤ L') :
    Admissible d η' M' L' n x v Y := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_, h.2.2.2.2.1.mono hM, h.2.2.2.2.2.mono hL⟩
  apply le_trans (ENNReal.ofReal_le_ofReal _) h.2.2.2.1
  have hp := Real.rpow_le_rpow_of_exponent_ge hd hd1 hη
  gcongr

theorem Admissible.mono_error {d η η' : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (h : Admissible d η (d ^ (-η)) (d ^ (-η)) n x v Y)
    (hd : 0 < d) (hd1 : d ≤ 1) (hη : η ≤ η') :
    Admissible d η' (d ^ (-η')) (d ^ (-η')) n x v Y :=
  h.mono hd hd1 hη
    (Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hη))
    (Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hη))

theorem Admissible.mass_pos {d η M L : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (h : Admissible d η M L n x v Y) (hd : 0 < d) :
    0 < ∑ i, volume (Y i) := by
  apply lt_of_lt_of_le _ h.2.2.2.1
  apply ENNReal.ofReal_pos.mpr
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos hd _) (Nat.cast_pos.mpr h.1))
    (sq_pos_of_pos hd)

theorem Admissible.mass_ne_top {d η M L : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (h : Admissible d η M L n x v Y) :
    ∑ i, volume (Y i) ≠ ⊤ := by
  apply ENNReal.sum_ne_top.mpr
  intro i hi
  exact ne_top_of_le_ne_top measure_ball_ne_top
    (measure_mono ((h.2.1 i).2.2.2.trans (h.2.1 i).2.1))

theorem VolumeBound.mono {σ ω κ κ' α α' d : ℝ} {n : ℕ} {Y : Fin n → Set Space}
    (h : VolumeBound σ ω κ α d n Y) (hd : 0 < d) (hd1 : d ≤ 1)
    (hκ : 0 ≤ κ') (hκκ : κ' ≤ κ) (hα : α' ≤ α) :
    VolumeBound σ ω κ' α' d n Y := by
  apply le_trans (ENNReal.ofReal_le_ofReal _) h
  have hκnonneg : 0 ≤ κ := hκ.trans hκκ
  have hp : d ^ (ω - α') ≤ d ^ (ω - α) :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
  gcongr

end WangZahlLot.Obl.wz_multiscale_finite_tower
