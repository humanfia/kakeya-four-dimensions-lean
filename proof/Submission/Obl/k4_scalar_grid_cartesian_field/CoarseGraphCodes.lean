import Submission.Obl.k4_scalar_grid_cartesian_field.QuadraticGradient
import Submission.Lib.K4ListedExceptions.FrameCodes
import Submission.Lib.K4QuadraticSheets.JetBins

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MvPolynomial
open Submission.Lib.K4ListedExceptions

/-- A bounded part of a low-gradient quadratic graph has an explicit finite physical-cell cover. -/
theorem coarse_graph_code_cover {Ω : Type*}
    (S : Set Ω) (z : Ω → Fin 2 → ℝ) (x : Ω → ℝ)
    (F : MvPolynomial (Fin 2) ℝ) (hF : F.totalDegree ≤ 2)
    {δ R E H : ℝ} (hδ : 0 < δ) (_hR : 0 ≤ R) (_hE : 0 ≤ E) (hH : 0 ≤ H)
    (z₀ : Fin 2 → ℝ)
    (hbase : ∀ p ∈ S, ∀ e, |z p e - z₀ e| ≤ R)
    (hfit : ∀ p ∈ S, |x p - eval (z p) F| ≤ E * δ)
    (hgrad : ∀ p ∈ S, ∀ e, |eval (z p) (pderiv e F)| ≤ H) :
    ∃ C : Finset (Fin 3 → ℤ),
      (C.card : ℝ) ≤ (2 * (⌈R / δ⌉₊ : ℝ) + 1) ^ 2 *
        (2 * (⌈2 * E + 2 * H⌉₊ : ℝ) + 1) ∧
      ∀ p ∈ S, (fun e : Fin 3 => (⌊(![z p 0, z p 1, x p] : Fin 3 → ℝ) e / δ⌋ : ℤ)) ∈ C := by
  classical
  let baseCode : Ω → Fin 2 → ℤ := fun p e => ⌊z p e / δ⌋
  let B := integerCodeBox ⌈R / δ⌉₊ (fun e => ⌊z₀ e / δ⌋)
  let M := ⌈2 * E + 2 * H⌉₊
  let center : (Fin 2 → ℤ) → ℝ := fun q =>
    if hq : ∃ p, p ∈ S ∧ baseCode p = q then x (Classical.choose hq) else 0
  let bins : (Fin 2 → ℤ) → Finset ℤ := fun q =>
    Finset.Icc (⌊center q / δ⌋ - M) (⌊center q / δ⌋ + M)
  let pairs := B.biUnion fun q => (bins q).image (fun c => (q, c))
  let C := pairs.image (fun q => (![q.1 0, q.1 1, q.2] : Fin 3 → ℤ))
  have hbaseCode : ∀ p ∈ S, baseCode p ∈ B := by
    intro p hp
    apply floor_code_mem_integerCodeBox ⌈R / δ⌉₊ (z p) z₀ (fun _ => δ) (fun _ => hδ)
    intro e
    apply (hbase p hp e).trans
    exact (div_le_iff₀ hδ).mp (Nat.le_ceil (R / δ))
  have hpair : ∀ p ∈ S, (baseCode p, (⌊x p / δ⌋ : ℤ)) ∈ pairs := by
    intro p hp
    refine Finset.mem_biUnion.mpr ⟨baseCode p, hbaseCode p hp, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨⌊x p / δ⌋, ?_, rfl⟩
    have hex : ∃ p', p' ∈ S ∧ baseCode p' = baseCode p := ⟨p, hp, rfl⟩
    let p₀ := Classical.choose hex
    have hp₀ : p₀ ∈ S ∧ baseCode p₀ = baseCode p := Classical.choose_spec hex
    have hcenter : center (baseCode p) = x p₀ := by simp only [center, dite_eq_left hex]; rfl
    have hdiam : ∀ e, |z p e - z p₀ e| ≤ δ := by
      intro e
      exact (Submission.Lib.K4QuadraticSheets.abs_sub_lt_of_floor_eq hδ
        (congrFun hp₀.2.symm e)).le
    have hvar : |eval (z p) F - eval (z p₀) F| ≤ 2 * H * δ := by
      have h := quadratic_lipschitz_between_low_gradient_points F hF (z p) (z p₀)
        (hgrad p hp) (hgrad p₀ hp₀.1)
      apply h.trans
      have hs : |z p 0 - z p₀ 0| + |z p 1 - z p₀ 1| ≤ 2 * δ := by
        linarith [hdiam 0, hdiam 1]
      nlinarith
    have hclose : |x p - x p₀| ≤ (M : ℝ) * δ := by
      have hsum : |x p - x p₀| ≤ |x p - eval (z p) F| +
          |eval (z p) F - eval (z p₀) F| + |eval (z p₀) F - x p₀| := by
        have h₁ := abs_add_le (x p - eval (z p) F) (eval (z p) F - eval (z p₀) F)
        have h₂ := abs_add_le (x p - eval (z p₀) F) (eval (z p₀) F - x p₀)
        ring_nf at h₁ h₂ ⊢
        linarith
      rw [abs_sub_comm (eval (z p₀) F) (x p₀)] at hsum
      have hM : 2 * E + 2 * H ≤ (M : ℝ) := Nat.le_ceil _
      nlinarith [hfit p hp, hfit p₀ hp₀.1]
    have hcode := floor_code_mem_integerCodeBox M (![x p] : Fin 1 → ℝ)
      ![x p₀] (fun _ => δ) (fun _ => hδ) (by intro e; fin_cases e; exact hclose)
    have hbin := (mem_integerCodeBox M _ _).mp hcode 0
    change ⌊x p / δ⌋ ∈ bins (baseCode p)
    simp only [bins, hcenter, Finset.mem_Icc]
    simpa using hbin
  refine ⟨C, ?_, ?_⟩
  · have hbins (q : Fin 2 → ℤ) : (bins q).card = 2 * M + 1 := by
      dsimp only [bins]
      rw [Int.card_Icc]
      omega
    have hcards : pairs.card ≤ B.card * (2 * M + 1) := by
      calc
        _ ≤ ∑ q ∈ B, ((bins q).image fun c => (q, c)).card := Finset.card_biUnion_le
        _ ≤ ∑ q ∈ B, (bins q).card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
        _ = _ := by simp only [hbins, Finset.sum_const_nat]
    have hcard : C.card ≤ (2 * ⌈R / δ⌉₊ + 1) ^ 2 * (2 * M + 1) := by
      apply Finset.card_image_le.trans
      simpa only [card_integerCodeBox, B] using hcards
    exact_mod_cast hcard
  · intro p hp
    apply Finset.mem_image.mpr
    refine ⟨(baseCode p, ⌊x p / δ⌋), hpair p hp, ?_⟩
    funext e
    fin_cases e <;> rfl

/-- The physical graph cover has two-dimensional size at the original thickness. -/
theorem coarse_graph_code_cover_scaled {Ω : Type*}
    (S : Set Ω) (z : Ω → Fin 2 → ℝ) (x : Ω → ℝ)
    (F : MvPolynomial (Fin 2) ℝ) (hF : F.totalDegree ≤ 2)
    {δ h L : ℝ} (hδ : 0 < δ) (hh : 0 < h) (hL : 1 ≤ L) (hscale : δ ≤ L * h)
    (z₀ : Fin 2 → ℝ)
    (hbase : ∀ p ∈ S, ∀ e, |z p e - z₀ e| ≤ L * h)
    (hfit : ∀ p ∈ S, |x p - eval (z p) F| ≤ L * δ)
    (hgrad : ∀ p ∈ S, ∀ e, |eval (z p) (pderiv e F)| ≤ L) :
    ∃ C : Finset (Fin 3 → ℤ), (C.card : ℝ) ≤ 1000 * L ^ 3 * (h / δ) ^ 2 ∧
      ∀ p ∈ S, (fun e : Fin 3 => (⌊(![z p 0, z p 1, x p] : Fin 3 → ℝ) e / δ⌋ : ℤ)) ∈ C := by
  have hLn : 0 ≤ L := by linarith
  obtain ⟨C, hcount, hcover⟩ := coarse_graph_code_cover S z x F hF hδ
    (by positivity : 0 ≤ L * h) hLn hLn z₀ hbase hfit hgrad
  refine ⟨C, hcount.trans ?_, hcover⟩
  have hratio : 1 ≤ L * h / δ := (le_div_iff₀ hδ).mpr (by linarith)
  have hbaseCount : 2 * (⌈L * h / δ⌉₊ : ℝ) + 1 ≤ 5 * L * (h / δ) := by
    have hceil := (Nat.ceil_lt_add_one (by positivity : 0 ≤ L * h / δ)).le
    have hid : 5 * L * (h / δ) = 5 * (L * h / δ) := by ring
    rw [hid]
    linarith
  have hhiddenCount : 2 * (⌈2 * L + 2 * L⌉₊ : ℝ) + 1 ≤ 11 * L := by
    have hceil := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * L + 2 * L)).le
    linarith
  calc
    _ ≤ (5 * L * (h / δ)) ^ 2 * (11 * L) := by gcongr
    _ = 275 * L ^ 3 * (h / δ) ^ 2 := by ring
    _ ≤ 1000 * L ^ 3 * (h / δ) ^ 2 := by gcongr; norm_num

end Submission.Obl.k4_scalar_grid_cartesian_field
