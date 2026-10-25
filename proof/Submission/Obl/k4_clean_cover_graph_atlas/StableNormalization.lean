-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/StableNormalization.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.LocalSheets
import Submission.Obl.k4_clean_cover_graph_atlas.PolynomialRemez

namespace Submission.Obl.k4_clean_cover_graph_atlas

open Set Metric MvPolynomial

noncomputable def quadraticRelation (a : ℂ) (b c : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial (Fin 4) ℂ :=
  C a * X (Fin.last 3) ^ 2 + rename Fin.castSucc b * X (Fin.last 3) + rename Fin.castSucc c

theorem eval_quadraticRelation (a : ℂ) (b c : MvPolynomial (Fin 3) ℂ)
    (z : Fin 3 → ℂ) (w : ℂ) :
    eval (Fin.snoc z w) (quadraticRelation a b c) = a * w ^ 2 + eval z b * w + eval z c := by
  simp only [quadraticRelation, map_add, map_mul, map_pow, eval_C, eval_X,
    Fin.snoc_last, MvPolynomial.eval_rename, Function.comp_def, Fin.snoc_castSucc]

theorem quadraticRelation_degree (a : ℂ) (b c : MvPolynomial (Fin 3) ℂ)
    (hb : b.totalDegree ≤ 1) (hc : c.totalDegree ≤ 2) :
    (quadraticRelation a b c).totalDegree ≤ 2 := by
  have hX : (X (Fin.last 3) : MvPolynomial (Fin 4) ℂ).totalDegree ≤ 1 := by simp
  have h1 : (C a * (X (Fin.last 3) : MvPolynomial (Fin 4) ℂ) ^ 2).totalDegree ≤ 2 := by
    have hh := (totalDegree_mul (C a) ((X (Fin.last 3) : MvPolynomial (Fin 4) ℂ) ^ 2)).trans
      (add_le_add le_rfl (totalDegree_pow _ 2))
    simp only [totalDegree_C, zero_add] at hh
    exact hh.trans (by omega)
  have h2 : (rename Fin.castSucc b * (X (Fin.last 3) : MvPolynomial (Fin 4) ℂ)).totalDegree ≤ 2 := by
    exact (totalDegree_mul _ _).trans (by
      have hh := (totalDegree_rename_le Fin.castSucc b).trans hb
      omega)
  have h3 : (rename Fin.castSucc c : MvPolynomial (Fin 4) ℂ).totalDegree ≤ 2 :=
    (totalDegree_rename_le _ c).trans hc
  exact (totalDegree_add _ _).trans
    (max_le ((totalDegree_add _ _).trans (max_le h1 h2)) h3)

theorem quadraticRelation_ne_zero_of_slope (a : ℂ) (b c : MvPolynomial (Fin 3) ℂ)
    (z : Fin 3 → ℂ) (w : ℂ) (hs : 2 * a * w + eval z b ≠ 0) :
    quadraticRelation a b c ≠ 0 := by
  intro hz
  have hp := congrArg (eval (Fin.snoc z (w + 1))) hz
  have hm := congrArg (eval (Fin.snoc z (w - 1))) hz
  rw [eval_quadraticRelation, map_zero] at hp hm
  apply hs
  linear_combination (1 / 2 : ℂ) * hp - (1 / 2 : ℂ) * hm

/-- Stable hidden sheets yield genuine bounded-degree real sheets on the fixed
comparison domain, retaining their original root equation and fitting estimate. -/
theorem exists_stable_normalized_sheet (h : stableSheets) :
    ∃ C : ℕ, 20 ≤ C ∧ ∀ A a_fit a : ℝ, 2 ≤ A → 0 < a_fit →
      ∀ b c : MvPolynomial (Fin 3) ℝ, b.totalDegree ≤ 1 → c.totalDegree ≤ 2 →
      (∀ e, |(b * b - MvPolynomial.C (4 * a) * c).coeff e| ≤ A) →
      |a| * a_fit ≤ A ^ (-20 : ℝ) →
      ∀ (u0 : Real3) (w0 : ℝ), ‖u0‖ ≤ A →
        |a * w0 ^ 2 + eval (fun j => u0 j) b * w0 + eval (fun j => u0 j) c| ≤ a_fit * A →
        A ^ (-1 : ℝ) ≤ |2 * a * w0 + eval (fun j => u0 j) b| →
        |2 * a * w0 + eval (fun j => u0 j) b| ≤ A →
        ∃ F : RealSheet 2, ∀ x : Real3, ‖x‖ ≤ 1 →
          let u := u0 + (A ^ (-(C : ℝ)) / 8) • x
          let w := (F.f (emb x)).re
          (a * w ^ 2 + eval (fun j => u j) b * w + eval (fun j => u j) c = 0) ∧
          A ^ (-(C : ℝ)) ≤ |2 * a * w + eval (fun j => u j) b| ∧
          |2 * a * w + eval (fun j => u j) b| ≤ A ^ (C : ℝ) ∧
          0 < (2 * a * w + eval (fun j => u j) b) * (2 * a * w0 + eval (fun j => u0 j) b) ∧
          ∀ v : ℝ, |a * v ^ 2 + eval (fun j => u j) b * v + eval (fun j => u j) c| ≤ a_fit * A →
            0 < (2 * a * v + eval (fun j => u j) b) * (2 * a * w0 + eval (fun j => u0 j) b) →
            |v - w| ≤ a_fit * A ^ (C : ℝ) := by
  obtain ⟨C, hC, hstable⟩ := h
  refine ⟨C, hC, ?_⟩
  intro A a_fit a hA ha_fit b c hb hc hcoeff ha u0 w0 hu0 hvalue hslo hshi
  have hApos : 0 < A := by linarith
  let r := A ^ (-(C : ℝ))
  have hr : 0 < r := Real.rpow_pos_of_pos hApos _
  obtain ⟨f, hf, heq, hreal, hfit⟩ :=
    hstable A a_fit a hA ha_fit b c hb hc hcoeff ha u0 w0 hu0 hvalue hslo hshi
  let Q := quadraticRelation (a : ℂ) (b.map (algebraMap ℝ ℂ)) (c.map (algebraMap ℝ ℂ))
  have hsne : 2 * a * w0 + eval (fun j => u0 j) b ≠ 0 :=
    abs_pos.mp ((Real.rpow_pos_of_pos hApos (-1)).trans_le hslo)
  have hsC : 2 * (a : ℂ) * (w0 : ℂ) +
      eval (fun j : Fin 3 => (emb u0) j) (b.map (algebraMap ℝ ℂ)) ≠ 0 := by
    change 2 * (a : ℂ) * (w0 : ℂ) +
      eval (fun j : Fin 3 => (u0 j : ℂ)) (b.map (algebraMap ℝ ℂ)) ≠ 0
    rw [complex_eval_real b u0]
    exact_mod_cast hsne
  have hQ : Q ≠ 0 := quadraticRelation_ne_zero_of_slope _ _ _ _ _ hsC
  have hQD : Q.totalDegree ≤ 2 := quadraticRelation_degree _ _ _
    ((totalDegree_map_le _ b).trans hb) ((totalDegree_map_le _ c).trans hc)
  have heqQ (z : Complex3) (hz : z ∈ ball (emb u0) r) :
      eval (Fin.snoc (fun j : Fin 3 => z j) (f z)) Q = 0 := by
    rw [eval_quadraticRelation, eval_map, eval_map]
    exact heq z hz
  let F := localRealSheet u0 r hr f Q hQ hQD hf heqQ (fun x hx => (hreal x hx).1)
  have hF (z : Complex3) : F.f z = f (emb u0 + ((r / 8 : ℝ) : ℂ) • z) := rfl
  refine ⟨F, ?_⟩
  intro x hx
  let u := u0 + (r / 8) • x
  have hu : ‖u - u0‖ < r := by
    have hh : ‖u - u0‖ = (r / 8) * ‖x‖ := by
      simp only [u, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < r / 8)]
    rw [hh]
    have hmul := mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ r / 8)
    linarith
  have hFx : F.f (emb x) = f (emb u) := by
    rw [hF, ← Submission.Obl.k4_algebraic_real_jet_comparison.realEmbedding_line]
  obtain ⟨hreal_u, hlo, hhi, hsign⟩ := hreal u hu
  change (f (emb u)).im = 0 at hreal_u
  have hroot : a * (f (emb u)).re ^ 2 + eval (fun j => u j) b * (f (emb u)).re +
      eval (fun j => u j) c = 0 := by
    have hz : emb u ∈ ball (emb u0) r := by
      rw [mem_ball, dist_eq_norm, ← map_sub, emb.norm_map]
      exact hu
    have hbC : eval₂ (algebraMap ℝ ℂ) (fun j : Fin 3 => (emb u) j) b =
        (eval (fun j => u j) b : ℂ) := by
      change eval₂ (algebraMap ℝ ℂ) (fun j : Fin 3 => (u j : ℂ)) b = _
      simpa only [eval_map] using complex_eval_real b u
    have hcC : eval₂ (algebraMap ℝ ℂ) (fun j : Fin 3 => (emb u) j) c =
        (eval (fun j => u j) c : ℂ) := by
      change eval₂ (algebraMap ℝ ℂ) (fun j : Fin 3 => (u j : ℂ)) c = _
      simpa only [eval_map] using complex_eval_real c u
    have hfC : f (emb u) = ((f (emb u)).re : ℂ) := by
      apply Complex.ext <;> simp [hreal_u]
    have hh := heq (emb u) hz
    rw [hbC, hcC, hfC] at hh
    exact_mod_cast hh
  change (a * (F.f (emb x)).re ^ 2 + eval (fun j => u j) b * (F.f (emb x)).re +
      eval (fun j => u j) c = 0) ∧ _
  rw [hFx]
  exact ⟨hroot, hlo, hhi, hsign, fun v hv hs => hfit u v hu hv hs⟩

end Submission.Obl.k4_clean_cover_graph_atlas
