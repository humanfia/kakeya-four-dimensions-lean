-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.LineMarkov, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/LineMarkov.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/LineMarkov.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_eligibility_sign_description.Families
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Path
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Interface

/-!
# Markov's inequality along an old packet's lines

A quadratic bounded by `M` on an interval of length `L` is `8M/L`-Lipschitz there
(three-point interpolation of its derivative at the two endpoints). Along every line
assigned to a packet, the frozen chart bound `|R(x l t)| ≤ κ δ` holds on the whole
dyadic time block, so the packet's normalized signal `R/δ` moves at speed at most
`8 κ 2^T` in physical time on that block.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set

noncomputable section

/-- **Markov for quadratics.** -/
theorem quadratic_lipschitz_of_bound {f : ℝ → ℝ}
    (hf : k4_eligibility_sign_description.Quadratic f) {a L M : ℝ} (hL : 0 < L)
    (hM : ∀ t ∈ Icc a (a + L), |f t| ≤ M) {s t : ℝ}
    (hs : s ∈ Icc a (a + L)) (ht : t ∈ Icc a (a + L)) :
    |f s - f t| ≤ 8 * M / L * |s - t| := by
  obtain ⟨A, B, C, hfe⟩ := hf
  have h0 := abs_le.mp (hM a ⟨le_rfl, by linarith⟩)
  have h1 := abs_le.mp (hM (a + L / 2) ⟨by linarith, by linarith⟩)
  have h2 := abs_le.mp (hM (a + L) ⟨by linarith, le_rfl⟩)
  have e1 : (2 * A * a + B) * L = -3 * f a + 4 * f (a + L / 2) - f (a + L) := by
    rw [hfe, hfe, hfe]; ring
  have e2 : (2 * A * (a + L) + B) * L = f a - 4 * f (a + L / 2) + 3 * f (a + L) := by
    rw [hfe, hfe, hfe]; ring
  have b1 : |2 * A * a + B| ≤ 8 * M / L := by
    have hh : |(2 * A * a + B) * L| ≤ 8 * M := by
      rw [e1, abs_le]; constructor <;> linarith
    rw [abs_mul, abs_of_pos hL] at hh
    exact (le_div_iff₀ hL).mpr hh
  have b2 : |2 * A * (a + L) + B| ≤ 8 * M / L := by
    have hh : |(2 * A * (a + L) + B) * L| ≤ 8 * M := by
      rw [e2, abs_le]; constructor <;> linarith
    rw [abs_mul, abs_of_pos hL] at hh
    exact (le_div_iff₀ hL).mpr hh
  have hfst : f s - f t = (s - t) * (2 * A * ((s + t) / 2) + B) := by
    rw [hfe, hfe]; ring
  have hu1 : a ≤ (s + t) / 2 := by linarith [hs.1, ht.1]
  have hu2 : (s + t) / 2 ≤ a + L := by linarith [hs.2, ht.2]
  have hmid : |2 * A * ((s + t) / 2) + B| ≤ 8 * M / L := by
    obtain ⟨l1, r1⟩ := abs_le.mp b1
    obtain ⟨l2, r2⟩ := abs_le.mp b2
    have d1 : 2 * A * ((s + t) / 2) + B - (2 * A * a + B) = 2 * A * ((s + t) / 2 - a) := by ring
    have d2 : 2 * A * (a + L) + B - (2 * A * ((s + t) / 2) + B) =
        2 * A * (a + L - (s + t) / 2) := by ring
    rw [abs_le]
    rcases le_total 0 A with hA | hA
    · have p1 : 0 ≤ 2 * A * ((s + t) / 2 - a) := by
        apply mul_nonneg (by linarith) (by linarith)
      have p2 : 0 ≤ 2 * A * (a + L - (s + t) / 2) := by
        apply mul_nonneg (by linarith) (by linarith)
      constructor <;> linarith
    · have p1 : 2 * A * ((s + t) / 2 - a) ≤ 0 := by
        apply mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      have p2 : 2 * A * (a + L - (s + t) / 2) ≤ 0 := by
        apply mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      constructor <;> linarith
  rw [hfst, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right hmid (abs_nonneg _)

/-- Polynomials of degree at most two are quadratic along every line. -/
theorem quadratic_eval_xp (S : MvPolynomial (Fin 4) ℝ) (hS : S.totalDegree ≤ 2)
    (l : ℕ × (Fin 6 → ℝ)) :
    k4_eligibility_sign_description.Quadratic (fun t => MvPolynomial.eval (xp l t) S) := by
  have h := k4_eligibility_sign_description.Quadratic.mv_line S hS
    ![0, l.2 0, l.2 1, l.2 2] ![1, l.2 3, l.2 4, l.2 5]
  have heq (t : ℝ) : xp l t =
      (fun i => ![0, l.2 0, l.2 1, l.2 2] i + t * ![1, l.2 3, l.2 4, l.2 5] i) := by
    ext j
    fin_cases j <;> simp [xp]
  simpa only [← heq] using h

section Path

variable {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}

/-- **The old signal along an old line.** On the old block, `R_old/δ_old` moves at
speed at most `8 κ 2^T` in physical time. -/
theorem Native.PathData.Valid.old_signal_line_lipschitz
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (old : Fin p.C)
    {l : ℕ × (Fin 6 → ℝ)} (hl : l ∈ p.A old) {t₁ t₂ : ℝ}
    (ht₁ : t₁ ∈ Icc ((p.j old : ℝ) / (2 : ℝ) ^ p.T (p.lev old))
      (((p.j old : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev old)))
    (ht₂ : t₂ ∈ Icc ((p.j old : ℝ) / (2 : ℝ) ^ p.T (p.lev old))
      (((p.j old : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev old))) :
    |MvPolynomial.eval (xp l t₁) (p.R old) / δ Nk (p.r (p.lev old)) -
        MvPolynomial.eval (xp l t₂) (p.R old) / δ Nk (p.r (p.lev old))| ≤
      8 * p.κ * (2 : ℝ) ^ p.T (p.lev old) * |t₁ - t₂| := by
  obtain ⟨-, -, hch⟩ := hp.2.2.2.2.2.2.2 old
  obtain ⟨_, _, _, _, hdeg, _, _, _, _, hlines, _⟩ := hch
  have hδ : 0 < δ Nk (p.r (p.lev old)) := by unfold δ; positivity
  have hT : (0 : ℝ) < (2 : ℝ) ^ p.T (p.lev old) := by positivity
  let a : ℝ := (p.j old : ℝ) / (2 : ℝ) ^ p.T (p.lev old)
  let Lb : ℝ := ((2 : ℝ) ^ p.T (p.lev old))⁻¹
  have hLb : 0 < Lb := by dsimp only [Lb]; positivity
  have hblock : Icc ((p.j old : ℝ) / (2 : ℝ) ^ p.T (p.lev old))
      (((p.j old : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev old)) = Icc a (a + Lb) := by
    congr 1
    dsimp only [a, Lb]
    field_simp
  rw [hblock] at ht₁ ht₂
  have hbound : ∀ t ∈ Icc a (a + Lb),
      |MvPolynomial.eval (xp l t) (p.R old)| ≤ p.κ * δ Nk (p.r (p.lev old)) := by
    intro t ht
    rw [← hblock] at ht
    exact ((hlines l hl).2.2 t ht).2.1
  have hq := quadratic_lipschitz_of_bound (quadratic_eval_xp (p.R old) hdeg l) hLb hbound
    ht₁ ht₂
  rw [← sub_div, abs_div, abs_of_pos hδ, div_le_iff₀ hδ]
  calc
    _ ≤ 8 * (p.κ * δ Nk (p.r (p.lev old))) / Lb * |t₁ - t₂| := hq
    _ = _ := by dsimp only [Lb]; field_simp

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
