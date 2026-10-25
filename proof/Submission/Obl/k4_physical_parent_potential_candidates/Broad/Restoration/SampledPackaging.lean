-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/SampledPackaging.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/SampledPackaging.lean (session x0945).
-- Existing source attributions are preserved below.

import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.BranchBand
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.Analytic.Expanded

/-!
# Packaging the sampled certificate in the frozen coordinates

`rawSampledCandidate_of_group_points` turns the analytic certificate (`RawBranchData`) of a
branch `f` of the native equation `a w² + B(z) w + C(z) = 0`, together with group lines and
counted incidences whose normalized points are *native group points* (small native fit,
hidden derivative in a window, the branch's sign), into the frozen sampled alternative
`RawSampledCandidate`. Every normalized point is put in the branch tube by `band_of_native_fit`.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open Metric Set MeasureTheory MvPolynomial

/-- A physical point whose normalized image lies on the group's native sheet: it is in the
unit ball, the native fit `S0 - P0` is at most `εfit`, and the hidden derivative has the
branch's sign and size between `A₁⁻¹` and `A₁`. -/
def NativeGroupPoint (c : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (B : ℝ) (S0 : Poly)
    (P0 : MvPolynomial (Fin 3) ℝ) (εfit A₁ σ : ℝ) (x : Fin 4 → ℝ) : Prop :=
  (pointOfCoordinates (coordinateMap c M B x)).1 ∈ closedBall (0 : Base) 1 ∧
  |eval (coordinateMap c M B x) S0 -
    eval (fun i => coordinateMap c M B x i.castSucc) P0| ≤ εfit ∧
  0 < eval (coordinateMap c M B x) (pderiv 3 S0) * σ ∧
  A₁⁻¹ ≤ |eval (coordinateMap c M B x) (pderiv 3 S0)| ∧
  |eval (coordinateMap c M B x) (pderiv 3 S0)| ≤ A₁

/-- A native group point lies in the frozen region of the branch. -/
theorem mem_rawRegion_of_nativeGroupPoint {c : Fin 3 → ℝ} {M : Matrix (Fin 3) (Fin 3) ℝ}
    {B : ℝ} {S0 : Poly} {P0 : MvPolynomial (Fin 3) ℝ} {εfit A₁ σ A0 b0 a : ℝ}
    {Bδ Cδ : MvPolynomial (Fin 3) ℝ} {f : Base → ℝ}
    (hA₁ : 2 ≤ A₁) (hA₁A0 : A₁ ≤ A0) (hε : 0 < εfit) (hband : εfit * A₁ ^ 19 ≤ A0 * b0)
    (hsmall : 4 * |a| * εfit ≤ (2 * A₁ ^ 2)⁻¹)
    (hroot : ∀ z ∈ ball (0 : Base) 4, a * (f z) ^ 2 + eval (fun i => z i) Bδ * f z +
      eval (fun i => z i) Cδ = 0 ∧ 0 < (2 * a * f z + eval (fun i => z i) Bδ) * σ)
    (hSeq : ∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] S0 - eval (fun i => z i) P0 =
      a * w ^ 2 + eval (fun i => z i) Bδ * w + eval (fun i => z i) Cδ)
    (hSd : ∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] (pderiv 3 S0) =
      2 * a * w + eval (fun i => z i) Bδ)
    {x : Fin 4 → ℝ} (hx : NativeGroupPoint c M B S0 P0 εfit A₁ σ x) :
    pointOfCoordinates (coordinateMap c M B x) ∈ rawRegion A0 b0 S0 f := by
  obtain ⟨hball, hfit, hsign, hlo, hhi⟩ := hx
  set y := coordinateMap c M B x with hy
  set z := (pointOfCoordinates y).1 with hz
  set w := (pointOfCoordinates y).2 with hw
  have hcoords : ![z 0, z 1, z 2, w] = y := coordinates_pointOfCoordinates y
  have hzcast : (fun i : Fin 3 => z i) = fun i => y i.castSucc := by
    funext i
    simp [hz, pointOfCoordinates]
  have hz4 : z ∈ ball (0 : Base) 4 :=
    closedBall_subset_ball (by norm_num) hball
  obtain ⟨hr, hrs⟩ := hroot z hz4
  have hfit' : |a * w ^ 2 + eval (fun i => z i) Bδ * w + eval (fun i => z i) Cδ| ≤ εfit := by
    rw [← hSeq z w, hcoords, hzcast]
    exact hfit
  have hder : eval ![z 0, z 1, z 2, w] (pderiv 3 S0) = eval y (pderiv 3 S0) := by
    rw [hcoords]
  have hwsign : 0 < (2 * a * w + eval (fun i => z i) Bδ) * σ := by
    rw [← hSd z w, hder]
    exact hsign
  have hlo' : A₁⁻¹ ≤ |2 * a * w + eval (fun i => z i) Bδ| := by
    rw [← hSd z w, hder]; exact hlo
  have hhi' : |2 * a * w + eval (fun i => z i) Bδ| ≤ A₁ := by
    rw [← hSd z w, hder]; exact hhi
  obtain ⟨hdist, -, -⟩ := band_of_native_fit hA₁ hε hr hrs hfit' hwsign hlo' hhi' hsmall
  have hA₁0 : 0 < A₁ := by linarith
  refine ⟨hball, hdist.trans hband, ?_, ?_⟩
  · rw [hder]
    exact (inv_anti₀ hA₁0 hA₁A0).trans hlo
  · rw [hder]
    exact hhi.trans hA₁A0

/-- The frozen sampled alternative from the analytic certificate and native group points. -/
theorem rawSampledCandidate_of_group_points {Cloc J Dr : ℕ} {Nk L : ℝ} {W : ℕ}
    {ν : Fin W → Measure Line} {B : Fin W → ℝ} {Mc : ℕ} {d₁ ρ gain ε : ℝ}
    {r : ℕ → ℝ} {T : ℕ → ℕ} {C : ℕ} {lev : Fin C → ℕ} {γ : Fin C → Fin W}
    {j : Fin C → ℕ} {A : Fin C → Set Line} {H : Fin W → Set Event}
    (b : Fin C) (ag : ℝ) (hg : gain ≤ ag) (hg8 : ag ≤ 1 / 8)
    (hroom : r (lev b) + 2 * ag * L ≤ L) (hBpos : 0 < B (γ b))
    (Mz MH : ℕ) (A0 Z a0 b0 h0 s0 : ℝ) (S0 : Poly) (f0 : Base → ℝ) (p0 : Fin 7 → Base)
    (E0 : Set Base) (hraw : RawBranchData Cloc J Dr A0 Z a0 b0 h0 s0 S0 f0 p0 E0)
    (c : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hformat : Mz * Cloc + 2 * MH + 11 ≤ Mc) (hZ : Z ≤ Nk ^ Mz)
    (hc : ∀ i, |c i| ≤ Nk ^ MH) (hM : ∀ i k, |M i k| ≤ Nk ^ MH) (hBsize : |B (γ b)| ≤ Nk ^ MH)
    (hb0 : b0 = dyadicThickness Nk (r (lev b) + ag * L))
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hbudget : restorationRemezFactor η * (A0 ^ (J + 1)) ^ Cloc ≤ Nk ^ (ρ * gain * L + ε))
    (P0 : MvPolynomial (Fin 3) ℝ) (a : ℝ) (Bδ Cδ : MvPolynomial (Fin 3) ℝ) (σ εfit A₁ : ℝ)
    (hA₁ : 2 ≤ A₁) (hA₁A0 : A₁ ≤ A0) (hε : 0 < εfit) (hband : εfit * A₁ ^ 19 ≤ A0 * b0)
    (hsmall : 4 * |a| * εfit ≤ (2 * A₁ ^ 2)⁻¹)
    (hroot : ∀ z ∈ ball (0 : Base) 4, a * (f0 z) ^ 2 + eval (fun i => z i) Bδ * f0 z +
      eval (fun i => z i) Cδ = 0 ∧ 0 < (2 * a * f0 z + eval (fun i => z i) Bδ) * σ)
    (hSeq : ∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] S0 - eval (fun i => z i) P0 =
      a * w ^ 2 + eval (fun i => z i) Bδ * w + eval (fun i => z i) Cδ)
    (hSd : ∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] (pderiv 3 S0) =
      2 * a * w + eval (fun i => z i) Bδ)
    (A' : Set Line) (hA'm : MeasurableSet A') (hA'b : A' ⊆ A b) (S : Line → Set ℝ)
    (hS : ∀ l ∈ A', S l ⊆ Icc (0 : ℝ) 1 ∧ ENNReal.ofReal η ≤ volume (S l))
    (hwit : ∀ l ∈ A', ∀ t ∈ S l, NativeGroupPoint c M (B (γ b)) S0 P0 εfit A₁ σ
      (graphPoint l ((j b : ℝ) / (2 : ℝ) ^ T (lev b) + ((2 : ℝ) ^ T (lev b))⁻¹ * t)))
    (counted : Set Event)
    (hcounted : counted ⊆ {p | p ∈ H (γ b) ∧ p.1 ∈ A' ∧
      p.2 ∈ Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b)) (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b)) ∧
      NativeGroupPoint c M (B (γ b)) S0 P0 εfit A₁ σ (graphPoint p.1 p.2)})
    (hmass : ENNReal.ofReal (Nk ^ (-((d₁ * ag + ρ * gain) * L) - ε) /
        (2 : ℝ) ^ T (lev b)) * ν (γ b) (A b) ≤ ((ν (γ b)).prod volume) counted) :
    RawSampledCandidate Cloc J Dr Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H := by
  have hregion : ∀ {x : Fin 4 → ℝ}, NativeGroupPoint c M (B (γ b)) S0 P0 εfit A₁ σ x →
      pointOfCoordinates (coordinateMap c M (B (γ b)) x) ∈ rawRegion A0 b0 S0 f0 :=
    fun hx => mem_rawRegion_of_nativeGroupPoint hA₁ hA₁A0 hε hband hsmall hroot hSeq hSd hx
  refine ⟨b, ag, Mz, MH, A0, Z, a0, b0, h0, s0, S0, f0, p0, E0, c, M, η, A', S, counted,
    hraw, hg, hg8, hroom, hBpos, hη, hη1, hformat, hZ, hc, hM, hBsize, hb0, hbudget, hA'm, hA'b,
    hS, fun l hl t ht => hregion (hwit l hl t ht), ?_, hmass⟩
  intro p hp
  obtain ⟨hpH, hpA, hpt, hpg⟩ := hcounted hp
  exact ⟨hpH, hpA, hpt, hregion hpg⟩

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open Metric Set MeasureTheory MvPolynomial

/-- A physical native group point whose normalized image also lies in the window of the
certificate's test `Sc`. -/
def CertifiedNativeGroupPoint (c : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (B : ℝ)
    (S0 : Poly) (P0 : MvPolynomial (Fin 3) ℝ) (Sc : Poly) (εfit A₁ σ : ℝ) (x : Fin 4 → ℝ) :
    Prop :=
  NativeGroupPoint c M B S0 P0 εfit A₁ σ x ∧
  A₁⁻¹ ≤ |eval (coordinateMap c M B x) (pderiv 3 Sc)| ∧
  |eval (coordinateMap c M B x) (pderiv 3 Sc)| ≤ A₁

/-- A certified native group point lies in the frozen region of the certificate's test. -/
theorem mem_rawRegion_of_certified {c : Fin 3 → ℝ} {M : Matrix (Fin 3) (Fin 3) ℝ}
    {B : ℝ} {S0 : Poly} {P0 : MvPolynomial (Fin 3) ℝ} {Sc : Poly} {εfit A₁ σ A0 b0 a : ℝ}
    {Bδ Cδ : MvPolynomial (Fin 3) ℝ} {f : Base → ℝ}
    (hA₁ : 2 ≤ A₁) (hA₁A0 : A₁ ≤ A0) (hε : 0 < εfit) (hband : εfit * A₁ ^ 19 ≤ A0 * b0)
    (hsmall : 4 * |a| * εfit ≤ (2 * A₁ ^ 2)⁻¹)
    (hroot : ∀ z ∈ ball (0 : Base) 4, a * (f z) ^ 2 + eval (fun i => z i) Bδ * f z +
      eval (fun i => z i) Cδ = 0 ∧ 0 < (2 * a * f z + eval (fun i => z i) Bδ) * σ)
    (hSeq : ∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] S0 - eval (fun i => z i) P0 =
      a * w ^ 2 + eval (fun i => z i) Bδ * w + eval (fun i => z i) Cδ)
    (hSd : ∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] (pderiv 3 S0) =
      2 * a * w + eval (fun i => z i) Bδ)
    {x : Fin 4 → ℝ} (hx : CertifiedNativeGroupPoint c M B S0 P0 Sc εfit A₁ σ x) :
    pointOfCoordinates (coordinateMap c M B x) ∈ rawRegion A0 b0 Sc f := by
  obtain ⟨hx0, hlo, hhi⟩ := hx
  have hmem := mem_rawRegion_of_nativeGroupPoint hA₁ hA₁A0 hε hband hsmall hroot hSeq hSd hx0
  obtain ⟨hball, hdist, -, -⟩ := hmem
  have hcoords := coordinates_pointOfCoordinates (coordinateMap c M B x)
  have hA₁0 : 0 < A₁ := by linarith
  refine ⟨hball, hdist, ?_, ?_⟩
  · rw [hcoords]
    exact (inv_anti₀ hA₁0 hA₁A0).trans hlo
  · rw [hcoords]
    exact hhi.trans hA₁A0

/-- The frozen sampled alternative with a certificate test `Sc` separate from the branch
equation `S0 - P0`. -/
theorem rawSampledCandidate_of_certified_points {Cloc J Dr : ℕ} {Nk L : ℝ} {W : ℕ}
    {ν : Fin W → Measure Line} {B : Fin W → ℝ} {Mc : ℕ} {d₁ ρ gain ε : ℝ}
    {r : ℕ → ℝ} {T : ℕ → ℕ} {C : ℕ} {lev : Fin C → ℕ} {γ : Fin C → Fin W}
    {j : Fin C → ℕ} {A : Fin C → Set Line} {H : Fin W → Set Event}
    (b : Fin C) (ag : ℝ) (hg : gain ≤ ag) (hg8 : ag ≤ 1 / 8)
    (hroom : r (lev b) + 2 * ag * L ≤ L) (hBpos : 0 < B (γ b))
    (Mz MH : ℕ) (A0 Z a0 b0 h0 s0 : ℝ) (Sc : Poly) (f0 : Base → ℝ) (p0 : Fin 7 → Base)
    (E0 : Set Base) (hraw : RawBranchData Cloc J Dr A0 Z a0 b0 h0 s0 Sc f0 p0 E0)
    (c : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hformat : Mz * Cloc + 2 * MH + 11 ≤ Mc) (hZ : Z ≤ Nk ^ Mz)
    (hc : ∀ i, |c i| ≤ Nk ^ MH) (hM : ∀ i k, |M i k| ≤ Nk ^ MH) (hBsize : |B (γ b)| ≤ Nk ^ MH)
    (hb0 : b0 = dyadicThickness Nk (r (lev b) + ag * L))
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hbudget : restorationRemezFactor η * (A0 ^ (J + 1)) ^ Cloc ≤ Nk ^ (ρ * gain * L + ε))
    (S0 : Poly) (P0 : MvPolynomial (Fin 3) ℝ) (a : ℝ) (Bδ Cδ : MvPolynomial (Fin 3) ℝ)
    (σ εfit A₁ : ℝ)
    (hA₁ : 2 ≤ A₁) (hA₁A0 : A₁ ≤ A0) (hε : 0 < εfit) (hband : εfit * A₁ ^ 19 ≤ A0 * b0)
    (hsmall : 4 * |a| * εfit ≤ (2 * A₁ ^ 2)⁻¹)
    (hroot : ∀ z ∈ ball (0 : Base) 4, a * (f0 z) ^ 2 + eval (fun i => z i) Bδ * f0 z +
      eval (fun i => z i) Cδ = 0 ∧ 0 < (2 * a * f0 z + eval (fun i => z i) Bδ) * σ)
    (hSeq : ∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] S0 - eval (fun i => z i) P0 =
      a * w ^ 2 + eval (fun i => z i) Bδ * w + eval (fun i => z i) Cδ)
    (hSd : ∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] (pderiv 3 S0) =
      2 * a * w + eval (fun i => z i) Bδ)
    (A' : Set Line) (hA'm : MeasurableSet A') (hA'b : A' ⊆ A b) (S : Line → Set ℝ)
    (hS : ∀ l ∈ A', S l ⊆ Icc (0 : ℝ) 1 ∧ ENNReal.ofReal η ≤ volume (S l))
    (hwit : ∀ l ∈ A', ∀ t ∈ S l, CertifiedNativeGroupPoint c M (B (γ b)) S0 P0 Sc εfit A₁ σ
      (graphPoint l ((j b : ℝ) / (2 : ℝ) ^ T (lev b) + ((2 : ℝ) ^ T (lev b))⁻¹ * t)))
    (counted : Set Event)
    (hcounted : counted ⊆ {p | p ∈ H (γ b) ∧ p.1 ∈ A' ∧
      p.2 ∈ Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b)) (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b)) ∧
      CertifiedNativeGroupPoint c M (B (γ b)) S0 P0 Sc εfit A₁ σ (graphPoint p.1 p.2)})
    (hmass : ENNReal.ofReal (Nk ^ (-((d₁ * ag + ρ * gain) * L) - ε) /
        (2 : ℝ) ^ T (lev b)) * ν (γ b) (A b) ≤ ((ν (γ b)).prod volume) counted) :
    RawSampledCandidate Cloc J Dr Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H := by
  have hregion : ∀ {x : Fin 4 → ℝ}, CertifiedNativeGroupPoint c M (B (γ b)) S0 P0 Sc εfit A₁ σ x →
      pointOfCoordinates (coordinateMap c M (B (γ b)) x) ∈ rawRegion A0 b0 Sc f0 :=
    fun hx => mem_rawRegion_of_certified hA₁ hA₁A0 hε hband hsmall hroot hSeq hSd hx
  refine ⟨b, ag, Mz, MH, A0, Z, a0, b0, h0, s0, Sc, f0, p0, E0, c, M, η, A', S, counted,
    hraw, hg, hg8, hroom, hBpos, hη, hη1, hformat, hZ, hc, hM, hBsize, hb0, hbudget, hA'm, hA'b,
    hS, fun l hl t ht => hregion (hwit l hl t ht), ?_, hmass⟩
  intro p hp
  obtain ⟨hpH, hpA, hpt, hpg⟩ := hcounted hp
  exact ⟨hpH, hpA, hpt, hregion hpg⟩

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
