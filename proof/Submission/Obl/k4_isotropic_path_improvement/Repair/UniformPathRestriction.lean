-- Part of an offer for o106 assembled by x0678 (o064). Adapted from this LOT tree, o064's
-- repository, origin/x0447 at f61522e4 (x0447's file Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/UniformPathRestriction.lean);
-- only the namespace changed. See that file for the sources it in turn adapts.
import Submission.Obl.k4_isotropic_path_improvement.Repair.GridPacketRestriction
import Submission.Obl.k4_quadratic_finite_greedy_cover

namespace Submission.Obl.k4_isotropic_path_improvement.Repair.UniformPathRestriction

open MeasureTheory UniformGridRefinement GridPacketRestriction
open Submission.Obl.k4_quadratic_finite_greedy_cover

section

variable {Nk L κ₁ δ₀ σ κ : ℝ} {W C m k Mp Dp : ℕ}
  {ω : Fin W → ℝ} {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {f : ℝ → ℝ}
  {sFine sCoarse r nw : ℕ → ℝ} {T : ℕ → ℕ}
  {lev : Fin C → ℕ} {par : Fin C → Fin C} {γ : Fin C → Fin W} {j : Fin C → ℕ}
  {c u : Fin C → EuclideanSpace ℝ (Fin 2)} {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ}
  {R : Fin C → MvPolynomial (Fin 4) ℝ} {A : Fin C → Set (ℕ × (Fin 6 → ℝ))}
  {F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
  {lst : ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)}

/-- Restrict a fine path to the old uniform nodes. Every chart, original
measure and world weight is retained verbatim; the parent follows the actual
ancestor chain and the old lists are pulled back through an injection. -/
theorem path_restrict_uniform (hm : 0 < m) (hk : 0 < k)
    (hgrid : ∀ i, i < m → sFine (coarseIndex k i) = sCoarse i)
    (hp : path Nk L W ω ν E B f κ₁ (m * k) sFine δ₀ Mp Dp σ
      r T nw κ C lev par γ j c u Q R A F lst) :
    let C' := GridPacketRestriction.count lev m k
    let idx : Fin C' → Fin C := GridPacketRestriction.index
    let lv : Fin C' → ℕ := GridPacketRestriction.level
    let ls : ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C') :=
      fun i w o => GridPacketRestriction.pullList (lst (coarseIndex k i) w o) i
    ∃ parent' : Fin C' → Fin C',
      path Nk L W ω ν E B f κ₁ m sCoarse δ₀ Mp Dp σ
        (r ∘ coarseIndex k) (T ∘ coarseIndex k) (nw ∘ coarseIndex k) κ C' lv parent'
        (γ ∘ idx) (j ∘ idx) (c ∘ idx) (u ∘ idx) (Q ∘ idx) (R ∘ idx) (A ∘ idx) (F ∘ idx) ls := by
  dsimp only
  rcases hp with ⟨hκ, hκN, hC, hlast, hlevels, hlists, hdisj, hcharts⟩
  have hparents (b : Fin C) (hb : 0 < lev b) :
      lev (par b) + 1 = lev b ∧ γ (par b) = γ b ∧ A b ⊆ A (par b) ∧ F b ⊆ F (par b) ∧
      (j (par b) : ℝ) / (2 : ℝ) ^ T (lev (par b)) ≤ (j b : ℝ) / (2 : ℝ) ^ T (lev b) ∧
      ((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b) ≤
        ((j (par b) : ℝ) + 1) / (2 : ℝ) ^ T (lev (par b)) := by
    rcases (hcharts b).2.2 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp⟩
    exact hp hb
  have hpar : ∀ b, 0 < lev b → lev (par b) + 1 = lev b := fun b hb => (hparents b hb).1
  have hidx (b : Fin (GridPacketRestriction.count lev m k)) :
      lev (GridPacketRestriction.index b) = coarseIndex k (GridPacketRestriction.level b) :=
    GridPacketRestriction.index_level b
  let low : Fin C → ℝ := fun b => (j b : ℝ) / (2 : ℝ) ^ T (lev b)
  let high : Fin C → ℝ := fun b => ((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b)
  let rel : Fin C → Fin C → Prop := fun b a =>
    γ b = γ a ∧ A b ⊆ A a ∧ F b ⊆ F a ∧ low a ≤ low b ∧ high b ≤ high a
  have hrefl : ∀ b, rel b b := fun _ => ⟨rfl, subset_rfl, subset_rfl, le_rfl, le_rfl⟩
  have htrans : ∀ a b c, rel a b → rel b c → rel a c := by
    rintro a b d ⟨hab, hAab, hFab, hloab, hhiab⟩ ⟨hbd, hAbd, hFbd, hlobd, hhibd⟩
    exact ⟨hab.trans hbd, hAab.trans hAbd, hFab.trans hFbd, hlobd.trans hloab, hhiab.trans hhibd⟩
  have hstep : ∀ b, 0 < lev b → rel b (par b) := by
    intro b hb
    obtain ⟨_, hγ, hA, hF, hlo, hhi⟩ := hparents b hb
    exact ⟨hγ.symm, hA, hF, hlo, hhi⟩
  refine ⟨GridPacketRestriction.predecessor par hpar, hκ, hκN, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hc : (GridPacketRestriction.count lev m k : ℝ) ≤ (C : ℝ) := by
      exact_mod_cast GridPacketRestriction.card_packets_le (lev := lev) (m := m) hk
    exact hc.trans hC
  · have hi : coarseIndex k (m - 1) = m * k - 1 := by
      simpa only [coarseIndex, uniformIndex] using uniformIndex_last hm k hk
    simpa only [Function.comp_apply, hi] using hlast
  · intro i hi
    have hfi : coarseIndex k i < m * k := (uniformIndex k hk ⟨i, hi⟩).isLt
    obtain ⟨hr, hrpos, htlo, hthi, hnw, hmass⟩ := hlevels (coarseIndex k i) hfi
    refine ⟨?_, hrpos, ?_, ?_, ?_, ?_⟩
    · simpa only [Function.comp_apply, hgrid i hi] using hr
    · simpa only [Function.comp_apply, hgrid i hi] using htlo
    · simpa only [Function.comp_apply, hgrid i hi] using hthi
    · simpa only [Function.comp_apply, hgrid i hi] using hnw
    · dsimp only [Function.comp_apply]
      rw [GridPacketRestriction.sum_level_fin hk
        (fun b => ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume) (F b)) i hi]
      exact hmass
  · intro i w o
    have hc := GridPacketRestriction.pullList_card (lev := lev) (m := m) hk
      (lst (coarseIndex k i) w o) i
    exact (Nat.cast_le.mpr hc).trans (hlists _ _ _)
  · intro b b' hne hl hw hj
    apply hdisj (GridPacketRestriction.index b) (GridPacketRestriction.index b')
    · exact fun he => hne (GridPacketRestriction.index_injective hk he)
    · rw [hidx b, hidx b', hl]
    · exact hw
    · exact hj
  · intro b
    have hb := hcharts (GridPacketRestriction.index b)
    rw [hidx b] at hb
    obtain ⟨_, hj, hc⟩ := hb
    rcases hc with ⟨hdet, hcu, hframe, hsize, hdeg, hcoeff, hA, hF, hfmt, hwhole,
      hselected, hfloor, hprior, hdlo, hdhi, hknown, _⟩
    refine ⟨GridPacketRestriction.level_lt b, hj,
      hdet, hcu, hframe, hsize, hdeg, hcoeff, hA, hF, hfmt, hwhole,
      hselected, hfloor, hprior, hdlo, hdhi, ?_, ?_⟩
    ·
      intro p hp
      exact GridPacketRestriction.mem_pullList rfl (hknown p hp)
    · intro hpos
      obtain ⟨hγ, hA, hF, hlo, hhi⟩ :=
        GridPacketRestriction.predecessor_relation hpar rel hrefl htrans hstep b hpos
      refine ⟨GridPacketRestriction.predecessor_level hpar b hpos,
        hγ.symm, hA, hF, ?_, ?_⟩
      · simpa only [low, hidx, Function.comp_apply] using hlo
      · simpa only [high, hidx, Function.comp_apply] using hhi

/-- The terminal residual is unchanged when the terminal fine level is retained. -/
theorem top_cover_restrict_uniform (hm : 0 < m) (hk : 0 < k)
    {H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (hH : ∀ w, H w ⊆ {p | ∃ b : Fin C, lev b = m * k - 1 ∧ γ b = w ∧ p ∈ F b}) :
    ∀ w, H w ⊆ {p | ∃ b : Fin (GridPacketRestriction.count lev m k),
      GridPacketRestriction.level b = m - 1 ∧ γ (GridPacketRestriction.index b) = w ∧
        p ∈ F (GridPacketRestriction.index b)} := by
  intro w p hp
  obtain ⟨b, hb, hγ, hF⟩ := hH w hp
  have hlast : coarseIndex k (m - 1) = m * k - 1 := by
    simpa only [coarseIndex, uniformIndex] using uniformIndex_last hm k hk
  obtain ⟨b', hindex, hlevel⟩ := GridPacketRestriction.index_surjective_at_level (m := m) (k := k)
    (m - 1) (by omega) b (hb.trans hlast.symm)
  exact ⟨b', hlevel, by simpa only [hindex] using hγ, by simpa only [hindex] using hF⟩

/-- An old-node width witness is a witness on the refined path. -/
theorem width_lift_uniform (hk : 0 < k) {gain τ : ℝ} {Mi Di : ℕ}
    (hw : width Nk L W ω ν E B m (r ∘ coarseIndex k) (T ∘ coarseIndex k)
      (nw ∘ coarseIndex k) gain Mi Di τ) :
    width Nk L W ω ν E B (m * k) r T nw gain Mi Di τ := by
  obtain ⟨i, hi, hroom, hs⟩ := hw
  exact ⟨coarseIndex k i, (uniformIndex k hk ⟨i, hi⟩).isLt, hroom, hs⟩

/-- The original quadratic candidate is unchanged under path restriction. -/
theorem candidate_lift_uniform {Mc : ℕ} {d₁ ρ gain ε : ℝ}
    {H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (hc : candidate Nk L W ν B Mc d₁ ρ gain ε (r ∘ coarseIndex k) (T ∘ coarseIndex k)
      (GridPacketRestriction.count lev m k) GridPacketRestriction.level
      (γ ∘ GridPacketRestriction.index) (j ∘ GridPacketRestriction.index)
      (A ∘ GridPacketRestriction.index) H) :
    candidate Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H := by
  obtain ⟨b, ag, hgain, hag, hmargin, P, A', hdeg, hcoeff, hmeas, hsub, hfit, hmass⟩ := hc
  refine ⟨GridPacketRestriction.index b, ag, hgain, hag, ?_, P, A', hdeg, hcoeff,
    hmeas, hsub, ?_, ?_⟩
  · simpa only [Function.comp_apply, GridPacketRestriction.index_level b] using hmargin
  · simpa only [Function.comp_apply, GridPacketRestriction.index_level b] using hfit
  · simpa only [Function.comp_apply, GridPacketRestriction.index_level b] using hmass

/-- Enlarging profile tolerance preserves the exact path, including both
determinant bounds and the original selected-incidence floors. -/
theorem path_tolerance_mono {δ₀' : ℝ} (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hδ : δ₀ ≤ δ₀')
    (hp : path Nk L W ω ν E B f κ₁ m sFine δ₀ Mp Dp σ
      r T nw κ C lev par γ j c u Q R A F lst) :
    path Nk L W ω ν E B f κ₁ m sFine δ₀' Mp Dp σ
      r T nw κ C lev par γ j c u Q R A F lst := by
  rcases hp with ⟨hκ, hκN, hC, hlast, hlevels, hlists, hdisj, hcharts⟩
  have hδL := mul_le_mul_of_nonneg_right hδ hL
  refine ⟨hκ, hκN, hC, hlast, ?_, hlists, hdisj, ?_⟩
  · intro i hi
    obtain ⟨hr, hrpos, htlo, hthi, hnw, hmass⟩ := hlevels i hi
    refine ⟨hr.trans hδL, hrpos, ?_, ?_, hnw.trans hδL, hmass⟩
    · exact (Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)).trans htlo
    · exact hthi.trans (Real.rpow_le_rpow_of_exponent_le hN (by nlinarith))
  · intro b
    rcases hcharts b with ⟨hlev, hj, hdet, hcu, hframe, hsize, hdeg, hcoeff,
      hA, hF, hfmt, hwhole, hselected, hfloor, hprior, hdlo, hdhi, hknown, hparent⟩
    refine ⟨hlev, hj, hdet, hcu, hframe, hsize, hdeg, hcoeff,
      hA, hF, hfmt, hwhole, hselected, hfloor, hprior, ?_, ?_, hknown, hparent⟩
    · exact (Real.rpow_le_rpow_of_exponent_le hN (by linarith)).trans hdlo
    · exact hdhi.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith))

end

end Submission.Obl.k4_isotropic_path_improvement.Repair.UniformPathRestriction
