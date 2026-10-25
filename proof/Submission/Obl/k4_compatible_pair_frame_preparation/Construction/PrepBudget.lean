-- Adapted from this LOT tree, o206, session x0753, commit f0f3bdbb,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/PrepBudget.lean.
-- Earlier attribution comments are retained below.

-- Adapted from this LOT tree, o104, session x0472, commit 82956838,
-- Submission/Obl/k4_terminal_time_extension/PrepBudget.lean.
-- Earlier source attributions in the original file are preserved below.

import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.PrepStruct
import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.PrepDensity
import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.Thickness
import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.FloorCounting

/-!
# Density budgets of a tested sample

* `Hyp.beta_le`: the source-base density of an entry in both roles (paper display
  `a02:source-base-density`): the pairs of an entry, as source or as witness, have their
  source incidence in `Good`, with the entry's old test at most `12 κ₀ δ (2^s+1)²` and its
  hidden derivative at least `dfl · B`; the capped depth-`L` density, the hidden-bin count of
  the test and the base Jacobian give `cap · 16 (1 + 12 κ₀ (2^s+1)² / dfl) · (100 κ)³ |det Q|`.
* `Hyp.count_le`: entries per world and coarse block, through the old true floors
  (paper display `a02:old-label-count`).
-/

namespace Submission.Obl.k4_compatible_pair_frame_preparation.Construction

open MeasureTheory Set MvPolynomial
open scoped ENNReal

namespace PrepData

variable {D : PrepData} {N : ℝ} {M₀ D₀ : ℕ} {L : ℝ} {E : Fin D.W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}

/-- The source incidences of the pairs of an entry. -/
def Xent (D : PrepData) (N L : ℝ) (s : Fin D.m) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  D.Good (D.fγ (D.frame s)) ∩
    {p | |eval (x p.1 p.2) (D.R (D.chartOf s))| ≤ 12 * (D.κ₀ * δ N L) * (2 ^ D.s + 1) ^ 2 ∧
      D.dfl * D.B (D.fγ (D.frame s)) ≤ |eval (x p.1 p.2) (pderiv 3 (D.R (D.chartOf s)))|}

theorem Hyp.Xent_meas (h : D.Hyp N M₀ D₀ L E) (s : Fin D.m) : MeasurableSet (D.Xent N L s) := by
  have hc (R : MvPolynomial (Fin 4) ℝ) :
      Continuous (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => |eval (x p.1 p.2) R|) := by
    apply Continuous.abs
    apply (MvPolynomial.continuous_eval _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp [x] <;> fun_prop
  exact (h.Good_meas _).inter ((measurableSet_le (hc _).measurable measurable_const).inter
    (measurableSet_le measurable_const (hc _).measurable))

/-- Both roles of an entry: the source incidence is in `Xent`, the witness time in the
coarse block. -/
theorem Hyp.roles_sub (h : D.Hyp N M₀ D₀ L E) (hdfl1 : D.dfl ≤ D.κ₀⁻¹) (s : Fin D.m)
    (p : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ)) (hp : (∃ s', p ∈ D.H s s') ∨ ∃ s', p ∈ D.H s' s) :
    (p.1, p.2.1) ∈ D.Xent N L s ∧ p.2.2 ∈ D.blk (D.fj (D.frame s)) := by
  have hκ₀ := h.κ₀one
  have hs1 : (1 : ℝ) ≤ 12 * (2 ^ D.s + 1) ^ 2 := by
    have : (1 : ℝ) ≤ 2 ^ D.s + 1 := by
      have := pow_pos (by norm_num : (0 : ℝ) < 2) D.s; linarith
    nlinarith
  have hδ : 0 < δ N L := by unfold δ; positivity
  rcases hp with ⟨s', hp⟩ | ⟨s', hp⟩
  · -- the source role
    obtain ⟨hsrc, hf, hS0, hblk, hS1, hG, -⟩ := hp
    set b := D.chartOf s with hb
    have hγ : D.fγ (D.frame s) = D.γ b := fγ_of_src hsrc
    obtain ⟨-, hA0, ht0, hd0⟩ := h.sel b hS0.1
    obtain ⟨-, -, hw⟩ := h.whole b hA0
    obtain ⟨-, hv, -, -⟩ := hw p.2.1 ht0
    refine ⟨⟨by rw [hγ]; exact hG, ?_, ?_⟩, hblk⟩
    · refine hv.trans ?_
      have : 0 ≤ D.κ₀ * δ N L := by positivity
      nlinarith
    · rw [hγ]
      refine le_trans ?_ hd0
      have hB := h.Bpos (D.γ b)
      rw [div_eq_mul_inv, mul_comm]
      exact mul_le_mul_of_nonneg_left hdfl1 hB.le
  · -- the witness role
    obtain ⟨hsrc, hf, hS0, hblk, hS1, hG, hder⟩ := hp
    set b := D.chartOf s' with hb
    set b' := D.chartOf s with hb'
    have hγ : D.fγ (D.frame s') = D.γ b := fγ_of_src hsrc
    have hγs : D.fγ (D.frame s) = D.γ b := by rw [hf]; exact hγ
    have hJ' : coarseIdx (D.j b') = D.fj (D.frame s') := witness_block hf
    have hJ : D.fj (D.frame s') = coarseIdx (D.j b) := fj_of_src hsrc
    obtain ⟨-, hA0, ht0, -⟩ := h.sel b hS0.1
    obtain ⟨-, hA1, -, -⟩ := h.sel b' hS1.1
    have ht0blk : p.2.1 ∈ D.blk (coarseIdx (D.j b')) := by
      rw [hJ', hJ]; exact old_sub_blk _ ht0
    obtain ⟨hv, -⟩ := h.extrap b' hA1 ht0blk
    refine ⟨⟨by rw [hγs]; exact hG, hv, by rw [hγs]; exact hder⟩, ?_⟩
    rw [hf]; exact hblk

/-- **Source-base densities in both roles.** -/
theorem Hyp.beta_le (h : D.Hyp N M₀ D₀ L E) (ν : Fin D.W → Measure (ℕ × (Fin 6 → ℝ)))
    [∀ γ, SFinite (ν γ)] (gL : Fin D.W → EuclideanSpace ℝ (Fin 3) × ℤ → ℝ≥0∞)
    (hgL : ∀ γ, Measurable (gL γ))
    (hmapL : ∀ γ, Measure.map (obs (D.B γ) (δ N L)) (((ν γ).prod volume).restrict (E γ)) =
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count).withDensity (gL γ))
    {cap : ℝ} (hcap : 0 ≤ cap)
    (hGood : ∀ γ, ∀ p ∈ D.Good γ, gL γ (obs (D.B γ) (δ N L) p) ≤ ENNReal.ofReal cap)
    {κ : ℝ} (hκ : 2 ≤ κ) (hdfl : 0 < D.dfl) (hdfl1 : D.dfl ≤ D.κ₀⁻¹) (s : Fin D.m)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : MeasurableSet U)
    (role : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ) → Prop)
    (hrole : ∀ p, role p → (∃ s', p ∈ D.H s s') ∨ ∃ s', p ∈ D.H s' s) :
    ENNReal.ofReal ((2 : ℝ) ^ D.T) ^ 2 *
      ((ν (D.fγ (D.frame s))).prod (volume.prod volume)) {p | role p ∧
        base D.T (((D.fj (D.frame s) : ℕ) : ℝ)) κ (D.fc (D.frame s)) (D.fu (D.frame s))
          (D.fQ (D.frame s)) p.1 p.2.1 ∈ U} ≤
      ENNReal.ofReal (cap * (16 * (1 + 12 * D.κ₀ * (2 ^ D.s + 1) ^ 2 / D.dfl)) *
        ((100 * κ) ^ 3 * |(D.fQ (D.frame s)).det|)) * volume U := by
  set γ := D.fγ (D.frame s) with hγdef
  set B := D.B γ with hBdef
  have hB : 0 < B := h.Bpos γ
  have hδ : 0 < δ N L := by unfold δ; positivity
  have hκ₀ := h.κ₀one
  have hpT : (0 : ℝ) < 2 ^ D.T := by positivity
  set ε := 12 * (D.κ₀ * δ N L) * (2 ^ D.s + 1) ^ 2 with hε
  set β := D.dfl * B with hβ
  have hε0 : 0 ≤ ε := by positivity
  have hβ0 : 0 < β := by positivity
  have hQ := (h.frame_bounds (D.frame s)).1
  set Y := hidClosed (D.R (D.chartOf s)) ε β (δ N L / B) with hY
  have hYm : MeasurableSet Y := measurableSet_hidClosed _ _ _ _
  have hfib := count_hidClosed_le (D.R (D.chartOf s)) (h.Rdeg _) hε0 hβ0
    (div_pos hδ hB)
  have hXE : D.Xent N L s ⊆ E γ := fun p hp => h.Good_sub γ hp.1
  have hX : ∀ p ∈ D.Xent N L s, gL γ (obs B (δ N L) p) ≤ ENNReal.ofReal cap ∧
      obs B (δ N L) p ∈ Y :=
    fun p hp => ⟨hGood γ p hp.1, obs_mem_hidClosed hB hδ _ hp.2.1 hp.2.2⟩
  have hsub : {p : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ) | role p ∧
      base D.T (((D.fj (D.frame s) : ℕ) : ℝ)) κ (D.fc (D.frame s)) (D.fu (D.frame s))
        (D.fQ (D.frame s)) p.1 p.2.1 ∈ U} ⊆
      {p | (p.1, p.2.1) ∈ D.Xent N L s ∧ p.2.2 ∈ D.blk (D.fj (D.frame s)) ∧
        movingBasePoint ((2 : ℝ) ^ D.T) (((D.fj (D.frame s) : ℕ) : ℝ)) (100 * κ)
          (D.fc (D.frame s)) (D.fu (D.frame s)) (D.fQ (D.frame s))
          (obs B (δ N L) (p.1, p.2.1)).1 ∈ U} := by
    rintro p ⟨hr, hU'⟩
    obtain ⟨hX', hblk⟩ := h.roles_sub hdfl1 s p (hrole p hr)
    refine ⟨hX', hblk, ?_⟩
    rw [← base_eq_movingBasePoint D.T _ κ _ _ _ B (δ N L) (p.1, p.2.1)]
    exact hU'
  have hmain := capped_pair_base_le (ν γ) (E γ) (gL γ) (hgL γ) (hmapL γ) Y hYm _ hfib
    (ENNReal.ofReal cap) (D.Xent N L s) (h.Xent_meas s) hXE hX (hpT) (by positivity : (0:ℝ) < 100 * κ)
    (j := (((D.fj (D.frame s) : ℕ) : ℝ))) (D.fc (D.frame s)) (D.fu (D.frame s))
    (D.fQ (D.frame s)) hQ U hU (D.blk (D.fj (D.frame s))) (blk_meas _)
  have hvol : volume (D.blk (D.fj (D.frame s))) = ENNReal.ofReal ((2 : ℝ) ^ D.T)⁻¹ := by
    rw [blk, Real.volume_Icc]
    congr 1
    field_simp
    ring
  have hratio : ε / (β * (δ N L / B)) = 12 * D.κ₀ * (2 ^ D.s + 1) ^ 2 / D.dfl := by
    rw [hε, hβ]
    field_simp
  rw [hratio] at hmain
  calc ENNReal.ofReal ((2 : ℝ) ^ D.T) ^ 2 * ((ν γ).prod (volume.prod volume)) {p | role p ∧
        base D.T (((D.fj (D.frame s) : ℕ) : ℝ)) κ (D.fc (D.frame s)) (D.fu (D.frame s))
          (D.fQ (D.frame s)) p.1 p.2.1 ∈ U}
      ≤ ENNReal.ofReal ((2 : ℝ) ^ D.T) ^ 2 * (volume (D.blk (D.fj (D.frame s))) *
          (ENNReal.ofReal cap * ENNReal.ofReal (16 * (1 + 12 * D.κ₀ * (2 ^ D.s + 1) ^ 2 / D.dfl)) *
            (ENNReal.ofReal ((100 * κ) ^ 3 * |(D.fQ (D.frame s)).det| / (2 : ℝ) ^ D.T) *
              volume U))) := by
        gcongr
        exact (measure_mono hsub).trans hmain
    _ = ENNReal.ofReal (cap * (16 * (1 + 12 * D.κ₀ * (2 ^ D.s + 1) ^ 2 / D.dfl)) *
        ((100 * κ) ^ 3 * |(D.fQ (D.frame s)).det|)) * volume U := by
        rw [hvol]
        have h16 : 0 ≤ 16 * (1 + 12 * D.κ₀ * (2 ^ D.s + 1) ^ 2 / D.dfl) := by positivity
        have hdet : 0 ≤ (100 * κ) ^ 3 * |(D.fQ (D.frame s)).det| := by positivity
        rw [← ENNReal.ofReal_pow hpT.le, ← mul_assoc, ← mul_assoc, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp

/-- The fine blocks of a coarse block. -/
theorem card_fine_blocks_le {T s : ℕ} (j₀ : Fin (2 ^ T)) :
    (Finset.univ.filter (fun j' : Fin (2 ^ (T + s)) => coarseIdx j' = j₀)).card ≤ 2 ^ s := by
  classical
  have hinj : Set.InjOn (fun j' : Fin (2 ^ (T + s)) => (j' : ℕ) % 2 ^ s)
      (Finset.univ.filter (fun j' : Fin (2 ^ (T + s)) => coarseIdx j' = j₀) : Set _) := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, mem_setOf_eq] at ha hb
    have ha' : (a : ℕ) / 2 ^ s = j₀ := by rw [← ha]; rfl
    have hb' : (b : ℕ) / 2 ^ s = j₀ := by rw [← hb]; rfl
    apply Fin.ext
    rw [← Nat.div_add_mod (a : ℕ) (2 ^ s), ← Nat.div_add_mod (b : ℕ) (2 ^ s), ha', hb']
    simp only at hab
    rw [hab]
  calc (Finset.univ.filter (fun j' : Fin (2 ^ (T + s)) => coarseIdx j' = j₀)).card
      ≤ (Finset.range (2 ^ s)).card := by
        apply Finset.card_le_card_of_injOn _ _ hinj
        intro a _
        simp only [Finset.coe_range, mem_Iio]
        exact Nat.mod_lt _ (by positivity)
    _ = 2 ^ s := Finset.card_range _

theorem abs_det_eq_r₁_mul_r₂ {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) :
    |Q.det| = r₁ Q * r₂ Q := by
  unfold r₂
  have := r₁_pos hQ
  field_simp

/-- Old charts of one world and old block, counted through their true floors. -/
theorem Hyp.card_old_le (h : D.Hyp N M₀ D₀ L E) (ν : Fin D.W → Measure (ℕ × (Fin 6 → ℝ)))
    [∀ γ, IsProbabilityMeasure (ν γ)] {fL : ℝ}
    (hfloor : ∀ b, ENNReal.ofReal (N ^ (-fL) * |(D.Q b).det| / ((2 : ℝ) ^ (D.T + D.s) * D.κ₀)) ≤
      ((ν (D.γ b)).prod volume) (D.F b))
    (γ₀ : Fin D.W) (j' : Fin (2 ^ (D.T + D.s))) :
    ((Finset.univ.filter (fun b : Fin D.C => D.γ b = γ₀ ∧ D.j b = j')).card : ℝ) ≤
      D.κ₀ * N ^ fL / (D.R₁ * D.R₂) := by
  classical
  set ι := {b : Fin D.C // D.γ b = γ₀ ∧ D.j b = j'}
  have hcard : (Finset.univ.filter (fun b : Fin D.C => D.γ b = γ₀ ∧ D.j b = j')).card =
      Fintype.card ι := by
    rw [Fintype.card_subtype]
  have hN : 0 < N := by linarith [h.N2]
  have hpT : (0 : ℝ) < 2 ^ (D.T + D.s) := by positivity
  have hκ₀ := h.κ₀one
  set I := Icc (((j' : ℕ) : ℝ) / (2 : ℝ) ^ (D.T + D.s)) ((((j' : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (D.T + D.s))
  set a := N ^ (-fL) * (D.R₁ * D.R₂) / ((2 : ℝ) ^ (D.T + D.s) * D.κ₀) with ha
  have hR := mul_pos h.R₁pos h.R₂pos
  have ha0 : 0 < a := by positivity
  have hfl : ∀ i : ι, ENNReal.ofReal a ≤ ((ν γ₀).prod volume) (D.F i.1) := by
    intro i
    have hb := hfloor i.1
    rw [i.2.1] at hb
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hb
    rw [ha]
    gcongr
    rw [abs_det_eq_r₁_mul_r₂ (h.det i.1)]
    exact mul_le_mul (h.r₁lo i.1) (h.r₂lo i.1) h.R₂pos.le (r₁_nonneg _)
  have hsub : ∀ i : ι, D.F i.1 ⊆ D.A i.1 ×ˢ I := by
    intro i p hp
    obtain ⟨-, hA, ht, -⟩ := h.sel i.1 hp
    refine ⟨hA, ?_⟩
    have := i.2.2
    simp only [I]
    rw [← this]
    exact ht
  have hdisj : Pairwise (fun i i' : ι => Disjoint (D.A i.1) (D.A i'.1)) := by
    intro i i' hne
    exact h.disj i.1 i'.1 (fun he => hne (Subtype.ext he)) (i.2.1.trans i'.2.1.symm)
      (i.2.2.trans i'.2.2.symm)
  have hIfin : (volume : Measure ℝ) I ≠ ⊤ := by simp [I, Real.volume_Icc]
  have hc := card_le_timeMass_div_floor (ν γ₀) volume (fun i : ι => D.A i.1)
    (fun i : ι => D.F i.1) I (fun i => h.Fmeas i.1) hdisj hsub hIfin ha0 hfl
  rw [hcard]
  refine hc.trans (le_of_eq ?_)
  rw [Real.volume_Icc, ENNReal.toReal_ofReal (by
    rw [sub_nonneg]; gcongr; linarith), ha]
  rw [Real.rpow_neg hN.le]
  field_simp
  ring

/-- **Entries per world and coarse block.** -/
theorem Hyp.count_le (h : D.Hyp N M₀ D₀ L E) (ν : Fin D.W → Measure (ℕ × (Fin 6 → ℝ)))
    [∀ γ, IsProbabilityMeasure (ν γ)] {fL : ℝ}
    (hfloor : ∀ b, ENNReal.ofReal (N ^ (-fL) * |(D.Q b).det| / ((2 : ℝ) ^ (D.T + D.s) * D.κ₀)) ≤
      ((ν (D.γ b)).prod volume) (D.F b))
    (γ₀ : Fin D.W) (j₀ : Fin (2 ^ D.T)) :
    ((Finset.univ.filter (fun s : Fin D.m => D.fγ (D.frame s) = γ₀ ∧ D.fj (D.frame s) = j₀)).card
      : ℝ) ≤ 2 ^ D.s * (D.κ₀ * N ^ fL / (D.R₁ * D.R₂)) * (98 * (2 * D.Kb + 1) ^ 4 + 1) := by
  classical
  set Bset := Finset.univ.filter (fun b : Fin D.C => D.γ b = γ₀ ∧ coarseIdx (D.j b) = j₀)
  set K := 98 * (2 * D.Kb + 1) ^ 4 + 1
  have hsub : Finset.univ.filter (fun s : Fin D.m => D.fγ (D.frame s) = γ₀ ∧ D.fj (D.frame s) = j₀)
      ⊆ Bset.biUnion (fun b => Finset.univ.filter (fun s : Fin D.m => D.chartOf s = b)) := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Bset]
    refine ⟨D.chartOf s, ⟨?_, ?_⟩, rfl⟩
    · rw [← D.frame_world s]; exact hs.1
    · rw [← D.frame_block s]; exact hs.2
  have h1 : (Finset.univ.filter (fun s : Fin D.m => D.fγ (D.frame s) = γ₀ ∧
      D.fj (D.frame s) = j₀)).card ≤ Bset.card * K := by
    calc _ ≤ (Bset.biUnion (fun b => Finset.univ.filter (fun s : Fin D.m => D.chartOf s = b))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ b ∈ Bset, (Finset.univ.filter (fun s : Fin D.m => D.chartOf s = b)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ Bset, K := Finset.sum_le_sum (fun b _ => card_charts_le b)
      _ = Bset.card * K := by rw [Finset.sum_const, smul_eq_mul]
  -- the charts of the coarse block, by fine block
  set Jset := Finset.univ.filter (fun j' : Fin (2 ^ (D.T + D.s)) => coarseIdx j' = j₀)
  have hB : Bset ⊆ Jset.biUnion
      (fun j' => Finset.univ.filter (fun b : Fin D.C => D.γ b = γ₀ ∧ D.j b = j')) := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bset] at hb
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Jset]
    exact ⟨D.j b, hb.2, hb.1, rfl⟩
  have h2 : (Bset.card : ℝ) ≤ 2 ^ D.s * (D.κ₀ * N ^ fL / (D.R₁ * D.R₂)) := by
    have hc : Bset.card ≤ ∑ j' ∈ Jset,
        (Finset.univ.filter (fun b : Fin D.C => D.γ b = γ₀ ∧ D.j b = j')).card :=
      (Finset.card_le_card hB).trans Finset.card_biUnion_le
    have hc' : (Bset.card : ℝ) ≤ ∑ j' ∈ Jset,
        ((Finset.univ.filter (fun b : Fin D.C => D.γ b = γ₀ ∧ D.j b = j')).card : ℝ) := by
      exact_mod_cast hc
    refine hc'.trans ?_
    calc ∑ j' ∈ Jset, ((Finset.univ.filter (fun b : Fin D.C => D.γ b = γ₀ ∧ D.j b = j')).card : ℝ)
        ≤ ∑ _j' ∈ Jset, D.κ₀ * N ^ fL / (D.R₁ * D.R₂) :=
          Finset.sum_le_sum (fun j' _ => h.card_old_le ν hfloor γ₀ j')
      _ = Jset.card * (D.κ₀ * N ^ fL / (D.R₁ * D.R₂)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ D.s * (D.κ₀ * N ^ fL / (D.R₁ * D.R₂)) := by
          have hN : 0 < N := by linarith [h.N2]
          have hκ₀ := h.κ₀one
          have hR := mul_pos h.R₁pos h.R₂pos
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast card_fine_blocks_le j₀
  have hK0 : (0 : ℝ) ≤ K := by positivity
  calc _ ≤ ((Bset.card * K : ℕ) : ℝ) := by exact_mod_cast h1
    _ = (Bset.card : ℝ) * K := by push_cast; ring
    _ ≤ 2 ^ D.s * (D.κ₀ * N ^ fL / (D.R₁ * D.R₂)) * K := mul_le_mul_of_nonneg_right h2 hK0
    _ = _ := by simp [K]

/-- The scaled pair mass of a set of pairs whose source incidences have capped density
and boundedly many hidden bins, in the base coordinates of a frame. -/
theorem Hyp.scaled_pair_le (h : D.Hyp N M₀ D₀ L E) (ν : Measure (ℕ × (Fin 6 → ℝ))) [SFinite ν]
    (γ : Fin D.W) {δr : ℝ} (gr : EuclideanSpace ℝ (Fin 3) × ℤ → ℝ≥0∞) (hgr : Measurable gr)
    (hmapr : Measure.map (obs (D.B γ) δr) ((ν.prod volume).restrict (E γ)) =
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count).withDensity gr)
    (Y : Set (EuclideanSpace ℝ (Fin 3) × ℤ)) (hY : MeasurableSet Y) {n cap : ℝ} (hn : 0 ≤ n)
    (hcap : 0 ≤ cap)
    (hfib : ∀ z, Measure.count (Prod.mk z ⁻¹' Y) ≤ ENNReal.ofReal n)
    (X : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hXm : MeasurableSet X) (hXE : X ⊆ E γ)
    (hX : ∀ p ∈ X, gr (obs (D.B γ) δr p) ≤ ENNReal.ofReal cap ∧ obs (D.B γ) δr p ∈ Y)
    {κ : ℝ} (hκ : 2 ≤ κ) (i : Fin D.J) (U : Set (EuclideanSpace ℝ (Fin 3)))
    (hU : MeasurableSet U) (Z : Set ((ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ)))
    (hZ : ∀ p ∈ Z, (p.1, p.2.1) ∈ X ∧ p.2.2 ∈ D.blk (D.fj i) ∧
      base D.T (((D.fj i : ℕ) : ℝ)) κ (D.fc i) (D.fu i) (D.fQ i) p.1 p.2.1 ∈ U) :
    ENNReal.ofReal ((2 : ℝ) ^ D.T) ^ 2 * (ν.prod (volume.prod volume)) Z ≤
      ENNReal.ofReal (cap * n * ((100 * κ) ^ 3 * |(D.fQ i).det|)) * volume U := by
  have hpT : (0 : ℝ) < 2 ^ D.T := by positivity
  have hQ := (h.frame_bounds i).1
  have hsub : Z ⊆ {p | (p.1, p.2.1) ∈ X ∧ p.2.2 ∈ D.blk (D.fj i) ∧
      movingBasePoint ((2 : ℝ) ^ D.T) (((D.fj i : ℕ) : ℝ)) (100 * κ) (D.fc i) (D.fu i) (D.fQ i)
        (obs (D.B γ) δr (p.1, p.2.1)).1 ∈ U} := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hZ p hp
    refine ⟨h1, h2, ?_⟩
    rw [← base_eq_movingBasePoint D.T _ κ _ _ _ (D.B γ) δr (p.1, p.2.1)]
    exact h3
  have hmain := capped_pair_base_le ν (E γ) gr hgr hmapr Y hY _ hfib (ENNReal.ofReal cap) X hXm
    hXE hX hpT (by positivity : (0 : ℝ) < 100 * κ) (j := (((D.fj i : ℕ) : ℝ))) (D.fc i)
    (D.fu i) (D.fQ i) hQ U hU (D.blk (D.fj i)) (blk_meas _)
  have hvol : volume (D.blk (D.fj i)) = ENNReal.ofReal ((2 : ℝ) ^ D.T)⁻¹ := by
    rw [blk, Real.volume_Icc]
    congr 1
    field_simp
    ring
  calc ENNReal.ofReal ((2 : ℝ) ^ D.T) ^ 2 * (ν.prod (volume.prod volume)) Z
      ≤ ENNReal.ofReal ((2 : ℝ) ^ D.T) ^ 2 * (volume (D.blk (D.fj i)) *
          (ENNReal.ofReal cap * ENNReal.ofReal n *
            (ENNReal.ofReal ((100 * κ) ^ 3 * |(D.fQ i).det| / (2 : ℝ) ^ D.T) * volume U))) := by
        gcongr
        exact (measure_mono hsub).trans hmain
    _ = ENNReal.ofReal (cap * n * ((100 * κ) ^ 3 * |(D.fQ i).det|)) * volume U := by
        rw [hvol]
        rw [← ENNReal.ofReal_pow hpT.le, ← mul_assoc, ← mul_assoc, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp

/-- The band pairs of a frame. -/
def bandPairs (D : PrepData) (N : ℝ) (κ : ℝ) (i : Fin D.J) (ρ : ℝ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (G : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Set ((ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ)) :=
  {p | (∃ s s', D.frame s = i ∧ p ∈ D.H s s') ∧
    base D.T (((D.fj i : ℕ) : ℝ)) κ (D.fc i) (D.fu i) (D.fQ i) p.1 p.2.1 ∈ U ∧
    |D.B (D.fγ i) * (x p.1 p.2.1) 3 -
      G (base D.T (((D.fj i : ℕ) : ℝ)) κ (D.fc i) (D.fu i) (D.fQ i) p.1 p.2.1)| ≤ ρ}

theorem bandPairs_sub {κ : ℝ} {i : Fin D.J} {ρ : ℝ} {U : Set (EuclideanSpace ℝ (Fin 3))}
    {G : EuclideanSpace ℝ (Fin 3) → ℝ} {p : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ)}
    (hp : p ∈ D.bandPairs N κ i ρ U G) :
    (p.1, p.2.1) ∈ D.Good (D.fγ i) ∧ p.2.2 ∈ D.blk (D.fj i) := by
  obtain ⟨⟨s, s', hs, hH⟩, -, -⟩ := hp
  obtain ⟨hsrc, -, -, hblk, -, hG, -⟩ := hH
  refine ⟨?_, by rw [← hs]; exact hblk⟩
  rw [← hs, D.frame_world s]
  exact hG

theorem continuous_base_inc (T : ℕ) (j κ : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    Continuous (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => base T j κ c u Q p.1 p.2) := by
  have : (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => base T j κ c u Q p.1 p.2) =
      fun p => movingBasePoint ((2 : ℝ) ^ T) j (100 * κ) c u Q (obs 1 1 p).1 := by
    funext p; exact base_eq_movingBasePoint T j κ c u Q 1 1 p
  rw [this]
  refine (continuous_movingBasePoint _ _ _ _ _ _).comp ?_
  unfold obs
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro k
  fin_cases k <;> simp [x] <;> fun_prop

/-- **Band bound at one depth.** -/
theorem Hyp.band_depth_le (h : D.Hyp N M₀ D₀ L E) (ν : Fin D.W → Measure (ℕ × (Fin 6 → ℝ)))
    [∀ γ, SFinite (ν γ)] {r : ℝ} (gr : Fin D.W → EuclideanSpace ℝ (Fin 3) × ℤ → ℝ≥0∞)
    (hgr : ∀ γ, Measurable (gr γ))
    (hmapr : ∀ γ, Measure.map (obs (D.B γ) (δ N r)) (((ν γ).prod volume).restrict (E γ)) =
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count).withDensity (gr γ))
    {cap : ℝ} (hcap : 0 ≤ cap)
    (hGood : ∀ γ, ∀ p ∈ D.Good γ, gr γ (obs (D.B γ) (δ N r) p) ≤ ENNReal.ofReal cap)
    {κ : ℝ} (hκ : 2 ≤ κ) (i : Fin D.J) {ρ : ℝ} (hρ : 0 ≤ ρ) (U : Set (EuclideanSpace ℝ (Fin 3)))
    (hU : MeasurableSet U) (G : EuclideanSpace ℝ (Fin 3) → ℝ) (hG : Measurable G) :
    ENNReal.ofReal ((2 : ℝ) ^ D.T) ^ 2 *
      ((ν (D.fγ i)).prod (volume.prod volume)) (D.bandPairs N κ i ρ U G) ≤
      ENNReal.ofReal (cap * (2 * ρ / δ N r + 2) * ((100 * κ) ^ 3 * |(D.fQ i).det|)) *
        volume U := by
  set γ := D.fγ i
  have hδ : 0 < δ N r := by unfold δ; positivity
  set Gb : EuclideanSpace ℝ (Fin 3) → ℝ := fun z =>
    G (movingBasePoint ((2 : ℝ) ^ D.T) (((D.fj i : ℕ) : ℝ)) (100 * κ) (D.fc i) (D.fu i) (D.fQ i) z)
  have hGb : Measurable Gb := hG.comp (measurable_movingBasePoint _ _ _ _ _ _)
  have hbase := continuous_base_inc D.T (((D.fj i : ℕ) : ℝ)) κ (D.fc i) (D.fu i) (D.fQ i)
  set X : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) := D.Good γ ∩ {p | |D.B γ * (x p.1 p.2) 3 -
      G (base D.T (((D.fj i : ℕ) : ℝ)) κ (D.fc i) (D.fu i) (D.fQ i) p.1 p.2)| ≤ ρ} with hX
  have hx3 : Continuous (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => (x p.1 p.2) 3) := by
    simp only [x]; fun_prop
  have hXm : MeasurableSet X := (h.Good_meas γ).inter (measurableSet_le
    ((measurable_const.mul hx3.measurable).sub (hG.comp hbase.measurable)).abs measurable_const)
  refine h.scaled_pair_le (ν γ) γ (gr γ) (hgr γ) (hmapr γ) (bandBins Gb ρ (δ N r))
    (measurableSet_bandBins hGb ρ _) (by positivity) hcap (count_bandBins_le Gb hρ hδ) X hXm
    (fun p hp => h.Good_sub γ hp.1) ?_ hκ i U hU _ ?_
  · intro p hp
    refine ⟨hGood γ p hp.1, obs_mem_bandBins hδ Gb ?_⟩
    have e : Gb (obs (D.B γ) (δ N r) p).1 =
        G (base D.T (((D.fj i : ℕ) : ℝ)) κ (D.fc i) (D.fu i) (D.fQ i) p.1 p.2) := by
      simp only [Gb]
      rw [← base_eq_movingBasePoint]
    rw [e]
    exact hp.2
  · intro p hp
    obtain ⟨hG', hblk⟩ := bandPairs_sub hp
    exact ⟨⟨hG', hp.2.2⟩, hblk, hp.2.1⟩

/-- **Band bound through the world equation's window at one depth.** -/
theorem Hyp.band_window_le (h : D.Hyp N M₀ D₀ L E) (ν : Fin D.W → Measure (ℕ × (Fin 6 → ℝ)))
    [∀ γ, SFinite (ν γ)] {r : ℝ} (gr : Fin D.W → EuclideanSpace ℝ (Fin 3) × ℤ → ℝ≥0∞)
    (hgr : ∀ γ, Measurable (gr γ))
    (hmapr : ∀ γ, Measure.map (obs (D.B γ) (δ N r)) (((ν γ).prod volume).restrict (E γ)) =
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count).withDensity (gr γ))
    {cap : ℝ} (hcap : 0 ≤ cap)
    (hGood : ∀ γ, ∀ p ∈ D.Good γ, gr γ (obs (D.B γ) (δ N r) p) ≤ ENNReal.ofReal cap)
    (Pw : Fin D.W → MvPolynomial (Fin 4) ℝ) (hPw : ∀ γ, (Pw γ).totalDegree ≤ 2) {K : ℝ}
    (hK : 0 < K)
    (hwin : ∀ γ, ∀ p ∈ D.Good γ, |eval (x p.1 p.2) (Pw γ)| ≤ K ∧
      D.B γ / K ≤ |eval (x p.1 p.2) (pderiv 3 (Pw γ))|)
    {κ : ℝ} (hκ : 2 ≤ κ) (i : Fin D.J) {ρ : ℝ} (U : Set (EuclideanSpace ℝ (Fin 3)))
    (hU : MeasurableSet U) (G : EuclideanSpace ℝ (Fin 3) → ℝ) :
    ENNReal.ofReal ((2 : ℝ) ^ D.T) ^ 2 *
      ((ν (D.fγ i)).prod (volume.prod volume)) (D.bandPairs N κ i ρ U G) ≤
      ENNReal.ofReal (cap * (16 * (1 + K ^ 2 / δ N r)) * ((100 * κ) ^ 3 * |(D.fQ i).det|)) *
        volume U := by
  set γ := D.fγ i
  have hδ : 0 < δ N r := by unfold δ; positivity
  have hB := h.Bpos γ
  have hβ : 0 < D.B γ / K := div_pos hB hK
  have hn : 16 * (1 + K / (D.B γ / K * (δ N r / D.B γ))) = 16 * (1 + K ^ 2 / δ N r) := by
    congr 2
    field_simp
  have hfib := count_hidClosed_le (Pw γ) (hPw γ) hK.le hβ (div_pos hδ hB)
  rw [hn] at hfib
  have hXm : MeasurableSet (D.Good γ) := h.Good_meas γ
  refine h.scaled_pair_le (ν γ) γ (gr γ) (hgr γ) (hmapr γ) _ (measurableSet_hidClosed _ _ _ _)
    (by positivity) hcap hfib (D.Good γ) hXm (h.Good_sub γ) ?_ hκ i U hU _ ?_
  · intro p hp
    exact ⟨hGood γ p hp, obs_mem_hidClosed hB hδ _ (hwin γ p hp).1 (hwin γ p hp).2⟩
  · intro p hp
    obtain ⟨hG', hblk⟩ := bandPairs_sub hp
    exact ⟨hG', hblk, hp.2.1⟩

end PrepData

end Submission.Obl.k4_compatible_pair_frame_preparation.Construction
