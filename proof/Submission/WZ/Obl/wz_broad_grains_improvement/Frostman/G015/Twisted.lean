-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.Frostman.G015.Twisted.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.Frostman.G015.Reduction

/- Adapted from the internal o015/x0589 assembly at effb3d2,
   WangZahlLot/Obl/wz_frostman_all_scales_volume/G015/Twisted.lean; original session credits below are retained. -/

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

namespace WangZahlLot.Obl.wz_broad_grains_improvement.Frostman.G015

abbrev Tube (δ : ℝ) (x v : Space) : Set Space :=
  Metric.thickening δ (segment ℝ x (x + v))

/-- The common finite-family and average-density hypotheses. -/
def Admissible (η δ : ℝ) (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) : Prop :=
  0 < n ∧ (∀ i, ‖v i‖ = 1) ∧ (∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1) ∧
  (∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
    (1/2 : ENNReal) * volume (Tube δ (x i) (v i))) ∧
  (∀ i, MeasurableSet (Y i)) ∧ (∀ i, Y i ⊆ Tube δ (x i) (v i)) ∧
  ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y i)

/-- The single-scale Frostman convex condition, without a tube-area factor. -/
def GlobalFrostman (η δ : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ W : Set Space, Convex ℝ W →
    ENNReal.ofReal (Set.ncard {i | Tube δ (x i) (v i) ⊆ W} : ℝ) ≤
      ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume W

/-- The slope normalization in the single-scale twisted-projection theorem. -/
def Nonsingular (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ∀ z : ℝ, z ∈ Set.Icc (-1) 1 →
    1 ≤ |deriv f z| ∧ |deriv f z| ≤ 2 ∧ |deriv (deriv f) z| ≤ (1/100 : ℝ)

def twist (f : ℝ → ℝ) (p : Space) : ℝ × ℝ :=
  (p 0 + f (p 2) * p 1, p 2)

/-- A fixed volume deficit persists at arbitrarily small scales and errors. -/
def VolumeCounterexamples : Prop :=
  ∃ s : ℝ, 0 < s ∧ ∀ η d0 : ℝ, 0 < η → 0 < d0 →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1/100 : ℝ) ∧
    ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Admissible η δ n x v Y ∧ AllScales η δ n x v ∧
      volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ s)

/-- The structural child produces a fixed deficit for planar twisted images. -/
def ProjectionCounterexamples : Prop :=
  ∃ s : ℝ, 0 < s ∧ ∀ η d0 : ℝ, 0 < η → 0 < d0 →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1/100 : ℝ) ∧
    ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Admissible η δ n x v Y ∧ (∀ i, (1/2 : ℝ) ≤ |v i 2|) ∧
      GlobalFrostman η δ n x v ∧
      ∃ f : ℝ → ℝ, Nonsingular f ∧
        volume (twist f '' (⋃ i, Y i)) ≤ ENNReal.ofReal (δ ^ s)

/-- The independent analytic child gives an area lower bound. -/
def ProjectionEstimate : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1/100 : ℝ) →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Admissible η δ n x v Y → (∀ i, (1/2 : ℝ) ≤ |v i 2|) →
      GlobalFrostman η δ n x v →
      ∀ f : ℝ → ℝ, Nonsingular f →
        ENNReal.ofReal (δ ^ ε) ≤ volume (twist f '' (⋃ i, Y i))

/-- An upper area deficit contradicts the lower bound at half its exponent. -/
theorem no_projection_counterexamples (hlower : ProjectionEstimate) :
    ¬ ProjectionCounterexamples := by
  rintro ⟨s, hs, hsmall⟩
  obtain ⟨η, hη, d0, hd0, hbound⟩ := hlower (s / 2) (half_pos hs)
  obtain ⟨δ, hδ, hδ0, hδ100, n, x, v, Y, hH, htrans, hF, f, hf, harea⟩ :=
    hsmall η d0 hη hd0
  have hlo := hbound δ hδ hδ0 hδ100 n x v Y hH htrans hF f hf
  have hδ1 : δ < 1 := hδ100.trans_lt (by norm_num)
  have hp : δ ^ s < δ ^ (s / 2) :=
    Real.rpow_lt_rpow_of_exponent_gt hδ hδ1 (by linarith)
  have hp' : ENNReal.ofReal (δ ^ s) < ENNReal.ofReal (δ ^ (s / 2)) :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hp
  exact (not_lt_of_ge (hlo.trans harea)) hp'

/-- Only quantifier negation and the elementary compact-scale reduction remain. -/
theorem statement_of_twisted
    (hextract : VolumeCounterexamples → ProjectionCounterexamples)
    (hlower : ProjectionEstimate) : Statement := by
  apply statement_of_small_scales
  intro ε hε
  by_contra! hfail
  apply no_projection_counterexamples hlower
  apply hextract
  refine ⟨ε, hε, ?_⟩
  intro η d0 hη hd0
  obtain ⟨δ, hδ, hδ0, hδ100, hbad⟩ := hfail 1 (by norm_num) η hη d0 hd0
  simp only [AtScale] at hbad
  push Not at hbad
  obtain ⟨n, x, v, Y, hn, hv, hball, hsep, hm, hY, hdens, hall, hvol⟩ := hbad
  refine ⟨δ, hδ, hδ0, hδ100, n, x, v, Y,
    ⟨hn, hv, hball, hsep, hm, hY, hdens⟩, hall, ?_⟩
  simpa only [one_mul] using hvol.le

end WangZahlLot.Obl.wz_broad_grains_improvement.Frostman.G015
