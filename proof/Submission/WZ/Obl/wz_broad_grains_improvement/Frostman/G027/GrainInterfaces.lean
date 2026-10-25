-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.Frostman.G027.GrainInterfaces.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.Frostman.G027.Slices

/- Adapted from the internal o015/x0589 assembly at effb3d2,
   WangZahlLot/Obl/wz_frostman_all_scales_volume/G027/GrainInterfaces.lean; original session credits below are retained. -/

namespace WangZahlLot.Obl.wz_broad_grains_improvement.Frostman.G027

/-- Tenfold concentric dilation of an exact unit-segment tube. -/
def DilatedTube : ℝ → Space → Space → Set Space :=
  fun (ρ : ℝ) (z w : Space) => Metric.thickening (10 * ρ)
  (segment ℝ (z - (9 / 2 : ℝ) • w) (z + (11 / 2 : ℝ) • w))

/-- The weak covers strengthened by disjoint fibres in fixed dilates. -/
def SeparatedScales (η δ : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ r : ℝ, δ ≤ r → r ≤ 1 → ∃ ρ : ℝ,
  r ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ δ ^ (-η) * r ∧ ∃ k : ℕ, 0 < k ∧
  ∃ z w : Fin k → Space, (∀ j, ‖w j‖ = 1) ∧
  (∀ j j', j ≠ j' → MeasureTheory.volume (Tube ρ (z j) (w j) ∩ Tube ρ (z j') (w j')) ≤
    (1 / 2 : ENNReal) * MeasureTheory.volume (Tube ρ (z j) (w j))) ∧
  (∀ i, ∃! j, Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)) ∧
  (∀ j, ∃ i, Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)) ∧
  (∀ j j', (Set.ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)} : ℝ) ≤
    δ ^ (-η) * (Set.ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j') (w j')} : ℝ)) ∧
  (∀ j, ∀ W : Set Space, Convex ℝ W →
    ENNReal.ofReal ((Set.ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j) ∧
      Tube δ (x i) (v i) ⊆ W} : ℝ) * ρ ^ 2) ≤
    ENNReal.ofReal (δ ^ (-η) *
      (Set.ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)} : ℝ)) *
        MeasureTheory.volume W) ∧
  (∀ i j j', Tube δ (x i) (v i) ⊆ DilatedTube ρ (z j) (w j) →
    Tube δ (x i) (v i) ⊆ DilatedTube ρ (z j') (w j') → j = j')

/-- Upper covering regularity on intervals; no lower regularity is assumed. -/
def ADCover : ℝ → ℝ → ℝ → Set ℝ → Prop :=
  fun (d α C : ℝ) (B : Set ℝ) =>
  ∀ r R a : ℝ, d ≤ r → r ≤ R → ∃ (m : ℕ) (c : Fin m → ℝ),
    B ∩ Set.Icc a (a + R) ⊆ (⋃ j, Metric.closedBall (c j) r) ∧
    (m : ℝ) ≤ C * (R / r) ^ α

def SeparatedExamples : ℝ → Prop :=
  fun (s : ℝ) => ∀ η d0 : ℝ, 0 < η → 0 < d0 → ∃ δ : ℝ,
  0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1 / 100 : ℝ) ∧
  ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    DenseFamily η δ n x v Y ∧ SeparatedScales η δ n x v ∧
      MeasureTheory.volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ s)

def LipschitzGrainExamples : ℝ → Prop :=
  fun (σ : ℝ) => ∀ η d0 : ℝ, 0 < η → 0 < d0 → ∃ δ : ℝ,
  0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1 / 100 : ℝ) ∧
  ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    DenseFamily η δ n x v Y ∧ SeparatedScales η δ n x v ∧ (∀ i, IsCompact (Y i)) ∧
    MeasureTheory.volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)) ∧
    ∃ (f : ℝ → ℝ) (P : Space → Space), (LipschitzWith 1 f) ∧ (∀ z : ℝ, z ∈ Set.Icc (-1) 1 →
      ADCover δ (1 - σ) (δ ^ (-η)) (projectedSlice f (⋃ i, Y i) z)) ∧
    LipschitzWith 1 P ∧ (∀ p, p ∈ (⋃ i, Y i) → ‖P p‖ = 1) ∧
    (∀ i p, p ∈ Y i → |inner ℝ (v i) (P p)| ≤ δ) ∧
    (∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 → ∀ p : Space, p ∈ (⋃ i, Y i) →
      ADCover ρ (1 - σ) (δ ^ (-η))
        ((fun q : Space => inner ℝ (P p) q) ''
          ((⋃ i, Y i) ∩ Metric.ball p (Real.sqrt ρ))))

def C2GrainExamples : ℝ → Prop :=
  fun (σ : ℝ) => ∀ η d0 : ℝ, 0 < η → 0 < d0 → ∃ δ : ℝ,
  0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1 / 100 : ℝ) ∧
  ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    DenseFamily η δ n x v Y ∧ SeparatedScales η δ n x v ∧ (∀ i, IsCompact (Y i)) ∧
    MeasureTheory.volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)) ∧
    ∃ (f : ℝ → ℝ) (P : Space → Space), (ContDiff ℝ 2 f ∧ ∀ z : ℝ, z ∈ Set.Icc (-1) 1 →
      |f z| ≤ 1 ∧ |deriv f z| ≤ 1 ∧ |deriv (deriv f) z| ≤ 1) ∧ (∀ z : ℝ, z ∈ Set.Icc (-1) 1 →
      ADCover δ (1 - σ) (δ ^ (-η)) (projectedSlice f (⋃ i, Y i) z)) ∧
    LipschitzWith 1 P ∧ (∀ p, p ∈ (⋃ i, Y i) → ‖P p‖ = 1) ∧
    (∀ i p, p ∈ Y i → |inner ℝ (v i) (P p)| ≤ δ) ∧
    (∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 → ∀ p : Space, p ∈ (⋃ i, Y i) →
      ADCover ρ (1 - σ) (δ ^ (-η))
        ((fun q : Space => inner ℝ (P p) q) ''
          ((⋃ i, Y i) ∩ Metric.ball p (Real.sqrt ρ))))

def NonsingularSliceExamples : ℝ → Prop :=
  fun (σ : ℝ) => ∀ η d0 : ℝ, 0 < η → 0 < d0 → ∃ δ : ℝ,
  0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1 / 100 : ℝ) ∧
  ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    DenseFamily η δ n x v Y ∧ (∀ i, IsCompact (Y i)) ∧
    (∀ i, (1 / 2 : ℝ) ≤ |v i 2|) ∧ GlobalFrostman η δ n x v ∧
    ∃ f : ℝ → ℝ, RegularSlope f ∧
      ∀ z : ℝ, z ∈ Set.Icc (-1) 1 →
        MeasureTheory.volume (projectedSlice f (⋃ i, Y i) z) ≤
          ENNReal.ofReal (δ ^ (σ / 8) / 2)

end WangZahlLot.Obl.wz_broad_grains_improvement.Frostman.G027
