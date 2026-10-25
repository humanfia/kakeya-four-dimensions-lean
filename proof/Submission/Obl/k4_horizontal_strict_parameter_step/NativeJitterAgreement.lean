/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeJitterAgreement.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeMenuBounds

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_critical_derivative_evaluation_lists

noncomputable section

namespace NativeModel

variable {α : Type} [MeasurableSpace α] (cfg : NativeModel α)

/-- The actual old and true predictors remain near at EVERY shared jitter point
and in the SAME normalized colour chart. This is a pointwise geometric fact
before redistribution of any original incidence mass. -/
theorem observed_pair_jitter_agreement {k : ℕ} {s ε D a χ M δ A : ℝ} {m : ℕ}
    {AH : Fin m → Set α} {group : Fin m → Fin 3 → ℤ} {hH : Fin m → Fin 6 → ℝ}
    {σ : Measure (α × ℝ)}
    (H : LayerAt cfg.N cfg.d cfg.e₀ cfg.π cfg.b k ε σ D a m AH group hH)
    {G : Set (α × ℝ)}
    (T : ObservedPairs G (fun i => AH i ×ˢ (univ : Set ℝ))
      (fun i => cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i)))
    (frame : (Fin 3 → ℤ) × Fin (2 ^ cfg.T k s) → ComparisonFrame)
    (hframe : ∀ g j, (frame (g, j)).velocity = χ * (g 0 : ℝ))
    (hframeH : ∀ g j, 0 < (frame (g, j)).timeScale)
    (hframeD : ∀ g j, 0 < (frame (g, j)).parameterScale)
    (L : Fin (cfg.n k s) → Fin 4 → ℝ) (hL : ∀ i (e : Fin 3), |L i e.succ| ≤ M)
    (hfit : ∀ i l, l ∈ cfg.B k s i → ∀ t ∈ Data.I (cfg.T k s) (cfg.j k s i),
      |cfg.b k l 2 + t * cfg.b k l 5 -
        (L i 0 + L i 1 * t + L i 2 * (cfg.b k l 0 + t * cfg.b k l 3) +
          L i 3 * (cfg.b k l 1 + t * cfg.b k l 4))| ≤ cfg.K k * a)
    (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k) (hM : 0 ≤ M)
    (hD : 0 < D) (hD1 : D ≤ 1) (hχ : 0 < χ) (hχ1 : χ ≤ 1)
    (hχeq : χ = cfg.N k ^ (-cfg.e₀)) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsource : cfg.N k ^ ε * a ≤ A) (hwitness : cfg.K k * a + 2 * M * χ ≤ A)
    (hround : let B := cfg.N k ^ ε + M * (1 + 6 * cfg.K k)
      2 * B * δ + (8 * B / D) * (3 * χ + (4 * (3 * cfg.K k) + 5) * δ) ≤ A)
    (htime : ∀ p ∈ G, p.2 ∈ Icc (0 : ℝ) 1)
    (hcoeff : ∀ p ∈ G, ∀ e, |cfg.b k p.1 e| ≤ 2 * cfg.K k)
    (hcontact : ∀ p ∈ G, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ χ)
    (p : α × ℝ) (hp : p ∈ G) (z : Fin 3 → ℝ)
    (hcell : baseMesh δ z = baseMesh δ (physicalBase (cfg.b k p.1) p.2)) :
    let x := (T.markedFrame group (cfg.j k s) frame (T.mark p)).coordinates z
    |predictor (T.comparisonPredictors group (cfg.j k s) frame hH L
        (T.source group (cfg.j k s) (T.mark p))) (x 0) (x 1) (x 2) -
      predictor (T.comparisonPredictors group (cfg.j k s) frame hH L
        (T.witness group (cfg.j k s) (T.mark p))) (x 0) (x 1) (x 2)| ≤ 4 * A := by
  let r := T.mark p
  let source := T.source group (cfg.j k s) r
  let witness := T.witness group (cfg.j k s) r
  let f := T.physicalPredictors group (cfg.j k s) frame hH L
  let v := (T.markedFrame group (cfg.j k s) frame r).velocity
  let B := cfg.N k ^ ε + M * (1 + 6 * cfg.K k)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hv : |v| ≤ 3 * cfg.K k := by
    dsimp [v, ObservedPairs.markedFrame]
    rw [hframe]
    exact (cfg.observed_reference_bounds H T hK hD hD1 hχ hχ1 hχeq hcoeff source).1
  have hb : |cfg.b k p.1 0| ≤ 3 * cfg.K k := (hcoeff p hp 0).trans (by linarith)
  have hg := (H.2.2.1 (T.old r)).1 p.1 (T.decode_old p hp).1
  have hvel : |cfg.b k p.1 3 - v| ≤ χ := by
    have hcode : ⌊cfg.b k p.1 3 / χ⌋ = group (T.old r) 0 := by
      simpa only [hχeq] using hg.1
    dsimp [v, ObservedPairs.markedFrame]
    rw [hframe]
    simpa only [floorPoint, hcode] using floorPoint_error hχ (cfg.b k p.1 3)
  have htimez := (reconstructBase_jitter hδ hδ1 (htime p hp) hvel
    (hcontact p hp) hχ1 hb hv hcell).1
  have hτ : z 0 ∈ Icc (-1 : ℝ) 2 := by
    have hh := abs_le.mp htimez
    constructor <;> linarith [(htime p hp).1, (htime p hp).2]
  have hderiv (i : T.Index group (cfg.j k s))
      (hi : T.colour group (cfg.j k s) i = T.colour group (cfg.j k s) source) :=
    cfg.observed_menu_derivatives H T frame hframe L hL hN hK hM hD hD1 hχ hχ1
      hχeq hcoeff p hp i hi hτ
  have herror (i : T.Index group (cfg.j k s))
      (hi : T.colour group (cfg.j k s) i = T.colour group (cfg.j k s) source) :
      |predictor (f i) p.2 (cfg.b k p.1 0) (cfg.b k p.1 1) -
        predictor (f i) (z 0) (reconstructBase v z 1) (reconstructBase v z 2)| ≤ A := by
    have hd := hderiv i hi
    exact (predictor_jitter_error hδ hδ1 (htime p hp) hvel (hcontact p hp) hχ1 hb hv
      (by positivity : 0 ≤ 2 * B) (by positivity : 0 ≤ 8 * B / D) hcell
      hd.1 ⟨hd.2.1, hd.2.2⟩).trans hround
  have hs := (cfg.observed_source_fit H T frame L htime p hp).trans hsource
  have hw := (cfg.observed_witness_fit H T frame hframe hχ hχeq L hL hfit
    htime hcontact p hp).trans hwitness
  have hes := herror source rfl
  have hew := herror witness (T.colour_source_eq_witness group (cfg.j k s) r).symm
  have hTimeNe : (T.markedFrame group (cfg.j k s) frame r).timeScale ≠ 0 := (hframeH _ _).ne'
  have hParamNe : (T.markedFrame group (cfg.j k s) frame r).parameterScale ≠ 0 := (hframeD _ _).ne'
  dsimp only
  rw [T.source_evaluation group (cfg.j k s) frame hH L r z hTimeNe hParamNe,
    T.witness_evaluation group (cfg.j k s) frame hH L r z hTimeNe hParamNe]
  have hsource' : |predictor (f source) (z 0) (reconstructBase v z 1)
      (reconstructBase v z 2) - (cfg.b k p.1 2 + p.2 * cfg.b k p.1 5)| ≤ 2 * A := by
    have hes' := hes
    have hs' := hs
    rw [abs_sub_comm] at hes' hs'
    exact (abs_sub_le _ (predictor (f source) p.2 (cfg.b k p.1 0) (cfg.b k p.1 1)) _).trans
      (by linarith)
  have hwitness' : |(cfg.b k p.1 2 + p.2 * cfg.b k p.1 5) -
      predictor (f witness) (z 0) (reconstructBase v z 1) (reconstructBase v z 2)| ≤ 2 * A := by
    exact (abs_sub_le _ (predictor (f witness) p.2 (cfg.b k p.1 0) (cfg.b k p.1 1)) _).trans
      (by linarith [hew, hw])
  exact (abs_sub_le _ (cfg.b k p.1 2 + p.2 * cfg.b k p.1 5) _).trans
    ((add_le_add hsource' hwitness').trans_eq (by ring))

end NativeModel

end

end Submission.Obl.k4_horizontal_strict_parameter_step
