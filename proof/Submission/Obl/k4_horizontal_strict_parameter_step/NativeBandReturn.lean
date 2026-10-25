/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at a5c0b1bcb6dacb66c2e29bec68dd8eae37c23e9d, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeBandReturn.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeMenuBounds

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_critical_derivative_evaluation_lists

noncomputable section

namespace NativeModel

variable {α : Type} [MeasurableSpace α] (cfg : NativeModel α)

/-- Every query sheet with the observed colour has the same physical jitter
error. The query need not be either member of the observed pair. -/
theorem observed_menu_jitter_error {k : ℕ} {s ε D a χ M δ A : ℝ} {m : ℕ}
    {AH : Fin m → Set α} {group : Fin m → Fin 3 → ℤ} {hH : Fin m → Fin 6 → ℝ}
    {σ : Measure (α × ℝ)}
    (H : LayerAt cfg.N cfg.d cfg.e₀ cfg.π cfg.b k ε σ D a m AH group hH)
    {G : Set (α × ℝ)}
    (T : ObservedPairs G (fun i => AH i ×ˢ (univ : Set ℝ))
      (fun i => cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i)))
    (frame : (Fin 3 → ℤ) × Fin (2 ^ cfg.T k s) → ComparisonFrame)
    (hframe : ∀ g j, (frame (g, j)).velocity = χ * (g 0 : ℝ))
    (L : Fin (cfg.n k s) → Fin 4 → ℝ) (hL : ∀ i (e : Fin 3), |L i e.succ| ≤ M)
    (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k) (hM : 0 ≤ M)
    (hD : 0 < D) (hD1 : D ≤ 1) (hχ : 0 < χ) (hχ1 : χ ≤ 1)
    (hχeq : χ = cfg.N k ^ (-cfg.e₀)) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hround : let B := cfg.N k ^ ε + M * (1 + 6 * cfg.K k)
      2 * B * δ + (8 * B / D) * (3 * χ + (4 * (3 * cfg.K k) + 5) * δ) ≤ A)
    (htime : ∀ p ∈ G, p.2 ∈ Icc (0 : ℝ) 1)
    (hcoeff : ∀ p ∈ G, ∀ e, |cfg.b k p.1 e| ≤ 2 * cfg.K k)
    (hcontact : ∀ p ∈ G, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ χ)
    (p : α × ℝ) (hp : p ∈ G) (i : T.Index group (cfg.j k s))
    (hcolour : T.colour group (cfg.j k s) i =
      T.colour group (cfg.j k s) (T.source group (cfg.j k s) (T.mark p)))
    (z : Fin 3 → ℝ)
    (hcell : baseMesh δ z = baseMesh δ (physicalBase (cfg.b k p.1) p.2)) :
    let f := T.physicalPredictors group (cfg.j k s) frame hH L i
    let v := (T.markedFrame group (cfg.j k s) frame (T.mark p)).velocity
    |predictor f p.2 (cfg.b k p.1 0) (cfg.b k p.1 1) -
      predictor f (z 0) (reconstructBase v z 1) (reconstructBase v z 2)| ≤ A := by
  let v := (T.markedFrame group (cfg.j k s) frame (T.mark p)).velocity
  let B := cfg.N k ^ ε + M * (1 + 6 * cfg.K k)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hv : |v| ≤ 3 * cfg.K k := by
    dsimp [v, ObservedPairs.markedFrame]
    rw [hframe]
    exact (cfg.observed_reference_bounds H T hK hD hD1 hχ hχ1 hχeq hcoeff
      (T.source group (cfg.j k s) (T.mark p))).1
  have hb : |cfg.b k p.1 0| ≤ 3 * cfg.K k := (hcoeff p hp 0).trans (by linarith)
  have hg := (H.2.2.1 (T.old (T.mark p))).1 p.1 (T.decode_old p hp).1
  have hvel : |cfg.b k p.1 3 - v| ≤ χ := by
    have hcode : ⌊cfg.b k p.1 3 / χ⌋ = group (T.old (T.mark p)) 0 := by
      simpa only [hχeq] using hg.1
    dsimp [v, ObservedPairs.markedFrame]
    rw [hframe]
    simpa only [floorPoint, hcode] using floorPoint_error hχ (cfg.b k p.1 3)
  have htimez := (reconstructBase_jitter hδ hδ1 (htime p hp) hvel
    (hcontact p hp) hχ1 hb hv hcell).1
  have hτ : z 0 ∈ Icc (-1 : ℝ) 2 := by
    have hh := abs_le.mp htimez
    constructor <;> linarith [(htime p hp).1, (htime p hp).2]
  have hd := cfg.observed_menu_derivatives H T frame hframe L hL hN hK hM hD hD1
    hχ hχ1 hχeq hcoeff p hp i hcolour hτ
  exact (predictor_jitter_error hδ hδ1 (htime p hp) hvel (hcontact p hp) hχ1 hb hv
    (by positivity : 0 ≤ 2 * B) (by positivity : 0 ≤ 8 * B / D) hcell
    hd.1 ⟨hd.2.1, hd.2.2⟩).trans hround

/-- A same-colour matching band returns to a graph band for the ORIGINAL
hidden coordinate. The enlargement pays one source fit and two jitter errors. -/
theorem observed_band_return {k : ℕ} {s ε D a χ M δ A r : ℝ} {m : ℕ}
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
    (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k) (hM : 0 ≤ M)
    (hD : 0 < D) (hD1 : D ≤ 1) (hχ : 0 < χ) (hχ1 : χ ≤ 1)
    (hχeq : χ = cfg.N k ^ (-cfg.e₀)) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsource : cfg.N k ^ ε * a ≤ A)
    (hround : let B := cfg.N k ^ ε + M * (1 + 6 * cfg.K k)
      2 * B * δ + (8 * B / D) * (3 * χ + (4 * (3 * cfg.K k) + 5) * δ) ≤ A)
    (htime : ∀ p ∈ G, p.2 ∈ Icc (0 : ℝ) 1)
    (hcoeff : ∀ p ∈ G, ∀ e, |cfg.b k p.1 e| ≤ 2 * cfg.K k)
    (hcontact : ∀ p ∈ G, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ χ)
    (p : α × ℝ) (hp : p ∈ G) (i : T.Index group (cfg.j k s))
    (hcolour : T.colour group (cfg.j k s) i =
      T.colour group (cfg.j k s) (T.source group (cfg.j k s) (T.mark p)))
    (z : Fin 3 → ℝ)
    (hcell : baseMesh δ z = baseMesh δ (physicalBase (cfg.b k p.1) p.2))
    (hband : let x := (T.markedFrame group (cfg.j k s) frame (T.mark p)).coordinates z
      |predictor (T.comparisonPredictors group (cfg.j k s) frame hH L i) (x 0) (x 1) (x 2) -
        predictor (T.comparisonPredictors group (cfg.j k s) frame hH L
          (T.source group (cfg.j k s) (T.mark p))) (x 0) (x 1) (x 2)| ≤ r) :
    |cfg.b k p.1 2 + p.2 * cfg.b k p.1 5 -
      predictor (T.physicalPredictors group (cfg.j k s) frame hH L i)
        p.2 (cfg.b k p.1 0) (cfg.b k p.1 1)| ≤ r + 3 * A := by
  let source := T.source group (cfg.j k s) (T.mark p)
  let f := T.physicalPredictors group (cfg.j k s) frame hH L
  let v := (T.markedFrame group (cfg.j k s) frame (T.mark p)).velocity
  have herr (j : T.Index group (cfg.j k s))
      (hj : T.colour group (cfg.j k s) j = T.colour group (cfg.j k s) source) :=
    cfg.observed_menu_jitter_error H T frame hframe L hL hN hK hM hD hD1 hχ hχ1
      hχeq hδ hδ1 hround htime hcoeff hcontact p hp j hj z hcell
  have heval (j : T.Index group (cfg.j k s))
      (hj : T.colour group (cfg.j k s) j = T.colour group (cfg.j k s) source) :
      let x := (T.markedFrame group (cfg.j k s) frame (T.mark p)).coordinates z
      predictor (T.comparisonPredictors group (cfg.j k s) frame hH L j) (x 0) (x 1) (x 2) =
        predictor (f j) (z 0) (reconstructBase v z 1) (reconstructBase v z 2) := by
    rw [T.comparisonPredictors_eq_rechart group (cfg.j k s) frame hH L j, hj]
    exact (frame (T.colour group (cfg.j k s) source)).rechart_coordinates (f j) z
      (hframeH _ _).ne' (hframeD _ _).ne'
  dsimp only at hband
  rw [heval i hcolour, heval source rfl] at hband
  have hs := (cfg.observed_source_fit H T frame L htime p hp).trans hsource
  have hse := herr source rfl
  have hie := herr i hcolour
  have hbs : |predictor (f source) (z 0) (reconstructBase v z 1) (reconstructBase v z 2) -
      predictor (f i) (z 0) (reconstructBase v z 1) (reconstructBase v z 2)| ≤ r := by
    simpa only [abs_sub_comm] using hband
  have hpair : |predictor (f source) p.2 (cfg.b k p.1 0) (cfg.b k p.1 1) -
      predictor (f i) p.2 (cfg.b k p.1 0) (cfg.b k p.1 1)| ≤ A + r + A := by
    calc
      _ ≤ |predictor (f source) p.2 (cfg.b k p.1 0) (cfg.b k p.1 1) -
          predictor (f source) (z 0) (reconstructBase v z 1) (reconstructBase v z 2)| +
        |predictor (f source) (z 0) (reconstructBase v z 1) (reconstructBase v z 2) -
          predictor (f i) p.2 (cfg.b k p.1 0) (cfg.b k p.1 1)| := abs_sub_le _ _ _
      _ ≤ A + (r + A) := add_le_add hse ((abs_sub_le _
        (predictor (f i) (z 0) (reconstructBase v z 1) (reconstructBase v z 2)) _).trans
          (add_le_add hbs (by simpa only [abs_sub_comm] using hie)))
      _ = _ := by ring
  exact (abs_sub_le _ (predictor (f source) p.2 (cfg.b k p.1 0) (cfg.b k p.1 1)) _).trans
    ((add_le_add hs hpair).trans_eq (by ring))

end NativeModel

end

end Submission.Obl.k4_horizontal_strict_parameter_step
