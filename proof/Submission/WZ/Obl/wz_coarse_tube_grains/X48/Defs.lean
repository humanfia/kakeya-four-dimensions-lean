-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.X48.Defs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
/-!
# Abbreviations for the frozen bindings (ported from o151, session x0448, Defs.lean)

Each abbreviation below is, verbatim, one of the `∀X, X = (...) →` bindings of the frozen
statement of `WangZahlLot.wz_broad_grains_move_one`, specialised to
`V = LeanEval.Analysis.WangZahlKakeya.Space`, `μ = volume`, `ι = fun p i => p i` and
`M = MeasurableSet`.  `Broad` is the pointwise broadness clause of `J`.
-/

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_tube_grains.X48

abbrev V := LeanEval.Analysis.WangZahlKakeya.Space
abbrev μ : Set V → ENNReal := MeasureTheory.volume
abbrev ι (p : V) (i : Fin 3) : ℝ := p i
abbrev M : Set V → Prop := MeasurableSet

abbrev O := ENNReal.ofReal

abbrev q := (fun(n:ℕ)(s:Set (Fin n))=>(s.ncard:ℝ))

abbrev I := Metric.ball (0:V) 1

abbrev T := (fun(d:ℝ)(p u:V)=>Metric.thickening d (segment ℝ p (p+u)))

abbrev Q := (fun(u:V)(t r:ℝ)=>{p:V|abs (inner ℝ u p-t)≤r})

abbrev X := (fun(d:ℝ)(n:ℕ)(x v:Fin n→V)=>∀i j,i≠j→μ (T d (x i) (v i)∩T d (x j) (v j))≤1/2*μ (T d (x i) (v i)))

abbrev K := (fun(d m:ℝ)(n:ℕ)(x v:Fin n→V)=>∀W,Convex ℝ W→O (q n {i|T d (x i) (v i)⊆W}*d^2)≤O m*μ W)

abbrev F := (fun(d l:ℝ)(n:ℕ)(x v:Fin n→V)=>∀(u:V)(t r:ℝ),‖u‖=1→0<r→O (q n {i|T d (x i) (v i)⊆I∩Q u t r})≤O (l*n)*μ (I∩Q u t r))

abbrev A := (fun(d η m l:ℝ)(n:ℕ)(x v:Fin n→V)(Y:Fin n→Set V)=>0<n∧(∀i,‖v i‖=1∧T d (x i) (v i)⊆I∧M (Y i)∧Y i⊆T d (x i) (v i))∧X d n x v∧O (d^η*n*d^2)≤∑i,μ (Y i)∧K d m n x v∧F d l n x v)

abbrev P := (fun(a b c:ℝ)(z:V)(e:V≃ₗᵢ[ℝ]V)=>{p:V|abs (ι (e (p-z)) 0)≤a/2∧abs (ι (e (p-z)) 1)≤b/2∧abs (ι (e (p-z)) 2)≤c/2})

end WangZahlLot.Obl.wz_coarse_tube_grains.X48
