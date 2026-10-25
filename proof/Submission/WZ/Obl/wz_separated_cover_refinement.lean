-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_cover_refinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_separated_cover_refinement.Refinement
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_separated_cover_refinement`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_separated_cover_refinement`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_separated_cover_refinement/`
belong to this obligation.
-/

theorem WangZahlLot.wz_separated_cover_refinement : (fun (T:ℝ→(EuclideanSpace ℝ (Fin 3))→(EuclideanSpace ℝ (Fin 3))→Set (EuclideanSpace ℝ (Fin 3)))=>(fun (H:ℝ→ℝ→(n:ℕ)→(Fin n→(EuclideanSpace ℝ (Fin 3)))→(Fin n→(EuclideanSpace ℝ (Fin 3)))→(Fin n→Set (EuclideanSpace ℝ (Fin 3)))→Prop)=>(fun (D:ℝ→(EuclideanSpace ℝ (Fin 3))→(EuclideanSpace ℝ (Fin 3))→Set (EuclideanSpace ℝ (Fin 3)))=>(fun (S:ℝ→ℝ→(n:ℕ)→(Fin n→(EuclideanSpace ℝ (Fin 3)))→(Fin n→(EuclideanSpace ℝ (Fin 3)))→Prop)=>(fun (A:ℝ→ℝ→(n:ℕ)→(Fin n→(EuclideanSpace ℝ (Fin 3)))→(Fin n→(EuclideanSpace ℝ (Fin 3)))→Prop)=>∀ε:ℝ,0<ε→∃η d1:ℝ,0<η∧0<d1∧∀δ:ℝ,0<δ→δ≤d1→δ≤(1/100:ℝ)→∀(n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3))) (Y:Fin n→Set (EuclideanSpace ℝ (Fin 3))),H η δ n x v Y→A η δ n x v→∃(m:ℕ) (a:Fin m→Fin n),Function.Injective a∧H ε δ m (fun i=>x (a i)) (fun i=>v (a i)) (fun i=>Y (a i))∧S ε δ m (fun i=>x (a i)) (fun i=>v (a i))) (fun (η δ:ℝ) (n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3)))=>∀r:ℝ,δ≤r→ r≤1→∃ρ:ℝ,r≤ρ∧ρ≤1∧ρ≤δ^(-η)*r∧∃k:ℕ,0<k∧∃z w:Fin k→(EuclideanSpace ℝ (Fin 3)),(∀j,‖w j‖=1)∧(∀j j',j≠j'→MeasureTheory.volume (T ρ (z j) (w j)∩T ρ (z j') (w j'))≤(1/2:ENNReal)*MeasureTheory.volume (T ρ (z j) (w j)))∧(∀i,∃! j,T δ (x i) (v i)⊆T ρ (z j) (w j))∧(∀j,∃i,T δ (x i) (v i)⊆T ρ (z j) (w j))∧(∀j j',(Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j) (w j)}:ℝ)≤δ^(-η)*(Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j') (w j')}:ℝ))∧(∀j,∀W:Set (EuclideanSpace ℝ (Fin 3)),Convex ℝ W→ENNReal.ofReal ((Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j) (w j)∧T δ (x i) (v i)⊆W}:ℝ)*ρ^2)≤ENNReal.ofReal (δ^(-η)*(Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j) (w j)}:ℝ))*MeasureTheory.volume W))) (fun (η δ:ℝ) (n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3)))=>∀r:ℝ,δ≤r→ r≤1→∃ρ:ℝ,r≤ρ∧ρ≤1∧ρ≤δ^(-η)*r∧∃k:ℕ,0<k∧∃z w:Fin k→(EuclideanSpace ℝ (Fin 3)),(∀j,‖w j‖=1)∧(∀j j',j≠j'→MeasureTheory.volume (T ρ (z j) (w j)∩T ρ (z j') (w j'))≤(1/2:ENNReal)*MeasureTheory.volume (T ρ (z j) (w j)))∧(∀i,∃! j,T δ (x i) (v i)⊆T ρ (z j) (w j))∧(∀j,∃i,T δ (x i) (v i)⊆T ρ (z j) (w j))∧(∀j j',(Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j) (w j)}:ℝ)≤δ^(-η)*(Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j') (w j')}:ℝ))∧(∀j,∀W:Set (EuclideanSpace ℝ (Fin 3)),Convex ℝ W→ENNReal.ofReal ((Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j) (w j)∧T δ (x i) (v i)⊆W}:ℝ)*ρ^2)≤ENNReal.ofReal (δ^(-η)*(Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j) (w j)}:ℝ))*MeasureTheory.volume W)∧(∀i j j',T δ (x i) (v i)⊆D ρ (z j) (w j)→T δ (x i) (v i)⊆D ρ (z j') (w j')→j=j'))) (fun (ρ:ℝ) (z w:(EuclideanSpace ℝ (Fin 3)))=>Metric.thickening (10*ρ) (segment ℝ (z-(9/2:ℝ) • w) (z+(11/2:ℝ) • w)))) (fun (η δ:ℝ) (n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3))) (Y:Fin n→Set (EuclideanSpace ℝ (Fin 3)))=>0<n∧(∀i,‖v i‖=1)∧(∀i,T δ (x i) (v i)⊆Metric.ball 0 1)∧(∀i j,i≠j→MeasureTheory.volume (T δ (x i) (v i)∩T δ (x j) (v j))≤(1/2:ENNReal)*MeasureTheory.volume (T δ (x i) (v i)))∧(∀i,MeasurableSet (Y i))∧(∀i,Y i⊆T δ (x i) (v i))∧ENNReal.ofReal (δ^η*(n:ℝ)*δ^2)≤Finset.sum Finset.univ (fun i=>MeasureTheory.volume (Y i)))) (fun (δ:ℝ) (x v:(EuclideanSpace ℝ (Fin 3)))=>Metric.thickening δ (segment ℝ x (x+v))) := by
  simpa only [WangZahlLot.Obl.wz_separated_cover_refinement.Dense,
    WangZahlLot.Obl.wz_separated_cover_refinement.Weak,
    WangZahlLot.Obl.wz_separated_cover_refinement.Strong,
    WangZahlLot.Obl.wz_separated_cover_refinement.CoverAt,
    WangZahlLot.Obl.wz_separated_cover_refinement.SeparatedAt,
    WangZahlLot.Obl.wz_separated_cover_refinement.Tube,
    WangZahlLot.Obl.wz_separated_cover_refinement.Dilate, and_assoc] using
    WangZahlLot.Obl.wz_separated_cover_refinement.refinement
