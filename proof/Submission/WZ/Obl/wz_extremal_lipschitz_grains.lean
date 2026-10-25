-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.GGXBridge
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormMain
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Exponent
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_extremal_lipschitz_grains`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_extremal_lipschitz_grains/`
belong to this obligation.
-/

theorem WangZahlLot.wz_extremal_lipschitz_grains : (fun (T:ℝ→(EuclideanSpace ℝ (Fin 3))→(EuclideanSpace ℝ (Fin 3))→Set (EuclideanSpace ℝ (Fin 3)))=>(fun (H:ℝ→ℝ→(n:ℕ)→(Fin n→(EuclideanSpace ℝ (Fin 3)))→(Fin n→(EuclideanSpace ℝ (Fin 3)))→(Fin n→Set (EuclideanSpace ℝ (Fin 3)))→Prop)=>(fun (D:ℝ→(EuclideanSpace ℝ (Fin 3))→(EuclideanSpace ℝ (Fin 3))→Set (EuclideanSpace ℝ (Fin 3)))=>(fun (S:ℝ→ℝ→(n:ℕ)→(Fin n→(EuclideanSpace ℝ (Fin 3)))→(Fin n→(EuclideanSpace ℝ (Fin 3)))→Prop)=>(fun (AD:ℝ→ℝ→ℝ→Set ℝ→Prop)=>(fun (PS:(ℝ→ℝ)→Set (EuclideanSpace ℝ (Fin 3))→ℝ→Set ℝ)=>(fun (X:ℝ→Prop)=>(fun (L:ℝ→Prop)=>∀σ:ℝ,0<σ→σ≤2→(∀t:ℝ,t<σ→X t)→(∀t:ℝ,σ<t→¬X t)→σ<1∧L σ) (fun (σ:ℝ)=>∀η d0:ℝ,0<η→0<d0→∃δ:ℝ,0<δ∧δ≤d0∧δ≤(1/100:ℝ)∧∃(n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3))) (Y:Fin n→Set (EuclideanSpace ℝ (Fin 3))),H η δ n x v Y∧S η δ n x v∧(∀i,IsCompact (Y i))∧MeasureTheory.volume (⋃ i,Y i)≤ENNReal.ofReal (δ^(σ-η))∧∃(f:ℝ→ℝ) (P:(EuclideanSpace ℝ (Fin 3))→(EuclideanSpace ℝ (Fin 3))),(LipschitzWith 1 f)∧(∀z:ℝ,z ∈ Set.Icc (-1) 1→AD δ (1-σ) (δ^(-η)) (PS f (⋃ i,Y i) z))∧LipschitzWith 1 P∧(∀p,p ∈ (⋃ i,Y i)→‖P p‖=1)∧(∀i p,p ∈ Y i→|inner ℝ (v i) (P p)|≤δ)∧(∀ρ:ℝ,δ≤ρ→ρ≤1→∀p:(EuclideanSpace ℝ (Fin 3)),p ∈ (⋃ i,Y i)→AD ρ (1-σ) (δ^(-η)) ((fun q:(EuclideanSpace ℝ (Fin 3))=>inner ℝ (P p) q) '' ((⋃ i,Y i)∩Metric.ball p (Real.sqrt ρ)))))) (fun (s:ℝ)=>∀η d0:ℝ,0<η→0<d0→∃δ:ℝ,0<δ∧δ≤d0∧δ≤(1/100:ℝ)∧∃(n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3))) (Y:Fin n→Set (EuclideanSpace ℝ (Fin 3))),H η δ n x v Y∧S η δ n x v∧MeasureTheory.volume (⋃ i,Y i)≤ENNReal.ofReal (δ^s))) ((fun (f:ℝ→ℝ) (E:Set (EuclideanSpace ℝ (Fin 3))) (z:ℝ)=>{u:ℝ|(u,z) ∈ (fun p:(EuclideanSpace ℝ (Fin 3))=>(p 0+f (p 2)*p 1,p 2)) '' E}))) (fun (d α C:ℝ) (B:Set ℝ)=>∀r R a:ℝ,d≤r→ r≤R→∃(m:ℕ) (c:Fin m→ℝ),B∩Set.Icc a (a+R)⊆(⋃ j,Metric.closedBall (c j) r)∧(m:ℝ)≤C*(R/r)^α)) (fun (η δ:ℝ) (n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3)))=>∀r:ℝ,δ≤r→ r≤1→∃ρ:ℝ,r≤ρ∧ρ≤1∧ρ≤δ^(-η)*r∧∃k:ℕ,0<k∧∃z w:Fin k→(EuclideanSpace ℝ (Fin 3)),(∀j,‖w j‖=1)∧(∀j j',j≠j'→MeasureTheory.volume (T ρ (z j) (w j)∩T ρ (z j') (w j'))≤(1/2:ENNReal)*MeasureTheory.volume (T ρ (z j) (w j)))∧(∀i,∃! j,T δ (x i) (v i)⊆T ρ (z j) (w j))∧(∀j,∃i,T δ (x i) (v i)⊆T ρ (z j) (w j))∧(∀j j',(Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j) (w j)}:ℝ)≤δ^(-η)*(Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j') (w j')}:ℝ))∧(∀j,∀W:Set (EuclideanSpace ℝ (Fin 3)),Convex ℝ W→ENNReal.ofReal ((Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j) (w j)∧T δ (x i) (v i)⊆W}:ℝ)*ρ^2)≤ENNReal.ofReal (δ^(-η)*(Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j) (w j)}:ℝ))*MeasureTheory.volume W)∧(∀i j j',T δ (x i) (v i)⊆D ρ (z j) (w j)→T δ (x i) (v i)⊆D ρ (z j') (w j')→j=j'))) (fun (ρ:ℝ) (z w:(EuclideanSpace ℝ (Fin 3)))=>Metric.thickening (10*ρ) (segment ℝ (z-(9/2:ℝ) • w) (z+(11/2:ℝ) • w)))) (fun (η δ:ℝ) (n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3))) (Y:Fin n→Set (EuclideanSpace ℝ (Fin 3)))=>0<n∧(∀i,‖v i‖=1)∧(∀i,T δ (x i) (v i)⊆Metric.ball 0 1)∧(∀i j,i≠j→MeasureTheory.volume (T δ (x i) (v i)∩T δ (x j) (v j))≤(1/2:ENNReal)*MeasureTheory.volume (T δ (x i) (v i)))∧(∀i,MeasurableSet (Y i))∧(∀i,Y i⊆T δ (x i) (v i))∧ENNReal.ofReal (δ^η*(n:ℝ)*δ^2)≤Finset.sum Finset.univ (fun i=>MeasureTheory.volume (Y i)))) (fun (δ:ℝ) (x v:(EuclideanSpace ℝ (Fin 3)))=>Metric.thickening δ (segment ℝ x (x+v))) := by
  change ∀ σ : ℝ, 0 < σ → σ ≤ 2 →
    (∀ t : ℝ, t < σ → WangZahlLot.Obl.wz_extremal_lipschitz_grains.Examples t) →
    (∀ t : ℝ, σ < t → ¬WangZahlLot.Obl.wz_extremal_lipschitz_grains.Examples t) →
    σ < 1 ∧ WangZahlLot.Obl.wz_extremal_lipschitz_grains.Grains σ
  intro σ hσ hσ2 hbelow habove
  have hσ1 := WangZahlLot.Obl.wz_extremal_lipschitz_grains.extremal_exponent_lt_one hbelow
  exact ⟨hσ1, WangZahlLot.Obl.wz_extremal_lipschitz_grains.norm_of_ggx hσ hσ1
    (WangZahlLot.Obl.wz_extremal_lipschitz_grains.ggx_of_examples hσ hσ1 hbelow habove)⟩
