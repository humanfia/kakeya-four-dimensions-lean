-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_grains_c2_regularization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_ad_projection_dichotomy
import Submission.WZ.Obl.wz_slab_local_linearity
import Submission.WZ.Obl.wz_multiscale_c2_extraction
import Submission.WZ.Obl.wz_c2_slope_normalization
import Submission.WZ.Obl.wz_grains_c2_regularization.Glue
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_grains_c2_regularization`

Sticky Proposition 5.1 (Assouad Proposition 6.4), split along sticky Section 5:

* `wz_ad_projection_dichotomy`: sticky Theorem 5.2 (projection dichotomy, Section 8);
* `wz_slab_local_linearity`: Theorem 5.2 implies sticky Lemma 5.3 (local linearity on a slab);
* `wz_multiscale_c2_extraction`: Lemma 5.3 implies, at the critical deficit, that Lipschitz
  examples with a slope bounded by three yield C2 examples with power losses
  (sticky Lemmas 5.4-5.5, Corollary 5.6, Proposition 5.7);
* `wz_c2_slope_normalization`: the final mild rescaling normalizes the C2 bounds to one.

The glue bounds the slope by an isometry (`bounded_examples`, proved in `BoundedSlope.lean`)
and composes the four children. The abbreviations of the children are bound by equations and
instantiated with `rfl`.
-/

theorem WangZahlLot.wz_grains_c2_regularization : (fun (T:ℝ→(EuclideanSpace ℝ (Fin 3))→(EuclideanSpace ℝ (Fin 3))→Set (EuclideanSpace ℝ (Fin 3)))=>(fun (H:ℝ→ℝ→(n:ℕ)→(Fin n→(EuclideanSpace ℝ (Fin 3)))→(Fin n→(EuclideanSpace ℝ (Fin 3)))→(Fin n→Set (EuclideanSpace ℝ (Fin 3)))→Prop)=>(fun (D:ℝ→(EuclideanSpace ℝ (Fin 3))→(EuclideanSpace ℝ (Fin 3))→Set (EuclideanSpace ℝ (Fin 3)))=>(fun (S:ℝ→ℝ→(n:ℕ)→(Fin n→(EuclideanSpace ℝ (Fin 3)))→(Fin n→(EuclideanSpace ℝ (Fin 3)))→Prop)=>(fun (AD:ℝ→ℝ→ℝ→Set ℝ→Prop)=>(fun (PS:(ℝ→ℝ)→Set (EuclideanSpace ℝ (Fin 3))→ℝ→Set ℝ)=>(fun (X:ℝ→Prop)=>(fun (L:ℝ→Prop)=>(fun (C:ℝ→Prop)=>∀σ:ℝ,0<σ→σ<1→(∀t:ℝ,t<σ→X t)→(∀t:ℝ,σ<t→¬X t)→L σ→C σ) (fun (σ:ℝ)=>∀η d0:ℝ,0<η→0<d0→∃δ:ℝ,0<δ∧δ≤d0∧δ≤(1/100:ℝ)∧∃(n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3))) (Y:Fin n→Set (EuclideanSpace ℝ (Fin 3))),H η δ n x v Y∧S η δ n x v∧(∀i,IsCompact (Y i))∧MeasureTheory.volume (⋃ i,Y i)≤ENNReal.ofReal (δ^(σ-η))∧∃(f:ℝ→ℝ) (P:(EuclideanSpace ℝ (Fin 3))→(EuclideanSpace ℝ (Fin 3))),(ContDiff ℝ 2 f∧∀z:ℝ,z ∈ Set.Icc (-1) 1→|f z|≤1∧|deriv f z|≤1∧|deriv (deriv f) z|≤1)∧(∀z:ℝ,z ∈ Set.Icc (-1) 1→AD δ (1-σ) (δ^(-η)) (PS f (⋃ i,Y i) z))∧LipschitzWith 1 P∧(∀p,p ∈ (⋃ i,Y i)→‖P p‖=1)∧(∀i p,p ∈ Y i→|inner ℝ (v i) (P p)|≤δ)∧(∀ρ:ℝ,δ≤ρ→ρ≤1→∀p:(EuclideanSpace ℝ (Fin 3)),p ∈ (⋃ i,Y i)→AD ρ (1-σ) (δ^(-η)) ((fun q:(EuclideanSpace ℝ (Fin 3))=>inner ℝ (P p) q) '' ((⋃ i,Y i)∩Metric.ball p (Real.sqrt ρ)))))) (fun (σ:ℝ)=>∀η d0:ℝ,0<η→0<d0→∃δ:ℝ,0<δ∧δ≤d0∧δ≤(1/100:ℝ)∧∃(n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3))) (Y:Fin n→Set (EuclideanSpace ℝ (Fin 3))),H η δ n x v Y∧S η δ n x v∧(∀i,IsCompact (Y i))∧MeasureTheory.volume (⋃ i,Y i)≤ENNReal.ofReal (δ^(σ-η))∧∃(f:ℝ→ℝ) (P:(EuclideanSpace ℝ (Fin 3))→(EuclideanSpace ℝ (Fin 3))),(LipschitzWith 1 f)∧(∀z:ℝ,z ∈ Set.Icc (-1) 1→AD δ (1-σ) (δ^(-η)) (PS f (⋃ i,Y i) z))∧LipschitzWith 1 P∧(∀p,p ∈ (⋃ i,Y i)→‖P p‖=1)∧(∀i p,p ∈ Y i→|inner ℝ (v i) (P p)|≤δ)∧(∀ρ:ℝ,δ≤ρ→ρ≤1→∀p:(EuclideanSpace ℝ (Fin 3)),p ∈ (⋃ i,Y i)→AD ρ (1-σ) (δ^(-η)) ((fun q:(EuclideanSpace ℝ (Fin 3))=>inner ℝ (P p) q) '' ((⋃ i,Y i)∩Metric.ball p (Real.sqrt ρ)))))) (fun (s:ℝ)=>∀η d0:ℝ,0<η→0<d0→∃δ:ℝ,0<δ∧δ≤d0∧δ≤(1/100:ℝ)∧∃(n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3))) (Y:Fin n→Set (EuclideanSpace ℝ (Fin 3))),H η δ n x v Y∧S η δ n x v∧MeasureTheory.volume (⋃ i,Y i)≤ENNReal.ofReal (δ^s))) ((fun (f:ℝ→ℝ) (E:Set (EuclideanSpace ℝ (Fin 3))) (z:ℝ)=>{u:ℝ|(u,z) ∈ (fun p:(EuclideanSpace ℝ (Fin 3))=>(p 0+f (p 2)*p 1,p 2)) '' E}))) (fun (d α C:ℝ) (B:Set ℝ)=>∀r R a:ℝ,d≤r→ r≤R→∃(m:ℕ) (c:Fin m→ℝ),B∩Set.Icc a (a+R)⊆(⋃ j,Metric.closedBall (c j) r)∧(m:ℝ)≤C*(R/r)^α)) (fun (η δ:ℝ) (n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3)))=>∀r:ℝ,δ≤r→ r≤1→∃ρ:ℝ,r≤ρ∧ρ≤1∧ρ≤δ^(-η)*r∧∃k:ℕ,0<k∧∃z w:Fin k→(EuclideanSpace ℝ (Fin 3)),(∀j,‖w j‖=1)∧(∀j j',j≠j'→MeasureTheory.volume (T ρ (z j) (w j)∩T ρ (z j') (w j'))≤(1/2:ENNReal)*MeasureTheory.volume (T ρ (z j) (w j)))∧(∀i,∃! j,T δ (x i) (v i)⊆T ρ (z j) (w j))∧(∀j,∃i,T δ (x i) (v i)⊆T ρ (z j) (w j))∧(∀j j',(Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j) (w j)}:ℝ)≤δ^(-η)*(Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j') (w j')}:ℝ))∧(∀j,∀W:Set (EuclideanSpace ℝ (Fin 3)),Convex ℝ W→ENNReal.ofReal ((Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j) (w j)∧T δ (x i) (v i)⊆W}:ℝ)*ρ^2)≤ENNReal.ofReal (δ^(-η)*(Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j) (w j)}:ℝ))*MeasureTheory.volume W)∧(∀i j j',T δ (x i) (v i)⊆D ρ (z j) (w j)→T δ (x i) (v i)⊆D ρ (z j') (w j')→j=j'))) (fun (ρ:ℝ) (z w:(EuclideanSpace ℝ (Fin 3)))=>Metric.thickening (10*ρ) (segment ℝ (z-(9/2:ℝ) • w) (z+(11/2:ℝ) • w)))) (fun (η δ:ℝ) (n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3))) (Y:Fin n→Set (EuclideanSpace ℝ (Fin 3)))=>0<n∧(∀i,‖v i‖=1)∧(∀i,T δ (x i) (v i)⊆Metric.ball 0 1)∧(∀i j,i≠j→MeasureTheory.volume (T δ (x i) (v i)∩T δ (x j) (v j))≤(1/2:ENNReal)*MeasureTheory.volume (T δ (x i) (v i)))∧(∀i,MeasurableSet (Y i))∧(∀i,Y i⊆T δ (x i) (v i))∧ENNReal.ofReal (δ^η*(n:ℝ)*δ^2)≤Finset.sum Finset.univ (fun i=>MeasureTheory.volume (Y i)))) (fun (δ:ℝ) (x v:(EuclideanSpace ℝ (Fin 3)))=>Metric.thickening δ (segment ℝ x (x+v))) := by
  intro σ hσ hσ1 hbelow habove hL
  have hL3 := WangZahlLot.Obl.wz_grains_c2_regularization.bounded_examples (σ := σ) hL
  have hlin := WangZahlLot.wz_slab_local_linearity _ rfl WangZahlLot.wz_ad_projection_dichotomy
  have hW := WangZahlLot.wz_multiscale_c2_extraction _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
    hlin σ hσ hσ1 habove hL3
  exact WangZahlLot.wz_c2_slope_normalization _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
    σ hσ hσ1 hbelow habove hW
