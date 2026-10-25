-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_grains_nonsingular_slices.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_grains_nonsingular_slices.Main
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_grains_nonsingular_slices`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_grains_nonsingular_slices`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_grains_nonsingular_slices/`
belong to this obligation.
-/

theorem WangZahlLot.wz_grains_nonsingular_slices : (fun (T:ℝ→(EuclideanSpace ℝ (Fin 3))→(EuclideanSpace ℝ (Fin 3))→Set (EuclideanSpace ℝ (Fin 3)))=>(fun (H:ℝ→ℝ→(n:ℕ)→(Fin n→(EuclideanSpace ℝ (Fin 3)))→(Fin n→(EuclideanSpace ℝ (Fin 3)))→(Fin n→Set (EuclideanSpace ℝ (Fin 3)))→Prop)=>(fun (D:ℝ→(EuclideanSpace ℝ (Fin 3))→(EuclideanSpace ℝ (Fin 3))→Set (EuclideanSpace ℝ (Fin 3)))=>(fun (S:ℝ→ℝ→(n:ℕ)→(Fin n→(EuclideanSpace ℝ (Fin 3)))→(Fin n→(EuclideanSpace ℝ (Fin 3)))→Prop)=>(fun (AD:ℝ→ℝ→ℝ→Set ℝ→Prop)=>(fun (PS:(ℝ→ℝ)→Set (EuclideanSpace ℝ (Fin 3))→ℝ→Set ℝ)=>(fun (X:ℝ→Prop)=>(fun (C:ℝ→Prop)=>(fun (F:ℝ→ℝ→(n:ℕ)→(Fin n→(EuclideanSpace ℝ (Fin 3)))→(Fin n→(EuclideanSpace ℝ (Fin 3)))→Prop)=>(fun (N:(ℝ→ℝ)→Prop)=>(fun (Q:ℝ→Prop)=>∀σ:ℝ,0<σ→σ<1→(∀t:ℝ,t<σ→X t)→(∀t:ℝ,σ<t→¬X t)→C σ→Q σ) (fun (σ:ℝ)=>∀η d0:ℝ,0<η→0<d0→∃δ:ℝ,0<δ∧δ≤d0∧δ≤(1/100:ℝ)∧∃(n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3))) (Y:Fin n→Set (EuclideanSpace ℝ (Fin 3))),H η δ n x v Y∧(∀i,IsCompact (Y i))∧(∀i,(1/2:ℝ)≤|v i 2|)∧F η δ n x v∧∃f:ℝ→ℝ,N f∧∀z:ℝ,z ∈ Set.Icc (-1) 1→MeasureTheory.volume (PS f (⋃ i,Y i) z)≤ENNReal.ofReal (δ^(σ/8)/2))) (fun (f:ℝ→ℝ)=>ContDiff ℝ 2 f∧∀z:ℝ,z ∈ Set.Icc (-1) 1→1≤|deriv f z|∧|deriv f z|≤2∧|deriv (deriv f) z|≤(1/100:ℝ))) (fun (η δ:ℝ) (n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3)))=>∀W:Set (EuclideanSpace ℝ (Fin 3)),Convex ℝ W→ENNReal.ofReal (Set.ncard {i|T δ (x i) (v i)⊆W}:ℝ)≤ENNReal.ofReal (δ^(-η)*(n:ℝ))*MeasureTheory.volume W)) (fun (σ:ℝ)=>∀η d0:ℝ,0<η→0<d0→∃δ:ℝ,0<δ∧δ≤d0∧δ≤(1/100:ℝ)∧∃(n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3))) (Y:Fin n→Set (EuclideanSpace ℝ (Fin 3))),H η δ n x v Y∧S η δ n x v∧(∀i,IsCompact (Y i))∧MeasureTheory.volume (⋃ i,Y i)≤ENNReal.ofReal (δ^(σ-η))∧∃(f:ℝ→ℝ) (P:(EuclideanSpace ℝ (Fin 3))→(EuclideanSpace ℝ (Fin 3))),(ContDiff ℝ 2 f∧∀z:ℝ,z ∈ Set.Icc (-1) 1→|f z|≤1∧|deriv f z|≤1∧|deriv (deriv f) z|≤1)∧(∀z:ℝ,z ∈ Set.Icc (-1) 1→AD δ (1-σ) (δ^(-η)) (PS f (⋃ i,Y i) z))∧LipschitzWith 1 P∧(∀p,p ∈ (⋃ i,Y i)→‖P p‖=1)∧(∀i p,p ∈ Y i→|inner ℝ (v i) (P p)|≤δ)∧(∀ρ:ℝ,δ≤ρ→ρ≤1→∀p:(EuclideanSpace ℝ (Fin 3)),p ∈ (⋃ i,Y i)→AD ρ (1-σ) (δ^(-η)) ((fun q:(EuclideanSpace ℝ (Fin 3))=>inner ℝ (P p) q) '' ((⋃ i,Y i)∩Metric.ball p (Real.sqrt ρ)))))) (fun (s:ℝ)=>∀η d0:ℝ,0<η→0<d0→∃δ:ℝ,0<δ∧δ≤d0∧δ≤(1/100:ℝ)∧∃(n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3))) (Y:Fin n→Set (EuclideanSpace ℝ (Fin 3))),H η δ n x v Y∧S η δ n x v∧MeasureTheory.volume (⋃ i,Y i)≤ENNReal.ofReal (δ^s))) ((fun (f:ℝ→ℝ) (E:Set (EuclideanSpace ℝ (Fin 3))) (z:ℝ)=>{u:ℝ|(u,z) ∈ (fun p:(EuclideanSpace ℝ (Fin 3))=>(p 0+f (p 2)*p 1,p 2)) '' E}))) (fun (d α C:ℝ) (B:Set ℝ)=>∀r R a:ℝ,d≤r→ r≤R→∃(m:ℕ) (c:Fin m→ℝ),B∩Set.Icc a (a+R)⊆(⋃ j,Metric.closedBall (c j) r)∧(m:ℝ)≤C*(R/r)^α)) (fun (η δ:ℝ) (n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3)))=>∀r:ℝ,δ≤r→ r≤1→∃ρ:ℝ,r≤ρ∧ρ≤1∧ρ≤δ^(-η)*r∧∃k:ℕ,0<k∧∃z w:Fin k→(EuclideanSpace ℝ (Fin 3)),(∀j,‖w j‖=1)∧(∀j j',j≠j'→MeasureTheory.volume (T ρ (z j) (w j)∩T ρ (z j') (w j'))≤(1/2:ENNReal)*MeasureTheory.volume (T ρ (z j) (w j)))∧(∀i,∃! j,T δ (x i) (v i)⊆T ρ (z j) (w j))∧(∀j,∃i,T δ (x i) (v i)⊆T ρ (z j) (w j))∧(∀j j',(Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j) (w j)}:ℝ)≤δ^(-η)*(Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j') (w j')}:ℝ))∧(∀j,∀W:Set (EuclideanSpace ℝ (Fin 3)),Convex ℝ W→ENNReal.ofReal ((Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j) (w j)∧T δ (x i) (v i)⊆W}:ℝ)*ρ^2)≤ENNReal.ofReal (δ^(-η)*(Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j) (w j)}:ℝ))*MeasureTheory.volume W)∧(∀i j j',T δ (x i) (v i)⊆D ρ (z j) (w j)→T δ (x i) (v i)⊆D ρ (z j') (w j')→j=j'))) (fun (ρ:ℝ) (z w:(EuclideanSpace ℝ (Fin 3)))=>Metric.thickening (10*ρ) (segment ℝ (z-(9/2:ℝ) • w) (z+(11/2:ℝ) • w)))) (fun (η δ:ℝ) (n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3))) (Y:Fin n→Set (EuclideanSpace ℝ (Fin 3)))=>0<n∧(∀i,‖v i‖=1)∧(∀i,T δ (x i) (v i)⊆Metric.ball 0 1)∧(∀i j,i≠j→MeasureTheory.volume (T δ (x i) (v i)∩T δ (x j) (v j))≤(1/2:ENNReal)*MeasureTheory.volume (T δ (x i) (v i)))∧(∀i,MeasurableSet (Y i))∧(∀i,Y i⊆T δ (x i) (v i))∧ENNReal.ofReal (δ^η*(n:ℝ)*δ^2)≤Finset.sum Finset.univ (fun i=>MeasureTheory.volume (Y i)))) (fun (δ:ℝ) (x v:(EuclideanSpace ℝ (Fin 3)))=>Metric.thickening δ (segment ℝ x (x+v))) := by
  intro σ hσ hσ1 hbelow habove hC
  change WangZahlLot.Obl.wz_grains_nonsingular_slices.NormalizedExamples σ
  have hgrains : WangZahlLot.Obl.wz_grains_nonsingular_slices.Grains σ := by
    simpa only [WangZahlLot.Obl.wz_grains_nonsingular_slices.Grains,
      WangZahlLot.Obl.wz_grains_nonsingular_slices.AD,
      WangZahlLot.Obl.wz_grains_nonsingular_slices.PS,
      WangZahlLot.Obl.wz_separated_cover_refinement.Dense,
      WangZahlLot.Obl.wz_separated_cover_refinement.Strong,
      WangZahlLot.Obl.wz_separated_cover_refinement.CoverAt,
      WangZahlLot.Obl.wz_separated_cover_refinement.SeparatedAt,
      WangZahlLot.Obl.wz_separated_cover_refinement.Tube,
      WangZahlLot.Obl.wz_separated_cover_refinement.Dilate, and_assoc] using hC
  have hupper : ∀ t : ℝ, σ < t →
      ¬ WangZahlLot.Obl.wz_grains_nonsingular_slices.Extremal t := by
    simpa only [WangZahlLot.Obl.wz_grains_nonsingular_slices.Extremal,
      WangZahlLot.Obl.wz_separated_cover_refinement.Dense,
      WangZahlLot.Obl.wz_separated_cover_refinement.Strong,
      WangZahlLot.Obl.wz_separated_cover_refinement.CoverAt,
      WangZahlLot.Obl.wz_separated_cover_refinement.SeparatedAt,
      WangZahlLot.Obl.wz_separated_cover_refinement.Tube,
      WangZahlLot.Obl.wz_separated_cover_refinement.Dilate, and_assoc] using habove
  have hlower : ∀ t : ℝ, t < σ →
      WangZahlLot.Obl.wz_grains_nonsingular_slices.Extremal t := by
    simpa only [WangZahlLot.Obl.wz_grains_nonsingular_slices.Extremal,
      WangZahlLot.Obl.wz_separated_cover_refinement.Dense,
      WangZahlLot.Obl.wz_separated_cover_refinement.Strong,
      WangZahlLot.Obl.wz_separated_cover_refinement.CoverAt,
      WangZahlLot.Obl.wz_separated_cover_refinement.SeparatedAt,
      WangZahlLot.Obl.wz_separated_cover_refinement.Tube,
      WangZahlLot.Obl.wz_separated_cover_refinement.Dilate, and_assoc] using hbelow
  clear hbelow habove hC
  exact WangZahlLot.Obl.wz_grains_nonsingular_slices.normalized_examples hσ hσ1 hupper hgrains
