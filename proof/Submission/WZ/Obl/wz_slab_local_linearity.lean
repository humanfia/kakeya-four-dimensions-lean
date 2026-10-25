-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_slab_local_linearity.Final
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_slab_local_linearity`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_slab_local_linearity`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_slab_local_linearity/`
belong to this obligation.
-/

theorem WangZahlLot.wz_slab_local_linearity : ∀ AD,AD=(fun (d α C:ℝ) (B:Set ℝ)=>∀r R a:ℝ,d≤r→ r≤R→∃(m:ℕ) (c:Fin m→ℝ),B∩Set.Icc a (a+R)⊆(⋃ j,Metric.closedBall (c j) r)∧(m:ℝ)≤C*(R/r)^α)→(∀ε:ℝ,0<ε→∃η δ₀:ℝ,0<η∧0<δ₀∧∀δ:ℝ,0<δ→δ≤δ₀→∀F G:Set (EuclideanSpace ℝ (Fin 2)),(∀a ∈ F,∀i:Fin 2,0≤a i∧a i≤1)→(∀b ∈ G,∀i:Fin 2,0≤b i∧b i≤1)→(∀(x:(EuclideanSpace ℝ (Fin 2))) (ρ r:ℝ),δ≤ρ→ρ≤r→∃(m:ℕ) (cc:Fin m→(EuclideanSpace ℝ (Fin 2))),F∩Metric.ball x r⊆(⋃ j,Metric.closedBall (cc j) ρ)∧(m:ℝ)≤δ^(-η)*(r/ρ))→(∀(x:(EuclideanSpace ℝ (Fin 2))) (ρ r:ℝ),δ≤ρ→ρ≤r→∃(m:ℕ) (cc:Fin m→(EuclideanSpace ℝ (Fin 2))),G∩Metric.ball x r⊆(⋃ j,Metric.closedBall (cc j) ρ)∧(m:ℝ)≤δ^(-η)*(r/ρ))→((∃(e b₀:(EuclideanSpace ℝ (Fin 2))) (c:ℝ),‖e‖=1∧(∀(m:ℕ) (cc:Fin m→(EuclideanSpace ℝ (Fin 2))),Metric.thickening δ {a|inner ℝ a e=c}∩F⊆(⋃ j,Metric.closedBall (cc j) δ)→δ^(ε-1)≤(m:ℝ))∧(∀(m:ℕ) (cc:Fin m→(EuclideanSpace ℝ (Fin 2))),Metric.thickening δ (Set.range (fun t:ℝ=>b₀+t • e))∩G⊆(⋃ j,Metric.closedBall (cc j) δ)→δ^(ε-1)≤(m:ℝ)))∨(∀Q:Set (EuclideanSpace ℝ (Fin 2)×EuclideanSpace ℝ (Fin 2)×EuclideanSpace ℝ (Fin 2)),Q⊆F ×ˢ (G ×ˢ G)→(∀(m:ℕ) (cc:Fin m→(EuclideanSpace ℝ (Fin 2)×EuclideanSpace ℝ (Fin 2)×EuclideanSpace ℝ (Fin 2))),Q⊆(⋃ j,Metric.closedBall (cc j) δ)→δ^(η-3)≤(m:ℝ))→∃ρ a L:ℝ,δ≤ρ∧δ^(-η)*ρ≤L∧∀(m:ℕ) (cc:Fin m→ℝ),Set.Icc a (a+L)∩{t:ℝ|∃h ∈ Q,t=inner ℝ h.1 (h.2.1-h.2.2)}⊆(⋃ j,Metric.closedBall (cc j) ρ)→(L/ρ)^(1-ε)≤(m:ℝ))))→∀σ:ℝ,0<σ→σ<1→∀ε:ℝ,0<ε→∃η ρ₀:ℝ,0<η∧0<ρ₀∧∀ρ:ℝ,0<ρ→ρ≤ρ₀→∀(z₀ c₀:ℝ) (Z:Set ℝ) (f:ℝ→ℝ) (K:Finset (Fin 3→ℤ)) (V:(EuclideanSpace ℝ (Fin 3))→(EuclideanSpace ℝ (Fin 3))),-1≤z₀→ z₀+(Real.sqrt ρ)≤1→ Z⊆Set.Icc z₀ (z₀+(Real.sqrt ρ))→(∀z ∈ Set.Icc z₀ (z₀+(Real.sqrt ρ)),∀z' ∈ Set.Icc z₀ (z₀+(Real.sqrt ρ)),|f z-f z'|≤|z-z'|)→(∀z ∈ Set.Icc z₀ (z₀+(Real.sqrt ρ)),|f z|≤4)→(fun (E:Set (EuclideanSpace ℝ (Fin 3)))=>(∀p ∈ E,|p 0|≤1∧|p 1|≤1∧p 2 ∈ Z∧|p 0+f z₀*p 1-c₀|≤(Real.sqrt ρ))→ ENNReal.ofReal (ρ^(1+σ/2+η))≤MeasureTheory.volume E→(∀p ∈ E,‖V p‖=1∧ρ^(2*η)≤(V p 0)^2+(V p 1)^2)→(∀p ∈ E,∀q ∈ E,dist (V p) (V q)≤dist p q)→(∀z ∈ Z,AD ρ (1-σ) (ρ^(-η)) {u:ℝ|∃p ∈ E,p 2=z∧u=p 0+f z*p 1})→(∀p ∈ E,MeasureTheory.volume ((fun q:(EuclideanSpace ℝ (Fin 3))=>inner ℝ (V p) q) '' (E∩Metric.ball p (Real.sqrt ρ)))≤ENNReal.ofReal (ρ^((1+σ)/2-η)))→∃Zl:Set ℝ,Zl⊆Z∧ENNReal.ofReal (ρ^((1:ℝ)/2+ε))≤MeasureTheory.volume Zl∧∃a b:ℝ,∀z ∈ Zl,|f z-(a+b*z)|≤ρ) (⋃ k ∈ K,{p:(EuclideanSpace ℝ (Fin 3))|∀i:Fin 3,ρ*(k i:ℝ)≤p i∧p i<ρ*((k i:ℝ)+1)}) := by
  intro AD hAD h52 σ hσ hσ1 ε hε
  subst hAD
  obtain ⟨η, ρ₀, hη, hρ₀, H⟩ :=
    WangZahlLot.Obl.wz_slab_local_linearity.slab_local_linearity h52 hσ hσ1 hε
  refine ⟨η, ρ₀, hη, hρ₀, ?_⟩
  intro ρ hρ hρρ₀ z₀ c₀ Z f K V _ _ hZ hf hf4 hE hvol hV hVlip hglob hloc
  exact H ρ hρ hρρ₀ z₀ c₀ Z f K V
    { heights := hZ, f_lip := hf, f_bound := hf4, region := hE, mass := hvol,
      normals := hV, normal_lip := hVlip, global_AD := hglob, local_volume := hloc }
