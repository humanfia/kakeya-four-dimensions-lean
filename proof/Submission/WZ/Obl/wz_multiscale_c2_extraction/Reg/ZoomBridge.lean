-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.ZoomBridge.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.ZoomMain

/-!
# The normalization in the flat frozen shape

The frozen statements write the separated covers with seven flat conjuncts and the example
shape with an arbitrary slope clause `Q η δ n Y f`.  `ExF Q σ` is that shape with the named
conditions; `normalizeF` is the normalization in this shape, ready to be matched against a
frozen statement by `subst` and unfolding.
-/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section

/-- The separated all-scale covers with the seven conjuncts of the frozen statement. -/
def StrongFlat (η δ : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ r : ℝ, δ ≤ r → r ≤ 1 → ∃ ρ : ℝ, r ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ δ ^ (-η) * r ∧
    ∃ k : ℕ, 0 < k ∧ ∃ z w : Fin k → Space,
      (∀ j, ‖w j‖ = 1) ∧
      (∀ j j', j ≠ j' → volume (Tube ρ (z j) (w j) ∩ Tube ρ (z j') (w j')) ≤
        (1 / 2 : ENNReal) * volume (Tube ρ (z j) (w j))) ∧
      (∀ i, ∃! j, Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)) ∧
      (∀ j, ∃ i, Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)) ∧
      (∀ j j', (Set.ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)} : ℝ) ≤
        δ ^ (-η) * (Set.ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j') (w j')} : ℝ)) ∧
      (∀ j, ∀ W : Set Space, Convex ℝ W →
        ENNReal.ofReal ((Set.ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j) ∧
          Tube δ (x i) (v i) ⊆ W} : ℝ) * ρ ^ 2) ≤
        ENNReal.ofReal (δ ^ (-η) *
          (Set.ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j)} : ℝ)) * volume W) ∧
      (∀ i j j', Tube δ (x i) (v i) ⊆ Dilate ρ (z j) (w j) →
        Tube δ (x i) (v i) ⊆ Dilate ρ (z j') (w j') → j = j')

theorem strong_of_flat {η δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    (h : StrongFlat η δ n x v) : Strong η δ n x v := by
  intro r hδr hr1
  obtain ⟨ρ, hrρ, hρ1, hρr, k, hk, z, w, h1, h2, h3, h4, h5, h6, h7⟩ := h r hδr hr1
  exact ⟨ρ, hrρ, hρ1, hρr, k, hk, z, w, ⟨h1, h2, h3, h4, h5, h6⟩, h7⟩

theorem flat_of_strong {η δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    (h : Strong η δ n x v) : StrongFlat η δ n x v := by
  intro r hδr hr1
  obtain ⟨ρ, hrρ, hρ1, hρr, k, hk, z, w, ⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ := h r hδr hr1
  exact ⟨ρ, hrρ, hρ1, hρr, k, hk, z, w, h1, h2, h3, h4, h5, h6, h7⟩

/-- The frozen example shape with an arbitrary slope clause. -/
def ExF (Q : ℝ → ℝ → (n : ℕ) → (Fin n → Set Space) → (ℝ → ℝ) → Prop) (σ : ℝ) : Prop :=
  ∀ η d₀ : ℝ, 0 < η → 0 < d₀ → ∃ δ : ℝ, 0 < δ ∧ δ ≤ d₀ ∧ δ ≤ (1 / 100 : ℝ) ∧
    ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Dense η δ n x v Y ∧ StrongFlat η δ n x v ∧ (∀ i, IsCompact (Y i)) ∧
      volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)) ∧
      ∃ (f : ℝ → ℝ) (P : Space → Space), Q η δ n Y f ∧
        (∀ z : ℝ, z ∈ Icc (-1) 1 → Assouad δ (1 - σ) (δ ^ (-η)) (ProjectedSlice f (⋃ i, Y i) z)) ∧
        LipschitzWith 1 P ∧ (∀ p, p ∈ (⋃ i, Y i) → ‖P p‖ = 1) ∧
        (∀ i p, p ∈ Y i → |inner ℝ (v i) (P p)| ≤ δ) ∧
        (∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 → ∀ p : Space, p ∈ (⋃ i, Y i) →
          Assouad ρ (1 - σ) (δ ^ (-η))
            ((fun q : Space => inner ℝ (P p) q) '' ((⋃ i, Y i) ∩ ball p (Real.sqrt ρ))))

/-- The slope clause of the weak examples. -/
def QW (η δ : ℝ) (n : ℕ) (_Y : Fin n → Set Space) (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ∀ z : ℝ, |f z| ≤ δ ^ (-η) ∧ |deriv f z| ≤ δ ^ (-η) ∧
    |deriv (deriv f) z| ≤ δ ^ (-η)

/-- The slope clause of the frozen conclusion. -/
def QC (_η _δ : ℝ) (n : ℕ) (_Y : Fin n → Set Space) (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ∀ z : ℝ, z ∈ Icc (-1) 1 → |f z| ≤ 1 ∧ |deriv f z| ≤ 1 ∧
    |deriv (deriv f) z| ≤ 1

theorem weak_of_exF {σ : ℝ} (h : ExF QW σ) : WeakSmoothExamples σ := by
  intro η d₀ hη hd₀
  obtain ⟨δ, hδ, hδd, hδ1, n, x, v, Y, hD, hS, hC, hV, f, P, hf, hg, hP, hn, ho, hl⟩ :=
    h η d₀ hη hd₀
  exact ⟨δ, hδ, hδd, hδ1, n, x, v, Y, ⟨hD, strong_of_flat hS, hC, hV⟩, f, P, hf,
    ⟨hg, hP, hn, ho, hl⟩⟩

theorem exF_of_smooth {σ : ℝ} (h : SmoothExamples σ) : ExF QC σ := by
  intro η d₀ hη hd₀
  obtain ⟨δ, hδ, hδd, hδ1, n, x, v, Y, ⟨hD, hS, hC, hV⟩, f, P, hf, ⟨hg, hP, hn, ho, hl⟩⟩ :=
    h η d₀ hη hd₀
  exact ⟨δ, hδ, hδd, hδ1, n, x, v, Y, hD, flat_of_strong hS, hC, hV, f, P, hf, hg, hP, hn,
    ho, hl⟩

/-- The normalization in the flat frozen shape. -/
theorem normalizeF {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (h : ExF QW σ) : ExF QC σ :=
  exF_of_smooth (normalize hσ0 hσ1 (weak_of_exF h))

/-- The slope clause of the frozen premise. -/
def QL (_η _δ : ℝ) (n : ℕ) (_Y : Fin n → Set Space) (f : ℝ → ℝ) : Prop := LipschitzWith 1 f

/-- **Reduction.** The frozen statement of `o062` follows from the passage from Lipschitz
examples to examples with a `C²` slope whose value and first two derivatives are bounded by
`δ ^ (-η)`; the normalization of the slope is `normalize`. -/
theorem reduction_to_weak (hyp : ∀ σ : ℝ, 0 < σ → σ < 1 → ExF QL σ → ExF QW σ) :
    (fun (T:ℝ→(EuclideanSpace ℝ (Fin 3))→(EuclideanSpace ℝ (Fin 3))→Set (EuclideanSpace ℝ (Fin 3)))=>(fun (H:ℝ→ℝ→(n:ℕ)→(Fin n→(EuclideanSpace ℝ (Fin 3)))→(Fin n→(EuclideanSpace ℝ (Fin 3)))→(Fin n→Set (EuclideanSpace ℝ (Fin 3)))→Prop)=>(fun (D:ℝ→(EuclideanSpace ℝ (Fin 3))→(EuclideanSpace ℝ (Fin 3))→Set (EuclideanSpace ℝ (Fin 3)))=>(fun (S:ℝ→ℝ→(n:ℕ)→(Fin n→(EuclideanSpace ℝ (Fin 3)))→(Fin n→(EuclideanSpace ℝ (Fin 3)))→Prop)=>(fun (AD:ℝ→ℝ→ℝ→Set ℝ→Prop)=>(fun (PS:(ℝ→ℝ)→Set (EuclideanSpace ℝ (Fin 3))→ℝ→Set ℝ)=>(fun (X:ℝ→Prop)=>(fun (L:ℝ→Prop)=>(fun (C:ℝ→Prop)=>∀σ:ℝ,0<σ→σ<1→(∀t:ℝ,t<σ→X t)→(∀t:ℝ,σ<t→¬X t)→L σ→C σ) (fun (σ:ℝ)=>∀η d0:ℝ,0<η→0<d0→∃δ:ℝ,0<δ∧δ≤d0∧δ≤(1/100:ℝ)∧∃(n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3))) (Y:Fin n→Set (EuclideanSpace ℝ (Fin 3))),H η δ n x v Y∧S η δ n x v∧(∀i,IsCompact (Y i))∧MeasureTheory.volume (⋃ i,Y i)≤ENNReal.ofReal (δ^(σ-η))∧∃(f:ℝ→ℝ) (P:(EuclideanSpace ℝ (Fin 3))→(EuclideanSpace ℝ (Fin 3))),(ContDiff ℝ 2 f∧∀z:ℝ,z ∈ Set.Icc (-1) 1→|f z|≤1∧|deriv f z|≤1∧|deriv (deriv f) z|≤1)∧(∀z:ℝ,z ∈ Set.Icc (-1) 1→AD δ (1-σ) (δ^(-η)) (PS f (⋃ i,Y i) z))∧LipschitzWith 1 P∧(∀p,p ∈ (⋃ i,Y i)→‖P p‖=1)∧(∀i p,p ∈ Y i→|inner ℝ (v i) (P p)|≤δ)∧(∀ρ:ℝ,δ≤ρ→ρ≤1→∀p:(EuclideanSpace ℝ (Fin 3)),p ∈ (⋃ i,Y i)→AD ρ (1-σ) (δ^(-η)) ((fun q:(EuclideanSpace ℝ (Fin 3))=>inner ℝ (P p) q) '' ((⋃ i,Y i)∩Metric.ball p (Real.sqrt ρ)))))) (fun (σ:ℝ)=>∀η d0:ℝ,0<η→0<d0→∃δ:ℝ,0<δ∧δ≤d0∧δ≤(1/100:ℝ)∧∃(n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3))) (Y:Fin n→Set (EuclideanSpace ℝ (Fin 3))),H η δ n x v Y∧S η δ n x v∧(∀i,IsCompact (Y i))∧MeasureTheory.volume (⋃ i,Y i)≤ENNReal.ofReal (δ^(σ-η))∧∃(f:ℝ→ℝ) (P:(EuclideanSpace ℝ (Fin 3))→(EuclideanSpace ℝ (Fin 3))),(LipschitzWith 1 f)∧(∀z:ℝ,z ∈ Set.Icc (-1) 1→AD δ (1-σ) (δ^(-η)) (PS f (⋃ i,Y i) z))∧LipschitzWith 1 P∧(∀p,p ∈ (⋃ i,Y i)→‖P p‖=1)∧(∀i p,p ∈ Y i→|inner ℝ (v i) (P p)|≤δ)∧(∀ρ:ℝ,δ≤ρ→ρ≤1→∀p:(EuclideanSpace ℝ (Fin 3)),p ∈ (⋃ i,Y i)→AD ρ (1-σ) (δ^(-η)) ((fun q:(EuclideanSpace ℝ (Fin 3))=>inner ℝ (P p) q) '' ((⋃ i,Y i)∩Metric.ball p (Real.sqrt ρ)))))) (fun (s:ℝ)=>∀η d0:ℝ,0<η→0<d0→∃δ:ℝ,0<δ∧δ≤d0∧δ≤(1/100:ℝ)∧∃(n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3))) (Y:Fin n→Set (EuclideanSpace ℝ (Fin 3))),H η δ n x v Y∧S η δ n x v∧MeasureTheory.volume (⋃ i,Y i)≤ENNReal.ofReal (δ^s))) ((fun (f:ℝ→ℝ) (E:Set (EuclideanSpace ℝ (Fin 3))) (z:ℝ)=>{u:ℝ|(u,z) ∈ (fun p:(EuclideanSpace ℝ (Fin 3))=>(p 0+f (p 2)*p 1,p 2)) '' E}))) (fun (d α C:ℝ) (B:Set ℝ)=>∀r R a:ℝ,d≤r→ r≤R→∃(m:ℕ) (c:Fin m→ℝ),B∩Set.Icc a (a+R)⊆(⋃ j,Metric.closedBall (c j) r)∧(m:ℝ)≤C*(R/r)^α)) (fun (η δ:ℝ) (n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3)))=>∀r:ℝ,δ≤r→ r≤1→∃ρ:ℝ,r≤ρ∧ρ≤1∧ρ≤δ^(-η)*r∧∃k:ℕ,0<k∧∃z w:Fin k→(EuclideanSpace ℝ (Fin 3)),(∀j,‖w j‖=1)∧(∀j j',j≠j'→MeasureTheory.volume (T ρ (z j) (w j)∩T ρ (z j') (w j'))≤(1/2:ENNReal)*MeasureTheory.volume (T ρ (z j) (w j)))∧(∀i,∃! j,T δ (x i) (v i)⊆T ρ (z j) (w j))∧(∀j,∃i,T δ (x i) (v i)⊆T ρ (z j) (w j))∧(∀j j',(Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j) (w j)}:ℝ)≤δ^(-η)*(Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j') (w j')}:ℝ))∧(∀j,∀W:Set (EuclideanSpace ℝ (Fin 3)),Convex ℝ W→ENNReal.ofReal ((Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j) (w j)∧T δ (x i) (v i)⊆W}:ℝ)*ρ^2)≤ENNReal.ofReal (δ^(-η)*(Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j) (w j)}:ℝ))*MeasureTheory.volume W)∧(∀i j j',T δ (x i) (v i)⊆D ρ (z j) (w j)→T δ (x i) (v i)⊆D ρ (z j') (w j')→j=j'))) (fun (ρ:ℝ) (z w:(EuclideanSpace ℝ (Fin 3)))=>Metric.thickening (10*ρ) (segment ℝ (z-(9/2:ℝ) • w) (z+(11/2:ℝ) • w)))) (fun (η δ:ℝ) (n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3))) (Y:Fin n→Set (EuclideanSpace ℝ (Fin 3)))=>0<n∧(∀i,‖v i‖=1)∧(∀i,T δ (x i) (v i)⊆Metric.ball 0 1)∧(∀i j,i≠j→MeasureTheory.volume (T δ (x i) (v i)∩T δ (x j) (v j))≤(1/2:ENNReal)*MeasureTheory.volume (T δ (x i) (v i)))∧(∀i,MeasurableSet (Y i))∧(∀i,Y i⊆T δ (x i) (v i))∧ENNReal.ofReal (δ^η*(n:ℝ)*δ^2)≤Finset.sum Finset.univ (fun i=>MeasureTheory.volume (Y i)))) (fun (δ:ℝ) (x v:(EuclideanSpace ℝ (Fin 3)))=>Metric.thickening δ (segment ℝ x (x+v))) := by
  intro σ hσ hσ1 _ _ hL
  exact normalizeF hσ.le hσ1.le (hyp σ hσ hσ1 hL)

end

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
