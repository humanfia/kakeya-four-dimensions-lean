-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/TimedVectorListedCartesian.lean;
-- only the namespace was renamed into o230's.
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.TimedVectorBinnedCartesian
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.PaddedBinChoice
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.GridExtension

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart

open Set MeasureTheory MvPolynomial
open scoped ENNReal

/-- Three actual local lists fix a cell value and two polynomial bins.
The qualifying per-state polynomials then produce one actual field on
a measurable part of the original source law. -/
theorem exists_original_cartesian_fields_from_timed_local_lists {ι Ω X Y : Type*}
    [MeasurableSpace Ω] [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : Set Ω) (hA : MeasurableSet A)
    (cell : Ω → X × Y) (hcell : ∀ c, MeasurableSet {ω | cell ω=c})
    (D : ℕ) (v : X → ℝ) (w : Y → ℝ)
    (hinjv : Function.Injective v) (hinjw : Function.Injective w)
    (B Bt timeOrigin gap Bx By η ε ρ H K θ m M : ℝ)
    (hB : 1 ≤ B) (hBt : 1 ≤ Bt) (hgap : 0 < gap) (hBx : 0 ≤ Bx) (hBy : 0 ≤ By)
    (hη : 0 < η) (hε : 0 < ε) (hρ : 0 ≤ ρ) (hH : 0 ≤ H) (hK : 1 ≤ K)
    (hθ : 0 < θ) (hm : 0 < m) (hM : 0 < M)
    (hv : ∀ x, |v x| ≤ B) (hw : ∀ y, |w y| ≤ B)
    (hlower : ENNReal.ofReal m ≤ μ A)
    (hcap : ∀ c, μ (A ∩ {ω | cell ω=c}) ≤ ENNReal.ofReal M)
    (hlight : θ*((Fintype.card X : ℝ)*(Fintype.card Y : ℝ)) ≤ (m/K^3)/2)
    (hηmass : 2*M*((Fintype.card X : ℝ)*(Fintype.card Y : ℝ))*η ≤ m/K^3)
    (hthinX : ∀ z, gridMean (finiteUniformWeights X)
      (fun x => if |v x-z| < gap then 1 else 0) ≤ Bx)
    (hthinY : ∀ z, gridMean (finiteUniformWeights Y)
      (fun y => if |w y-z| < gap then 1 else 0) ≤ By)
    (hloss : ((D : ℝ)+2)^2*Bx+((D : ℝ)+2)^2*By ≤ η^((D+2)^2)/2)
    (G : ι → Ω → ℝ) (Pr Pc : ι → Ω → Polynomial ℝ)
    (htime : ∀ ω ∈ A, |timeOrigin+v (cell ω).1+w (cell ω).2| ≤ Bt)
    (hG : ∀ i, ∀ ω ∈ A, |G i ω| ≤ H)
    (hPr : ∀ i, ∀ ω ∈ A, (Pr i ω).natDegree ≤ D)
    (hPc : ∀ i, ∀ ω ∈ A, (Pc i ω).natDegree ≤ D)
    (hrowfit : ∀ i, ∀ ω ∈ A, |G i ω-(Pr i ω).eval (timeOrigin+v (cell ω).1+w (cell ω).2)| ≤ ρ)
    (hcolfit : ∀ i, ∀ ω ∈ A, |G i ω-(Pc i ω).eval (timeOrigin+v (cell ω).1+w (cell ω).2)| ≤ ρ)
    (hmG : ∀ j : ι → ℤ, MeasurableSet {ω | (fun i => ⌊G i ω/ε⌋)=j})
    (hmPr : ∀ c, MeasurableSet {ω | (fun i (k : Fin (D+1)) => ⌊(Pr i ω).coeff k/ε⌋)=c})
    (hmPc : ∀ c, MeasurableSet {ω | (fun i (k : Fin (D+1)) => ⌊(Pc i ω).coeff k/ε⌋)=c})
    (L₀ : X × Y → Finset (ι → ℤ))
    (Lr : Y → Finset (ι → Fin (D+1) → ℤ)) (Lc : X → Finset (ι → Fin (D+1) → ℤ))
    (hc₀ : ∀ c, ((L₀ c).card : ℝ) ≤ K)
    (hcr : ∀ y, ((Lr y).card : ℝ) ≤ K) (hcc : ∀ x, ((Lc x).card : ℝ) ≤ K)
    (hk₀ : ∀ ω ∈ A, (fun i => ⌊G i ω/ε⌋) ∈ L₀ (cell ω))
    (hkr : ∀ ω ∈ A, (fun i (k : Fin (D+1)) => ⌊(Pr i ω).coeff k/ε⌋) ∈ Lr (cell ω).2)
    (hkc : ∀ ω ∈ A, (fun i (k : Fin (D+1)) => ⌊(Pc i ω).coeff k/ε⌋) ∈ Lc (cell ω).1) :
    let W := ((D : ℝ)+1)*(2*B/gap)^D
    let Err := ε+ρ+2*((D : ℝ)+1)*ε*Bt^D
    ∃ (P : ι → MvPolynomial (Fin 2) ℝ) (S : Set Ω),
      (∀ i, (P i).totalDegree ≤ 2*D) ∧
      (∀ i, ∀ x y : ℝ, |x| ≤ B → |y| ≤ B → |eval ![x,y] (P i)| ≤ (ε+H)*W^2) ∧
      MeasurableSet S ∧ S ⊆ A ∧
      ENNReal.ofReal (θ*((Fintype.card X : ℝ)*(Fintype.card Y : ℝ))*(η^((D+2)^2)/2)) ≤ μ S ∧
      ∀ ω ∈ S, ∀ i, |G i ω-eval ![v (cell ω).1,w (cell ω).2] (P i)| ≤ ε+Err*(1+2*W+W^2) := by
  classical
  dsimp only
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hoY (y : Y) : MeasurableSet {ω | (cell ω).2=y} :=
    measurableSet_finite_observation_predicate cell hcell (fun c => c.2=y)
  have hoX (x : X) : MeasurableSet {ω | (cell ω).1=x} :=
    measurableSet_finite_observation_predicate cell hcell (fun c => c.1=x)
  have hK' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal K := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hK
  obtain ⟨c₀,cr,cc,S,hSm,hSA,hcost,hcoh⟩ := exists_three_original_bin_choices μ A hA
    cell (fun ω => (cell ω).2) (fun ω => (cell ω).1) hcell hoY hoX
    (fun ω i => ⌊G i ω/ε⌋) (fun ω => (fun i (k : Fin (D+1)) => ⌊(Pr i ω).coeff k/ε⌋))
    (fun ω => (fun i (k : Fin (D+1)) => ⌊(Pc i ω).coeff k/ε⌋)) hmG hmPr hmPc L₀ Lr Lc hk₀ hkr hkc
    (ENNReal.ofReal K) hK'
    (fun c => by simpa using ENNReal.ofReal_le_ofReal (hc₀ c))
    (fun y => by simpa using ENNReal.ofReal_le_ofReal (hcr y))
    (fun x => by simpa using ENNReal.ofReal_le_ofReal (hcc x))
  have hSfloor : ENNReal.ofReal (m/K^3) ≤ μ S :=
    original_floor_after_bin_choices μ A S K m hK0 hm.le hlower hcost
  let f : ι → ℝ → ℝ → ℝ := fun i =>
    cartesianGridExtension v w (fun x y => ε*(c₀ (x,y) i : ℝ))
  have hfield (i : ι) (ω : Ω) (hω : ω ∈ S) :
      |f i (v (cell ω).1) (w (cell ω).2)-G i ω| ≤ ε := by
    dsimp only [f]
    rw [cartesianGridExtension_at v w hinjv hinjw]
    have h := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hε (G i ω)
    have heq : ⌊G i ω/ε⌋=c₀ (cell ω) i := congrFun (hcoh ω hω).1 i
    rw [heq] at h
    simpa only [Prod.mk.eta,abs_sub_comm] using h
  have hrowbins (ω : Ω) (hω : ω ∈ S) (ω' : Ω) (hω' : ω' ∈ S)
      (hsame : (cell ω).2=(cell ω').2) :
      ∀ i (k : Fin (D+1)), ⌊(Pr i ω).coeff k/ε⌋=⌊(Pr i ω').coeff k/ε⌋ := by
    have heq : (fun i (k : Fin (D+1)) => ⌊(Pr i ω).coeff k/ε⌋)=
        (fun i (k : Fin (D+1)) => ⌊(Pr i ω').coeff k/ε⌋) :=
      (hcoh ω hω).2.1 |>.trans ((congrArg cr hsame).trans (hcoh ω' hω').2.1.symm)
    intro i k
    exact congrFun (congrFun heq i) k
  have hcolbins (ω : Ω) (hω : ω ∈ S) (ω' : Ω) (hω' : ω' ∈ S)
      (hsame : (cell ω).1=(cell ω').1) :
      ∀ i (k : Fin (D+1)), ⌊(Pc i ω).coeff k/ε⌋=⌊(Pc i ω').coeff k/ε⌋ := by
    have heq : (fun i (k : Fin (D+1)) => ⌊(Pc i ω).coeff k/ε⌋)=
        (fun i (k : Fin (D+1)) => ⌊(Pc i ω').coeff k/ε⌋) :=
      (hcoh ω hω).2.2 |>.trans ((congrArg cc hsame).trans (hcoh ω' hω').2.2.symm)
    intro i k
    exact congrFun (congrFun heq i) k
  have hScap (c : X × Y) : μ (S ∩ {ω | cell ω=c}) ≤ ENNReal.ofReal M :=
    (measure_mono (Set.inter_subset_inter_left _ hSA)).trans (hcap c)
  obtain ⟨P,T,hP,hNorm,hTm,hTS,hMass,hfit⟩ :=
    exists_original_cartesian_fields_from_timed_binned_witnesses μ S hSm cell hcell D v w
      B Bt timeOrigin gap Bx By η ε ε ρ H θ (m/K^3) M hB hBt hgap hBx hBy hη hε hε.le hρ hH
      hθ (by positivity) hM hv hw hSfloor hScap hlight hηmass hthinX hthinY hloss f G Pr Pc
      (fun ω hω => htime ω (hSA hω)) (fun i ω hω => hG i ω (hSA hω)) hfield
      (fun i ω hω => hPr i ω (hSA hω)) (fun i ω hω => hPc i ω (hSA hω))
      (fun i ω hω => hrowfit i ω (hSA hω)) (fun i ω hω => hcolfit i ω (hSA hω)) hrowbins hcolbins
  exact ⟨P,T,hP,hNorm,hTm,hTS.trans hSA,hMass,hfit⟩

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart
